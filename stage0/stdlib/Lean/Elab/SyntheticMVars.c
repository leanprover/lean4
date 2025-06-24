// Lean compiler output
// Module: Lean.Elab.SyntheticMVars
// Imports: Lean.Meta.Tactic.Util Lean.Util.NumObjs Lean.Util.ForEachExpr Lean.Util.OccursCheck Lean.Elab.Tactic.Basic Lean.Meta.AbstractNestedProofs
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
LEAN_EXPORT uint8_t l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__7;
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__13____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__1;
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runPendingTacticsAt_spec__0___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPostponed___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__5;
static lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__1;
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_instInhabitedPostponeBehavior;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sharecommon_quick(lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__4;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__2;
static lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2;
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__2;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_toCtorIdx___boxed(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instReprPostponeBehavior;
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutPostponing___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runTactic_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4157____boxed(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__0;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___closed__0;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__4;
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__2___closed__0;
lean_object* l_Lean_RBNode_setBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__1;
static lean_object* l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__4;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__3;
static lean_object* l_Lean_Elab_Term_reprPostponeBehavior___closed__2____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__12____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoTreeContext___at___Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withSavedContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__6____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalContext;
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7___closed__0;
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_RBNode_find___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_PrettyPrinter_Delaborator_delabConst_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___closed__0;
static lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__6;
static lean_object* l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getSyntheticMVarDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runTactic_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_logErrorAt___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__1;
extern lean_object* l_Lean_Elab_instInhabitedInfoTree;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__3;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__7;
lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__4;
static lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_eqWithInfoAndTraceReuse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___redArg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__8;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__17____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelParams_visitExpr_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__2;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__1;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runPendingTacticsAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__1;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reprPostponeBehavior___closed__4____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
lean_object* l_Lean_Meta_mkLevelStuckErrorMessage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_runTactic___lam__13___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__2;
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_reportStuckSyntheticMVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runTactic_spec__5___redArg(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_goalsToMessageData(lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__5;
extern lean_object* l_Lean_Meta_instInhabitedPostponedEntry;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelParams_visitExpr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reprPostponeBehavior___closed__5____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273____boxed(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__14____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
lean_object* l_Lean_Elab_Term_traceAtCmdPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__0;
static lean_object* l_Lean_Elab_Term_initFn___closed__7____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4157_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedDefaultInstances;
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
extern lean_object* l_Lean_Meta_defaultInstanceExtension;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_ofBool___boxed(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_normLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_processPostponedUniverseConstraints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_instBEqPostponeBehavior___closed__0;
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__5;
static lean_object* l_Lean_Elab_Term_initFn___closed__8____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__3;
lean_object* l_Lean_RBNode_balRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__5(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runPendingTacticsAt_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__6;
static lean_object* l_Lean_Elab_Term_initFn___closed__10____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__4;
static lean_object* l_Lean_Elab_Term_initFn___closed__9____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reprPostponeBehavior___closed__6____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeSomeUsingDefault_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__5;
static lean_object* l_Lean_Elab_Term_reprPostponeBehavior___closed__1____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__0;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__13(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__0;
lean_object* l_Lean_Elab_getResetInfoTrees___at_____private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___Lean_Elab_withSaveParentDeclInfoContext___at___Lean_Elab_Term_withDeclName_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__0;
static lean_object* l_Lean_Elab_Term_initFn___closed__15____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__2;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10;
static lean_object* l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__3;
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runPendingTacticsAt_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Term_exprToSyntax_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_coerce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runPendingTacticsAt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___Lean_Elab_Tactic_evalTactic_eval_spec__7___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0___closed__1;
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runTactic_spec__5(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_instReprPostponeBehavior___closed__0;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7474_(lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__5;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__3___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_runTactic___lam__13___closed__0;
static lean_object* l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__2;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_panic___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar_spec__0___closed__0;
static lean_object* l_Lean_Elab_Term_initFn___closed__16____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at___Lean_Elab_withLogging___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__11____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_postponeExceptionId;
lean_object* l_Lean_Elab_Term_withoutAutoBoundImplicit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasMissing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__2;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reprPostponeBehavior___closed__3____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_Term_extraMsgToMsg(lean_object*);
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___closed__1;
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__9;
LEAN_EXPORT uint8_t l_Lean_Elab_Term_PostponeBehavior_ofBool(uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__4(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instBEqPostponeBehavior;
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reprPostponeBehavior___closed__7____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_beq___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reprPostponeBehavior___closed__0____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_instantiate_expr_mvars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Elab_Term_reportStuckSyntheticMVar_spec__0___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstancesStep_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__5;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__4;
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__6;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_getDelayedMVarRoot___at___Lean_Elab_Term_isLetRecAuxMVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__0;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__0;
lean_object* l_Lean_Level_hash___boxed(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstancesStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_toCtorIdx(uint8_t);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn___closed__5____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
lean_object* l_Lean_Meta_zetaReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0___redArg___boxed(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__12(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__3;
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__0;
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 1);
x_15 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 2);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 5);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 3);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 4);
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 5);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 6);
x_24 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 7);
x_25 = lean_ctor_get(x_4, 6);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 x_29 = x_4;
} else {
 lean_dec_ref(x_4);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
x_31 = lean_box(1);
if (x_14 == 0)
{
x_32 = x_14;
goto block_37;
}
else
{
x_32 = x_3;
goto block_37;
}
block_37:
{
lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 7, 11);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_12);
lean_ctor_set(x_33, 2, x_16);
lean_ctor_set(x_33, 3, x_17);
lean_ctor_set(x_33, 4, x_18);
lean_ctor_set(x_33, 5, x_19);
lean_ctor_set(x_33, 6, x_25);
lean_ctor_set_uint8(x_33, sizeof(void*)*7, x_13);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 1, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 2, x_15);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 3, x_20);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 4, x_21);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 5, x_22);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 6, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 7, x_24);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 8, x_26);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 9, x_27);
lean_ctor_set_uint8(x_33, sizeof(void*)*7 + 10, x_28);
x_34 = lean_unbox(x_30);
x_35 = lean_unbox(x_31);
x_36 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_34, x_35, x_33, x_5, x_6, x_7, x_8, x_9, x_10);
return x_36;
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
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_8, x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_14, x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_8, x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_14, x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_6, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_name_eq(x_1, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
x_12 = l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_7, x_10);
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
x_18 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__1___redArg(x_2, x_17, x_7, x_16);
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
x_26 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__0;
lean_ctor_set(x_19, 0, x_26);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__0;
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
x_33 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__0;
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
x_36 = lean_ctor_get(x_21, 0);
lean_inc(x_36);
lean_dec(x_21);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_dec(x_18);
x_38 = lean_ctor_get(x_19, 1);
lean_inc(x_38);
lean_dec(x_19);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_2 = x_39;
x_3 = x_38;
x_10 = x_37;
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
x_44 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0(x_1, x_43, x_42, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
x_45 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_21; 
x_21 = l_Lean_Expr_hasExprMVar(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_22 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__0;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; uint8_t x_41; 
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
x_27 = lean_array_get_size(x_26);
x_28 = l_Lean_Expr_hash(x_2);
x_29 = 32;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = 16;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_37 = 1;
x_38 = lean_usize_sub(x_36, x_37);
x_39 = lean_usize_land(x_35, x_38);
x_40 = lean_array_uget(x_26, x_39);
x_41 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelParams_visitExpr_spec__0___redArg(x_2, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
if (x_41 == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_3);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_81 = lean_ctor_get(x_3, 1);
lean_dec(x_81);
x_82 = lean_ctor_get(x_3, 0);
lean_dec(x_82);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_add(x_25, x_83);
lean_dec(x_25);
lean_inc(x_2);
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_2);
lean_ctor_set(x_85, 1, x_42);
lean_ctor_set(x_85, 2, x_40);
x_86 = lean_array_uset(x_26, x_39, x_85);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_mul(x_84, x_87);
x_89 = lean_unsigned_to_nat(3u);
x_90 = lean_nat_div(x_88, x_89);
lean_dec(x_88);
x_91 = lean_array_get_size(x_86);
x_92 = lean_nat_dec_le(x_90, x_91);
lean_dec(x_91);
lean_dec(x_90);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelParams_visitExpr_spec__1___redArg(x_86);
lean_ctor_set(x_3, 1, x_93);
lean_ctor_set(x_3, 0, x_84);
x_43 = x_3;
goto block_79;
}
else
{
lean_ctor_set(x_3, 1, x_86);
lean_ctor_set(x_3, 0, x_84);
x_43 = x_3;
goto block_79;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_3);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_25, x_94);
lean_dec(x_25);
lean_inc(x_2);
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_2);
lean_ctor_set(x_96, 1, x_42);
lean_ctor_set(x_96, 2, x_40);
x_97 = lean_array_uset(x_26, x_39, x_96);
x_98 = lean_unsigned_to_nat(4u);
x_99 = lean_nat_mul(x_95, x_98);
x_100 = lean_unsigned_to_nat(3u);
x_101 = lean_nat_div(x_99, x_100);
lean_dec(x_99);
x_102 = lean_array_get_size(x_97);
x_103 = lean_nat_dec_le(x_101, x_102);
lean_dec(x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelParams_visitExpr_spec__1___redArg(x_97);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_95);
lean_ctor_set(x_105, 1, x_104);
x_43 = x_105;
goto block_79;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_95);
lean_ctor_set(x_106, 1, x_97);
x_43 = x_106;
goto block_79;
}
}
}
else
{
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_25);
x_43 = x_3;
goto block_79;
}
block_79:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
lean_dec(x_2);
x_45 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0(x_1, x_44, x_43, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_45;
}
case 5:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
lean_dec(x_2);
x_48 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0(x_1, x_46, x_43, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_47);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_2 = x_47;
x_3 = x_52;
x_10 = x_51;
goto _start;
}
}
case 6:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 2);
lean_inc(x_55);
lean_dec(x_2);
x_11 = x_54;
x_12 = x_55;
x_13 = x_43;
goto block_20;
}
case 7:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 2);
lean_inc(x_57);
lean_dec(x_2);
x_11 = x_56;
x_12 = x_57;
x_13 = x_43;
goto block_20;
}
case 8:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_2, 3);
lean_inc(x_60);
lean_dec(x_2);
x_61 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0(x_1, x_58, x_43, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0(x_1, x_59, x_65, x_4, x_5, x_6, x_7, x_8, x_9, x_64);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_60);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_2 = x_60;
x_3 = x_70;
x_10 = x_69;
goto _start;
}
}
}
case 10:
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_2, 1);
lean_inc(x_72);
lean_dec(x_2);
x_2 = x_72;
x_3 = x_43;
goto _start;
}
case 11:
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_2, 2);
lean_inc(x_74);
lean_dec(x_2);
x_2 = x_74;
x_3 = x_43;
goto _start;
}
default: 
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_2);
x_76 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__0;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_43);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_10);
return x_78;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
x_107 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__0;
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_3);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_10);
return x_109;
}
}
block_20:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0(x_1, x_11, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_2 = x_12;
x_3 = x_18;
x_10 = x_17;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasExprMVar(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_box(1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__4;
x_14 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0(x_1, x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_16);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = lean_box(x_10);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(x_10);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_29; 
x_6 = lean_st_ref_take(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 7);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 8);
lean_inc(x_17);
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
 x_18 = x_7;
} else {
 lean_dec_ref(x_7);
 x_18 = lean_box(0);
}
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_16, 2);
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_30, 2);
lean_inc(x_32);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_32);
if (x_34 == 0)
{
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_3);
lean_ctor_set(x_16, 2, x_2);
x_19 = x_16;
goto block_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = l_Lean_Elab_instInhabitedInfoTree;
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_sub(x_32, x_36);
lean_dec(x_32);
x_38 = l_Lean_PersistentArray_get_x21___redArg(x_35, x_30, x_37);
lean_dec(x_37);
x_39 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_31, x_3, x_38);
lean_ctor_set(x_16, 2, x_2);
lean_ctor_set(x_16, 0, x_39);
x_19 = x_16;
goto block_28;
}
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_ctor_get(x_16, 2);
x_41 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
x_42 = lean_ctor_get(x_16, 0);
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_16);
x_44 = lean_ctor_get(x_40, 2);
lean_inc(x_44);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_lt(x_45, x_44);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_3);
x_47 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_2);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_41);
x_19 = x_47;
goto block_28;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = l_Lean_Elab_instInhabitedInfoTree;
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_sub(x_44, x_49);
lean_dec(x_44);
x_51 = l_Lean_PersistentArray_get_x21___redArg(x_48, x_40, x_50);
lean_dec(x_50);
x_52 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_42, x_3, x_51);
x_53 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_43);
lean_ctor_set(x_53, 2, x_2);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_41);
x_19 = x_53;
goto block_28;
}
}
block_28:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 9, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_11);
lean_ctor_set(x_20, 3, x_12);
lean_ctor_set(x_20, 4, x_13);
lean_ctor_set(x_20, 5, x_14);
lean_ctor_set(x_20, 6, x_15);
lean_ctor_set(x_20, 7, x_19);
lean_ctor_set(x_20, 8, x_17);
x_21 = lean_st_ref_set(x_1, x_20, x_8);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc(x_1);
x_42 = l_Lean_Elab_Term_getMVarDecl___redArg(x_1, x_7, x_10);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 2);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_45, x_7, x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_47);
if (x_3 == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_box(1);
x_148 = lean_unbox(x_147);
x_50 = x_148;
goto block_146;
}
else
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_box(0);
x_150 = lean_unbox(x_149);
x_50 = x_150;
goto block_146;
}
block_27:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_apply_2(x_11, x_15, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(x_12);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
block_41:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = lean_apply_2(x_28, x_31, x_30);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_29);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_29);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
block_146:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_st_ref_get(x_9, x_48);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 7);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*3);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_49);
lean_inc(x_2);
x_56 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(x_2, x_49, x_50, x_4, x_5, x_6, x_7, x_8, x_9, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_8, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_8, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_8, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_8, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_8, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_8, 5);
lean_inc(x_64);
x_65 = lean_ctor_get(x_8, 6);
lean_inc(x_65);
x_66 = lean_ctor_get(x_8, 7);
lean_inc(x_66);
x_67 = lean_ctor_get(x_8, 8);
lean_inc(x_67);
x_68 = lean_ctor_get(x_8, 9);
lean_inc(x_68);
x_69 = lean_ctor_get(x_8, 10);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_71 = lean_ctor_get(x_8, 11);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_73 = lean_ctor_get(x_8, 12);
lean_inc(x_73);
x_74 = lean_box(0);
x_75 = lean_box(0);
x_76 = l_Lean_replaceRef(x_2, x_64);
lean_dec(x_64);
lean_dec(x_2);
x_77 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_77, 0, x_59);
lean_ctor_set(x_77, 1, x_60);
lean_ctor_set(x_77, 2, x_61);
lean_ctor_set(x_77, 3, x_62);
lean_ctor_set(x_77, 4, x_63);
lean_ctor_set(x_77, 5, x_76);
lean_ctor_set(x_77, 6, x_65);
lean_ctor_set(x_77, 7, x_66);
lean_ctor_set(x_77, 8, x_67);
lean_ctor_set(x_77, 9, x_68);
lean_ctor_set(x_77, 10, x_69);
lean_ctor_set(x_77, 11, x_71);
lean_ctor_set(x_77, 12, x_73);
lean_ctor_set_uint8(x_77, sizeof(void*)*13, x_70);
lean_ctor_set_uint8(x_77, sizeof(void*)*13 + 1, x_72);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_78 = l_Lean_Elab_Term_ensureHasType(x_49, x_57, x_74, x_75, x_4, x_5, x_6, x_7, x_77, x_9, x_58);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_79);
x_81 = l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0(x_1, x_79, x_4, x_5, x_6, x_7, x_8, x_9, x_80);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
if (x_83 == 0)
{
uint8_t x_84; 
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_7);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_81);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_81, 0);
lean_dec(x_85);
x_86 = lean_box(x_54);
lean_ctor_set(x_81, 0, x_86);
return x_81;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_88 = lean_box(x_54);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_dec(x_81);
x_91 = l_Lean_MVarId_assign___at___Lean_Elab_Term_exprToSyntax_spec__0___redArg(x_1, x_79, x_7, x_90);
lean_dec(x_7);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
lean_ctor_set(x_91, 0, x_82);
return x_91;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_82);
lean_ctor_set(x_95, 1, x_94);
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
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_78);
if (x_96 == 0)
{
return x_78;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_78, 0);
x_98 = lean_ctor_get(x_78, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_78);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_49);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_56);
if (x_100 == 0)
{
return x_56;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_56, 0);
x_102 = lean_ctor_get(x_56, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_56);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_51, 1);
lean_inc(x_104);
lean_dec(x_51);
x_105 = l_Lean_Elab_getResetInfoTrees___at_____private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___Lean_Elab_withSaveParentDeclInfoContext___at___Lean_Elab_Term_withDeclName_spec__1_spec__1_spec__1___redArg(x_9, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_1);
lean_inc(x_9);
x_108 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__0___boxed), 5, 3);
lean_closure_set(x_108, 0, x_9);
lean_closure_set(x_108, 1, x_106);
lean_closure_set(x_108, 2, x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_49);
lean_inc(x_2);
x_109 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(x_2, x_49, x_50, x_4, x_5, x_6, x_7, x_8, x_9, x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_8, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_8, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_8, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_8, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_8, 4);
lean_inc(x_116);
x_117 = lean_ctor_get(x_8, 5);
lean_inc(x_117);
x_118 = lean_ctor_get(x_8, 6);
lean_inc(x_118);
x_119 = lean_ctor_get(x_8, 7);
lean_inc(x_119);
x_120 = lean_ctor_get(x_8, 8);
lean_inc(x_120);
x_121 = lean_ctor_get(x_8, 9);
lean_inc(x_121);
x_122 = lean_ctor_get(x_8, 10);
lean_inc(x_122);
x_123 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_124 = lean_ctor_get(x_8, 11);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_126 = lean_ctor_get(x_8, 12);
lean_inc(x_126);
x_127 = lean_box(0);
x_128 = lean_box(0);
x_129 = l_Lean_replaceRef(x_2, x_117);
lean_dec(x_117);
lean_dec(x_2);
x_130 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_130, 0, x_112);
lean_ctor_set(x_130, 1, x_113);
lean_ctor_set(x_130, 2, x_114);
lean_ctor_set(x_130, 3, x_115);
lean_ctor_set(x_130, 4, x_116);
lean_ctor_set(x_130, 5, x_129);
lean_ctor_set(x_130, 6, x_118);
lean_ctor_set(x_130, 7, x_119);
lean_ctor_set(x_130, 8, x_120);
lean_ctor_set(x_130, 9, x_121);
lean_ctor_set(x_130, 10, x_122);
lean_ctor_set(x_130, 11, x_124);
lean_ctor_set(x_130, 12, x_126);
lean_ctor_set_uint8(x_130, sizeof(void*)*13, x_123);
lean_ctor_set_uint8(x_130, sizeof(void*)*13 + 1, x_125);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_131 = l_Lean_Elab_Term_ensureHasType(x_49, x_110, x_127, x_128, x_4, x_5, x_6, x_7, x_130, x_9, x_111);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
lean_inc(x_132);
x_134 = l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0(x_1, x_132, x_4, x_5, x_6, x_7, x_8, x_9, x_133);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_unbox(x_135);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
lean_dec(x_132);
lean_dec(x_7);
lean_dec(x_1);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_unbox(x_135);
lean_dec(x_135);
x_11 = x_108;
x_12 = x_138;
x_13 = x_137;
goto block_27;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_135);
x_139 = lean_ctor_get(x_134, 1);
lean_inc(x_139);
lean_dec(x_134);
x_140 = l_Lean_MVarId_assign___at___Lean_Elab_Term_exprToSyntax_spec__0___redArg(x_1, x_132, x_7, x_139);
lean_dec(x_7);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_11 = x_108;
x_12 = x_54;
x_13 = x_141;
goto block_27;
}
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_142 = lean_ctor_get(x_131, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_131, 1);
lean_inc(x_143);
lean_dec(x_131);
x_28 = x_108;
x_29 = x_142;
x_30 = x_143;
goto block_41;
}
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_49);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_144 = lean_ctor_get(x_109, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_109, 1);
lean_inc(x_145);
lean_dec(x_109);
x_28 = x_108;
x_29 = x_144;
x_30 = x_145;
goto block_41;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_postponeExceptionId;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Elab_Term_saveState___redArg(x_5, x_7, x_9, x_10);
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
x_14 = l_Lean_Elab_Term_withSavedContext___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_47; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_47 = l_Lean_Exception_isInterrupt(x_15);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Exception_isRuntime(x_15);
x_17 = x_48;
goto block_46;
}
else
{
x_17 = x_47;
goto block_46;
}
block_46:
{
if (x_17 == 0)
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_18; 
lean_dec(x_14);
x_18 = lean_box(1);
if (x_3 == 0)
{
lean_object* x_19; 
lean_dec(x_12);
x_19 = l_Lean_Elab_logException___at___Lean_Elab_withLogging___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore_spec__2_spec__2(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
uint8_t x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_15);
x_28 = lean_unbox(x_18);
x_29 = l_Lean_Elab_Term_SavedState_restore(x_12, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(x_17);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(x_17);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_15, 0);
lean_inc(x_36);
lean_dec(x_15);
x_37 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__2___closed__0;
x_38 = lean_nat_dec_eq(x_36, x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
else
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_14);
x_39 = l_Lean_Elab_Term_SavedState_restore(x_12, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(x_17);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(x_17);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_9, 5);
x_14 = lean_box(x_4);
lean_inc(x_2);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__1___boxed), 10, 3);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_14);
x_16 = lean_box(x_4);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__2___boxed), 10, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_16);
x_18 = l_Lean_replaceRef(x_2, x_13);
lean_dec(x_13);
lean_dec(x_2);
lean_ctor_set(x_9, 5, x_18);
x_19 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
x_22 = lean_ctor_get(x_9, 2);
x_23 = lean_ctor_get(x_9, 3);
x_24 = lean_ctor_get(x_9, 4);
x_25 = lean_ctor_get(x_9, 5);
x_26 = lean_ctor_get(x_9, 6);
x_27 = lean_ctor_get(x_9, 7);
x_28 = lean_ctor_get(x_9, 8);
x_29 = lean_ctor_get(x_9, 9);
x_30 = lean_ctor_get(x_9, 10);
x_31 = lean_ctor_get_uint8(x_9, sizeof(void*)*13);
x_32 = lean_ctor_get(x_9, 11);
x_33 = lean_ctor_get_uint8(x_9, sizeof(void*)*13 + 1);
x_34 = lean_ctor_get(x_9, 12);
lean_inc(x_34);
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
lean_dec(x_9);
x_35 = lean_box(x_4);
lean_inc(x_2);
lean_inc(x_3);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__1___boxed), 10, 3);
lean_closure_set(x_36, 0, x_3);
lean_closure_set(x_36, 1, x_2);
lean_closure_set(x_36, 2, x_35);
x_37 = lean_box(x_4);
x_38 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__2___boxed), 10, 3);
lean_closure_set(x_38, 0, x_1);
lean_closure_set(x_38, 1, x_36);
lean_closure_set(x_38, 2, x_37);
x_39 = l_Lean_replaceRef(x_2, x_25);
lean_dec(x_25);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_40, 0, x_20);
lean_ctor_set(x_40, 1, x_21);
lean_ctor_set(x_40, 2, x_22);
lean_ctor_set(x_40, 3, x_23);
lean_ctor_set(x_40, 4, x_24);
lean_ctor_set(x_40, 5, x_39);
lean_ctor_set(x_40, 6, x_26);
lean_ctor_set(x_40, 7, x_27);
lean_ctor_set(x_40, 8, x_28);
lean_ctor_set(x_40, 9, x_29);
lean_ctor_set(x_40, 10, x_30);
lean_ctor_set(x_40, 11, x_32);
lean_ctor_set(x_40, 12, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*13, x_31);
lean_ctor_set_uint8(x_40, sizeof(void*)*13 + 1, x_33);
x_41 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_3, x_38, x_5, x_6, x_7, x_8, x_40, x_10, x_11);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_getExprMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_getDelayedMVarAssignment_x3f___at___Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__2(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
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
static lean_object* _init_l_panic___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar_spec__0___closed__0;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.SyntheticMVars", 24, 24);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Elab.SyntheticMVars.0.Lean.Elab.Term.synthesizePendingInstMVar", 76, 76);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__2;
x_2 = lean_unsigned_to_nat(26u);
x_3 = lean_unsigned_to_nat(70u);
x_4 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__1;
x_5 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_11 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_29; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_29 = l_Lean_Exception_isInterrupt(x_12);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Exception_isRuntime(x_12);
x_14 = x_30;
goto block_28;
}
else
{
x_14 = x_29;
goto block_28;
}
block_28:
{
if (x_14 == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Elab_logException___at___Lean_Elab_withLogging___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore_spec__2_spec__2(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
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
lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
x_26 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__3;
x_27 = l_panic___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar_spec__0(x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_27;
}
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
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
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___boxed), 10, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_2);
x_12 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_22; lean_object* x_28; 
x_9 = l_Lean_Elab_Term_saveState___redArg(x_3, x_5, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_28 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_unbox(x_29);
x_33 = l_Lean_Elab_Term_SavedState_restore(x_10, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_29);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_dec(x_29);
x_22 = x_28;
goto block_27;
}
}
else
{
x_22 = x_28;
goto block_27;
}
block_21:
{
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_SavedState_restore(x_10, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
block_27:
{
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = l_Lean_Exception_isInterrupt(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Exception_isRuntime(x_23);
x_12 = x_23;
x_13 = x_22;
x_14 = x_24;
x_15 = x_26;
goto block_21;
}
else
{
x_12 = x_23;
x_13 = x_22;
x_14 = x_24;
x_15 = x_25;
goto block_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_22; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_22 = l_Lean_Exception_isInterrupt(x_12);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Exception_isRuntime(x_12);
lean_dec(x_12);
x_14 = x_23;
goto block_21;
}
else
{
lean_dec(x_12);
x_14 = x_22;
goto block_21;
}
block_21:
{
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = lean_box(x_14);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
x_19 = lean_box(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
else
{
lean_dec(x_13);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_box(0);
x_10 = lean_box(0);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___lam__0___boxed), 10, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5), 10, 3);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_11);
x_13 = l_Lean_commitWhen___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27_spec__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstancesStep_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_13 = x_1;
} else {
 lean_dec_ref(x_1);
 x_13 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_11);
x_18 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_14 = x_21;
goto block_17;
}
else
{
lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_11);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_1 = x_12;
x_9 = x_22;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_1 = x_12;
x_9 = x_26;
goto _start;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_14 = x_28;
goto block_17;
}
}
else
{
uint8_t x_29; 
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
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
block_17:
{
lean_object* x_15; 
if (lean_is_scalar(x_13)) {
 x_15 = lean_alloc_ctor(1, 2, 0);
} else {
 x_15 = x_13;
}
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_2);
x_1 = x_12;
x_2 = x_15;
x_9 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstancesStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstancesStep_spec__0(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_List_reverse___redArg(x_12);
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
x_16 = l_List_reverse___redArg(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
return x_10;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = l_List_lengthTR___redArg(x_10);
x_13 = l_List_lengthTR___redArg(x_1);
lean_dec(x_1);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
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
lean_dec(x_9);
x_1 = x_10;
x_8 = x_11;
goto _start;
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
lean_dec(x_1);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_defaultInstanceExtension;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg___closed__0;
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_10 = l_Lean_Meta_instInhabitedDefaultInstances;
x_11 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_10, x_7, x_6, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg___closed__0;
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*3);
lean_dec(x_17);
x_19 = l_Lean_Meta_instInhabitedDefaultInstances;
x_20 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_19, x_16, x_15, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 3);
lean_inc(x_17);
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_RBNode_forIn_visit___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__1(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_25 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio(x_1, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
lean_free_object(x_19);
lean_free_object(x_18);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
lean_inc(x_2);
{
lean_object* _tmp_3 = x_17;
lean_object* _tmp_4 = x_2;
lean_object* _tmp_11 = x_28;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_25, 0);
lean_dec(x_31);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 0, x_32);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_25, 0, x_19);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 0, x_34);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_18);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_free_object(x_19);
lean_free_object(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
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
lean_dec(x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_40 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio(x_1, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_41);
lean_free_object(x_18);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
lean_inc(x_2);
{
lean_object* _tmp_3 = x_17;
lean_object* _tmp_4 = x_2;
lean_object* _tmp_11 = x_43;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_12 = _tmp_11;
}
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
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
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 0, x_47);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_18);
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
lean_free_object(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_18, 1);
lean_inc(x_54);
lean_dec(x_18);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_55 = x_19;
} else {
 lean_dec_ref(x_19);
 x_55 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_56 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio(x_1, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_57);
lean_dec(x_55);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
lean_inc(x_2);
{
lean_object* _tmp_3 = x_17;
lean_object* _tmp_4 = x_2;
lean_object* _tmp_11 = x_59;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_12 = _tmp_11;
}
goto _start;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_62 = x_56;
} else {
 lean_dec_ref(x_56);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_57);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_3);
if (lean_is_scalar(x_55)) {
 x_65 = lean_alloc_ctor(0, 1, 0);
} else {
 x_65 = x_55;
 lean_ctor_set_tag(x_65, 0);
}
lean_ctor_set(x_65, 0, x_64);
if (lean_is_scalar(x_62)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_62;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_55);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_69 = x_56;
} else {
 lean_dec_ref(x_56);
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
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__0() {
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__0;
x_14 = l_Lean_RBNode_forIn_visit___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__1(x_1, x_13, x_12, x_10, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_25; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_18 = x_25;
goto block_24;
block_24:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
if (lean_is_scalar(x_17)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_17;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
return x_23;
}
}
}
else
{
uint8_t x_26; 
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
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg___closed__0;
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
lean_dec(x_9);
x_11 = l_Lean_Meta_instInhabitedDefaultInstances;
x_12 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_11, x_8, x_7, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_13, x_1);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_ctor_set(x_4, 0, x_16);
return x_4;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg___closed__0;
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*3);
lean_dec(x_21);
x_23 = l_Lean_Meta_instInhabitedDefaultInstances;
x_24 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_23, x_20, x_19, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_RBNode_find___at___Lean_NameMap_contains_spec__0___redArg(x_25, x_1);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_18);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_18);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getDefaultInstances___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__0___redArg(x_1, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_6);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_nat_dec_eq(x_19, x_1);
lean_dec(x_19);
if (x_20 == 0)
{
lean_free_object(x_15);
lean_dec(x_18);
lean_inc(x_2);
{
lean_object* _tmp_4 = x_16;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_22; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_22 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance(x_3, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
lean_free_object(x_15);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
lean_inc(x_2);
{
lean_object* _tmp_4 = x_16;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_12 = x_25;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_13 = _tmp_12;
}
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_22, 0);
lean_dec(x_28);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_15, 1, x_4);
lean_ctor_set(x_15, 0, x_29);
lean_ctor_set(x_22, 0, x_15);
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_15, 1, x_4);
lean_ctor_set(x_15, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_free_object(x_15);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
x_39 = lean_nat_dec_eq(x_38, x_1);
lean_dec(x_38);
if (x_39 == 0)
{
lean_dec(x_37);
lean_inc(x_2);
{
lean_object* _tmp_4 = x_16;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_41; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_41 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance(x_3, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_42);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
lean_inc(x_2);
{
lean_object* _tmp_4 = x_16;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_12 = x_44;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_13 = _tmp_12;
}
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
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
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_42);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_4);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_ctor_get(x_41, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_53 = x_41;
} else {
 lean_dec_ref(x_41);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__1___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_14; 
lean_inc(x_1);
x_14 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_isClass_x3f(x_15, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_10 = x_19;
goto block_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Meta_getDefaultInstances___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__0___redArg(x_21, x_8, x_20);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_10 = x_24;
goto block_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__0;
x_28 = l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__1___redArg(x_2, x_27, x_1, x_26, x_23, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_39);
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_dec(x_28);
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
lean_dec(x_30);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_28);
if (x_43 == 0)
{
return x_28;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_17);
if (x_47 == 0)
{
return x_17;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_17, 0);
x_49 = lean_ctor_get(x_17, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_17);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
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
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_14);
if (x_51 == 0)
{
return x_14;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_14, 0);
x_53 = lean_ctor_get(x_14, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_14);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___lam__0___boxed), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_14; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_14 = lean_nat_dec_lt(x_5, x_7);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_16 = lean_array_fget(x_1, x_5);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
x_18 = lean_box(3);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_17, x_19);
if (x_20 == 0)
{
x_9 = x_4;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_Lean_instInhabitedExpr;
x_22 = lean_array_get(x_21, x_2, x_5);
x_23 = l_Lean_Expr_mvarId_x21(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
x_9 = x_24;
x_10 = x_6;
goto block_13;
}
}
block_13:
{
lean_object* x_11; 
x_11 = lean_nat_add(x_5, x_8);
lean_dec(x_5);
x_4 = x_9;
x_5 = x_11;
x_6 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_14);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("defaultInstance", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__1;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isDefEq worked ", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" =\?= ", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Meta_forallMetaTelescopeReducing(x_14, x_16, x_18, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_196; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_24 = x_20;
} else {
 lean_dec_ref(x_20);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_26 = x_21;
} else {
 lean_dec_ref(x_21);
 x_26 = lean_box(0);
}
x_44 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__2;
x_45 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_44, x_7, x_22);
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
x_49 = l_Lean_mkAppN(x_11, x_23);
x_196 = lean_unbox(x_46);
lean_dec(x_46);
if (x_196 == 0)
{
x_133 = x_3;
x_134 = x_4;
x_135 = x_5;
x_136 = x_6;
x_137 = x_7;
x_138 = x_8;
x_139 = x_47;
goto block_195;
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_inc(x_2);
x_197 = l_Lean_Expr_mvar___override(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_197);
x_198 = lean_infer_type(x_197, x_5, x_6, x_7, x_8, x_47);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_49);
x_201 = lean_infer_type(x_49, x_5, x_6, x_7, x_8, x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10;
x_205 = lean_expr_dbg_to_string(x_197);
x_206 = l_Lean_stringToMessageData(x_205);
lean_dec(x_205);
x_207 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_206);
x_208 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__12;
x_209 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = l_Lean_MessageData_ofExpr(x_197);
x_211 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__6;
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Lean_MessageData_ofExpr(x_199);
x_215 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_216 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__8;
x_217 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
lean_inc(x_49);
x_218 = l_Lean_MessageData_ofExpr(x_49);
x_219 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_212);
x_221 = l_Lean_MessageData_ofExpr(x_202);
x_222 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_204);
x_224 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_44, x_223, x_5, x_6, x_7, x_8, x_203);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_133 = x_3;
x_134 = x_4;
x_135 = x_5;
x_136 = x_6;
x_137 = x_7;
x_138 = x_8;
x_139 = x_225;
goto block_195;
}
else
{
uint8_t x_226; 
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_226 = !lean_is_exclusive(x_201);
if (x_226 == 0)
{
return x_201;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_201, 0);
x_228 = lean_ctor_get(x_201, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_201);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_197);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_230 = !lean_is_exclusive(x_198);
if (x_230 == 0)
{
return x_198;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_198, 0);
x_232 = lean_ctor_get(x_198, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_198);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
block_43:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_box(0);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get_size(x_25);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_37);
x_39 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance_spec__0___redArg(x_25, x_23, x_38, x_34, x_35, x_33);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_25);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending(x_40, x_27, x_28, x_29, x_30, x_31, x_32, x_41);
return x_42;
}
block_132:
{
if (x_57 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_59 = lean_box(x_57);
if (lean_is_scalar(x_48)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_48;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_48);
x_61 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_44, x_56, x_58);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_26);
lean_dec(x_24);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_27 = x_55;
x_28 = x_53;
x_29 = x_54;
x_30 = x_51;
x_31 = x_56;
x_32 = x_52;
x_33 = x_64;
goto block_43;
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 1);
x_67 = lean_ctor_get(x_61, 0);
lean_dec(x_67);
lean_inc(x_52);
lean_inc(x_56);
lean_inc(x_51);
lean_inc(x_54);
lean_inc(x_50);
x_68 = lean_infer_type(x_50, x_54, x_51, x_56, x_52, x_66);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_52);
lean_inc(x_56);
lean_inc(x_51);
lean_inc(x_54);
lean_inc(x_49);
x_71 = lean_infer_type(x_49, x_54, x_51, x_56, x_52, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__4;
x_75 = l_Lean_MessageData_ofExpr(x_50);
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_75);
lean_ctor_set(x_61, 0, x_74);
x_76 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__6;
if (lean_is_scalar(x_26)) {
 x_77 = lean_alloc_ctor(7, 2, 0);
} else {
 x_77 = x_26;
 lean_ctor_set_tag(x_77, 7);
}
lean_ctor_set(x_77, 0, x_61);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_MessageData_ofExpr(x_69);
if (lean_is_scalar(x_24)) {
 x_79 = lean_alloc_ctor(7, 2, 0);
} else {
 x_79 = x_24;
 lean_ctor_set_tag(x_79, 7);
}
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__8;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_MessageData_ofExpr(x_49);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
x_85 = l_Lean_MessageData_ofExpr(x_72);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_44, x_88, x_54, x_51, x_56, x_52, x_73);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_27 = x_55;
x_28 = x_53;
x_29 = x_54;
x_30 = x_51;
x_31 = x_56;
x_32 = x_52;
x_33 = x_90;
goto block_43;
}
else
{
uint8_t x_91; 
lean_dec(x_69);
lean_free_object(x_61);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_91 = !lean_is_exclusive(x_71);
if (x_91 == 0)
{
return x_71;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_71, 0);
x_93 = lean_ctor_get(x_71, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_71);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_free_object(x_61);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_95 = !lean_is_exclusive(x_68);
if (x_95 == 0)
{
return x_68;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_68, 0);
x_97 = lean_ctor_get(x_68, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_68);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_61, 1);
lean_inc(x_99);
lean_dec(x_61);
lean_inc(x_52);
lean_inc(x_56);
lean_inc(x_51);
lean_inc(x_54);
lean_inc(x_50);
x_100 = lean_infer_type(x_50, x_54, x_51, x_56, x_52, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_52);
lean_inc(x_56);
lean_inc(x_51);
lean_inc(x_54);
lean_inc(x_49);
x_103 = lean_infer_type(x_49, x_54, x_51, x_56, x_52, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__4;
x_107 = l_Lean_MessageData_ofExpr(x_50);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__6;
if (lean_is_scalar(x_26)) {
 x_110 = lean_alloc_ctor(7, 2, 0);
} else {
 x_110 = x_26;
 lean_ctor_set_tag(x_110, 7);
}
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_MessageData_ofExpr(x_101);
if (lean_is_scalar(x_24)) {
 x_112 = lean_alloc_ctor(7, 2, 0);
} else {
 x_112 = x_24;
 lean_ctor_set_tag(x_112, 7);
}
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__8;
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_MessageData_ofExpr(x_49);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_109);
x_118 = l_Lean_MessageData_ofExpr(x_104);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10;
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_44, x_121, x_54, x_51, x_56, x_52, x_105);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_27 = x_55;
x_28 = x_53;
x_29 = x_54;
x_30 = x_51;
x_31 = x_56;
x_32 = x_52;
x_33 = x_123;
goto block_43;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_101);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_124 = lean_ctor_get(x_103, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_103, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_126 = x_103;
} else {
 lean_dec_ref(x_103);
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
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_128 = lean_ctor_get(x_100, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_100, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_130 = x_100;
} else {
 lean_dec_ref(x_100);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
}
}
block_195:
{
lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_140 = lean_ctor_get(x_135, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_135, sizeof(void*)*7 + 8);
x_142 = lean_ctor_get(x_135, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_135, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_135, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_135, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_135, 5);
lean_inc(x_146);
x_147 = lean_ctor_get(x_135, 6);
lean_inc(x_147);
x_148 = !lean_is_exclusive(x_140);
if (x_148 == 0)
{
uint8_t x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; uint64_t x_154; lean_object* x_155; lean_object* x_156; 
x_149 = lean_ctor_get_uint8(x_135, sizeof(void*)*7 + 9);
x_150 = lean_ctor_get_uint8(x_135, sizeof(void*)*7 + 10);
x_151 = l_Lean_Expr_mvar___override(x_2);
x_152 = lean_box(1);
x_153 = lean_unbox(x_152);
lean_ctor_set_uint8(x_140, 7, x_153);
x_154 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_140);
x_155 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_155, 0, x_140);
lean_ctor_set(x_155, 1, x_142);
lean_ctor_set(x_155, 2, x_143);
lean_ctor_set(x_155, 3, x_144);
lean_ctor_set(x_155, 4, x_145);
lean_ctor_set(x_155, 5, x_146);
lean_ctor_set(x_155, 6, x_147);
lean_ctor_set_uint64(x_155, sizeof(void*)*7, x_154);
lean_ctor_set_uint8(x_155, sizeof(void*)*7 + 8, x_141);
lean_ctor_set_uint8(x_155, sizeof(void*)*7 + 9, x_149);
lean_ctor_set_uint8(x_155, sizeof(void*)*7 + 10, x_150);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_49);
lean_inc(x_151);
x_156 = l_Lean_Meta_isExprDefEqGuarded(x_151, x_49, x_155, x_136, x_137, x_138, x_139);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_unbox(x_157);
lean_dec(x_157);
x_50 = x_151;
x_51 = x_136;
x_52 = x_138;
x_53 = x_134;
x_54 = x_135;
x_55 = x_133;
x_56 = x_137;
x_57 = x_159;
x_58 = x_158;
goto block_132;
}
else
{
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_156, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_156, 1);
lean_inc(x_161);
lean_dec(x_156);
x_162 = lean_unbox(x_160);
lean_dec(x_160);
x_50 = x_151;
x_51 = x_136;
x_52 = x_138;
x_53 = x_134;
x_54 = x_135;
x_55 = x_133;
x_56 = x_137;
x_57 = x_162;
x_58 = x_161;
goto block_132;
}
else
{
lean_dec(x_151);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
return x_156;
}
}
}
else
{
uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; uint64_t x_186; lean_object* x_187; lean_object* x_188; 
x_163 = lean_ctor_get_uint8(x_135, sizeof(void*)*7 + 9);
x_164 = lean_ctor_get_uint8(x_135, sizeof(void*)*7 + 10);
x_165 = lean_ctor_get_uint8(x_140, 0);
x_166 = lean_ctor_get_uint8(x_140, 1);
x_167 = lean_ctor_get_uint8(x_140, 2);
x_168 = lean_ctor_get_uint8(x_140, 3);
x_169 = lean_ctor_get_uint8(x_140, 4);
x_170 = lean_ctor_get_uint8(x_140, 5);
x_171 = lean_ctor_get_uint8(x_140, 6);
x_172 = lean_ctor_get_uint8(x_140, 8);
x_173 = lean_ctor_get_uint8(x_140, 9);
x_174 = lean_ctor_get_uint8(x_140, 10);
x_175 = lean_ctor_get_uint8(x_140, 11);
x_176 = lean_ctor_get_uint8(x_140, 12);
x_177 = lean_ctor_get_uint8(x_140, 13);
x_178 = lean_ctor_get_uint8(x_140, 14);
x_179 = lean_ctor_get_uint8(x_140, 15);
x_180 = lean_ctor_get_uint8(x_140, 16);
x_181 = lean_ctor_get_uint8(x_140, 17);
lean_dec(x_140);
x_182 = l_Lean_Expr_mvar___override(x_2);
x_183 = lean_box(1);
x_184 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_184, 0, x_165);
lean_ctor_set_uint8(x_184, 1, x_166);
lean_ctor_set_uint8(x_184, 2, x_167);
lean_ctor_set_uint8(x_184, 3, x_168);
lean_ctor_set_uint8(x_184, 4, x_169);
lean_ctor_set_uint8(x_184, 5, x_170);
lean_ctor_set_uint8(x_184, 6, x_171);
x_185 = lean_unbox(x_183);
lean_ctor_set_uint8(x_184, 7, x_185);
lean_ctor_set_uint8(x_184, 8, x_172);
lean_ctor_set_uint8(x_184, 9, x_173);
lean_ctor_set_uint8(x_184, 10, x_174);
lean_ctor_set_uint8(x_184, 11, x_175);
lean_ctor_set_uint8(x_184, 12, x_176);
lean_ctor_set_uint8(x_184, 13, x_177);
lean_ctor_set_uint8(x_184, 14, x_178);
lean_ctor_set_uint8(x_184, 15, x_179);
lean_ctor_set_uint8(x_184, 16, x_180);
lean_ctor_set_uint8(x_184, 17, x_181);
x_186 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_184);
x_187 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_142);
lean_ctor_set(x_187, 2, x_143);
lean_ctor_set(x_187, 3, x_144);
lean_ctor_set(x_187, 4, x_145);
lean_ctor_set(x_187, 5, x_146);
lean_ctor_set(x_187, 6, x_147);
lean_ctor_set_uint64(x_187, sizeof(void*)*7, x_186);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 8, x_141);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 9, x_163);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 10, x_164);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_49);
lean_inc(x_182);
x_188 = l_Lean_Meta_isExprDefEqGuarded(x_182, x_49, x_187, x_136, x_137, x_138, x_139);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_unbox(x_189);
lean_dec(x_189);
x_50 = x_182;
x_51 = x_136;
x_52 = x_138;
x_53 = x_134;
x_54 = x_135;
x_55 = x_133;
x_56 = x_137;
x_57 = x_191;
x_58 = x_190;
goto block_132;
}
else
{
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
lean_dec(x_188);
x_194 = lean_unbox(x_192);
lean_dec(x_192);
x_50 = x_182;
x_51 = x_136;
x_52 = x_138;
x_53 = x_134;
x_54 = x_135;
x_55 = x_133;
x_56 = x_137;
x_57 = x_194;
x_58 = x_193;
goto block_132;
}
else
{
lean_dec(x_182);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
return x_188;
}
}
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_234 = !lean_is_exclusive(x_19);
if (x_234 == 0)
{
return x_19;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_19, 0);
x_236 = lean_ctor_get(x_19, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_19);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_238 = !lean_is_exclusive(x_13);
if (x_238 == 0)
{
return x_13;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_13, 0);
x_240 = lean_ctor_get(x_13, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_13);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_242 = !lean_is_exclusive(x_10);
if (x_242 == 0)
{
return x_10;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_10, 0);
x_244 = lean_ctor_get(x_10, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_10);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0), 9, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_1);
x_11 = l_Lean_commitWhen___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27_spec__0(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
x_13 = l_List_isEmpty___redArg(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_free_object(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeSomeUsingDefault_x3f(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(x_13);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(x_13);
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
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_1 = x_23;
x_8 = x_22;
goto _start;
}
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
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
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
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_29);
return x_9;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_32 = l_List_isEmpty___redArg(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_33 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeSomeUsingDefault_x3f(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_box(x_32);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_1 = x_40;
x_8 = x_39;
goto _start;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_box(x_32);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_31);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_9);
if (x_48 == 0)
{
return x_9;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_9, 0);
x_50 = lean_ctor_get(x_9, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_9);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
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
lean_free_object(x_1);
lean_dec(x_12);
return x_18;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set(x_19, 0, x_1);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
lean_ctor_set(x_1, 1, x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_28 = x_19;
} else {
 lean_dec_ref(x_19);
 x_28 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_27);
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
}
else
{
lean_free_object(x_1);
lean_dec(x_12);
return x_18;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_14, 0);
lean_dec(x_32);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_14, 0, x_33);
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_13);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
return x_14;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_41);
x_43 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeSomeUsingDefault_x3f(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_dec(x_41);
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
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
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_41);
lean_ctor_set(x_53, 1, x_51);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
else
{
lean_dec(x_41);
return x_47;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_ctor_get(x_43, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_57 = x_43;
} else {
 lean_dec_ref(x_43);
 x_57 = lean_box(0);
}
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_42);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_ctor_get(x_43, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_43, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_62 = x_43;
} else {
 lean_dec_ref(x_43);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getDefaultInstances___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getDefaultInstances___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = l_Lean_Elab_Term_getSyntheticMVarDecl_x3f___redArg(x_14, x_5, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_15;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_9 = x_18;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_10 = _tmp_9;
}
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_21);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
x_26 = lean_ctor_get(x_8, 2);
x_27 = lean_ctor_get(x_8, 3);
x_28 = lean_ctor_get(x_8, 4);
x_29 = lean_ctor_get(x_8, 5);
x_30 = lean_ctor_get(x_8, 6);
x_31 = lean_ctor_get(x_8, 7);
x_32 = lean_ctor_get(x_8, 8);
x_33 = lean_ctor_get(x_8, 9);
x_34 = lean_ctor_get(x_8, 10);
x_35 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_36 = lean_ctor_get(x_8, 11);
x_37 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_38 = lean_ctor_get(x_8, 12);
x_39 = l_Lean_replaceRef(x_23, x_29);
lean_dec(x_23);
lean_inc(x_38);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_40 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_40, 0, x_24);
lean_ctor_set(x_40, 1, x_25);
lean_ctor_set(x_40, 2, x_26);
lean_ctor_set(x_40, 3, x_27);
lean_ctor_set(x_40, 4, x_28);
lean_ctor_set(x_40, 5, x_39);
lean_ctor_set(x_40, 6, x_30);
lean_ctor_set(x_40, 7, x_31);
lean_ctor_set(x_40, 8, x_32);
lean_ctor_set(x_40, 9, x_33);
lean_ctor_set(x_40, 10, x_34);
lean_ctor_set(x_40, 11, x_36);
lean_ctor_set(x_40, 12, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*13, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*13 + 1, x_37);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_14);
x_41 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio(x_14, x_1, x_4, x_5, x_6, x_7, x_40, x_9, x_22);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_42);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_15;
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
lean_dec(x_14);
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
x_52 = l_List_reverse___redArg(x_15);
x_53 = l_List_appendTR___redArg(x_52, x_3);
lean_ctor_set(x_48, 2, x_53);
x_54 = lean_st_ref_set(x_5, x_48, x_49);
lean_dec(x_5);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_42);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_42);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_59 = lean_ctor_get(x_48, 0);
x_60 = lean_ctor_get(x_48, 1);
x_61 = lean_ctor_get(x_48, 3);
x_62 = lean_ctor_get(x_48, 4);
x_63 = lean_ctor_get(x_48, 5);
x_64 = lean_ctor_get(x_48, 6);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_48);
x_65 = l_List_reverse___redArg(x_15);
x_66 = l_List_appendTR___redArg(x_65, x_3);
x_67 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_60);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_61);
lean_ctor_set(x_67, 4, x_62);
lean_ctor_set(x_67, 5, x_63);
lean_ctor_set(x_67, 6, x_64);
x_68 = lean_st_ref_set(x_5, x_67, x_49);
lean_dec(x_5);
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
lean_ctor_set(x_71, 0, x_42);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
else
{
lean_free_object(x_2);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_41;
}
}
else
{
lean_object* x_72; 
lean_dec(x_21);
lean_dec(x_20);
x_72 = lean_ctor_get(x_16, 1);
lean_inc(x_72);
lean_dec(x_16);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_15;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_9 = x_72;
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
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_2, 0);
x_75 = lean_ctor_get(x_2, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_2);
x_76 = l_Lean_Elab_Term_getSyntheticMVarDecl_x3f___redArg(x_74, x_5, x_10);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_3);
x_2 = x_75;
x_3 = x_79;
x_10 = x_78;
goto _start;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_82);
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_dec(x_76);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_ctor_get(x_8, 0);
x_86 = lean_ctor_get(x_8, 1);
x_87 = lean_ctor_get(x_8, 2);
x_88 = lean_ctor_get(x_8, 3);
x_89 = lean_ctor_get(x_8, 4);
x_90 = lean_ctor_get(x_8, 5);
x_91 = lean_ctor_get(x_8, 6);
x_92 = lean_ctor_get(x_8, 7);
x_93 = lean_ctor_get(x_8, 8);
x_94 = lean_ctor_get(x_8, 9);
x_95 = lean_ctor_get(x_8, 10);
x_96 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_97 = lean_ctor_get(x_8, 11);
x_98 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_99 = lean_ctor_get(x_8, 12);
x_100 = l_Lean_replaceRef(x_84, x_90);
lean_dec(x_84);
lean_inc(x_99);
lean_inc(x_97);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
x_101 = lean_alloc_ctor(0, 13, 2);
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
lean_ctor_set(x_101, 12, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*13, x_96);
lean_ctor_set_uint8(x_101, sizeof(void*)*13 + 1, x_98);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_74);
x_102 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio(x_74, x_1, x_4, x_5, x_6, x_7, x_101, x_9, x_83);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_unbox(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_103);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_74);
lean_ctor_set(x_106, 1, x_3);
x_2 = x_75;
x_3 = x_106;
x_10 = x_105;
goto _start;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_74);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_108 = lean_ctor_get(x_102, 1);
lean_inc(x_108);
lean_dec(x_102);
x_109 = lean_st_ref_take(x_5, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 4);
lean_inc(x_115);
x_116 = lean_ctor_get(x_110, 5);
lean_inc(x_116);
x_117 = lean_ctor_get(x_110, 6);
lean_inc(x_117);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 lean_ctor_release(x_110, 4);
 lean_ctor_release(x_110, 5);
 lean_ctor_release(x_110, 6);
 x_118 = x_110;
} else {
 lean_dec_ref(x_110);
 x_118 = lean_box(0);
}
x_119 = l_List_reverse___redArg(x_75);
x_120 = l_List_appendTR___redArg(x_119, x_3);
if (lean_is_scalar(x_118)) {
 x_121 = lean_alloc_ctor(0, 7, 0);
} else {
 x_121 = x_118;
}
lean_ctor_set(x_121, 0, x_112);
lean_ctor_set(x_121, 1, x_113);
lean_ctor_set(x_121, 2, x_120);
lean_ctor_set(x_121, 3, x_114);
lean_ctor_set(x_121, 4, x_115);
lean_ctor_set(x_121, 5, x_116);
lean_ctor_set(x_121, 6, x_117);
x_122 = lean_st_ref_set(x_5, x_121, x_111);
lean_dec(x_5);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_103);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_102;
}
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_82);
lean_dec(x_81);
x_126 = lean_ctor_get(x_76, 1);
lean_inc(x_126);
lean_dec(x_76);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_74);
lean_ctor_set(x_127, 1, x_3);
x_2 = x_75;
x_3 = x_127;
x_10 = x_126;
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
x_13 = l_List_reverse___redArg(x_12);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_RBNode_forIn_visit___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault_spec__0(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_25);
lean_free_object(x_18);
lean_free_object(x_17);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
lean_inc(x_1);
{
lean_object* _tmp_2 = x_16;
lean_object* _tmp_3 = x_1;
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_24, 0);
lean_dec(x_30);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 0, x_31);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_24, 0, x_18);
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 0, x_33);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_17);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_free_object(x_18);
lean_free_object(x_17);
lean_dec(x_16);
lean_dec(x_10);
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
else
{
lean_object* x_39; 
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_39 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_40);
lean_free_object(x_17);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
lean_inc(x_1);
{
lean_object* _tmp_2 = x_16;
lean_object* _tmp_3 = x_1;
lean_object* _tmp_10 = x_42;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_45 = x_39;
} else {
 lean_dec_ref(x_39);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 0, x_46);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_17);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_51 = x_39;
} else {
 lean_dec_ref(x_39);
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
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
lean_dec(x_17);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_54 = x_18;
} else {
 lean_dec_ref(x_18);
 x_54 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_55 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_56);
lean_dec(x_54);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
lean_inc(x_1);
{
lean_object* _tmp_2 = x_16;
lean_object* _tmp_3 = x_1;
lean_object* _tmp_10 = x_58;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_61 = x_55;
} else {
 lean_dec_ref(x_55);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_56);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_2);
if (lean_is_scalar(x_54)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_54;
 lean_ctor_set_tag(x_64, 0);
}
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_61)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_61;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_54);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_66 = lean_ctor_get(x_55, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_68 = x_55;
} else {
 lean_dec_ref(x_55);
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
}
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__0;
x_13 = l_Lean_RBNode_forIn_visit___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault_spec__0(x_12, x_11, x_9, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_24; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_17 = x_24;
goto block_23;
block_23:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
if (lean_is_scalar(x_16)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_16;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
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
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_RBNode_forIn_visit___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_12;
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
static lean_object* _init_l_panic___at___Lean_Elab_Term_reportStuckSyntheticMVar_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Term_reportStuckSyntheticMVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___Lean_Elab_Term_reportStuckSyntheticMVar_spec__0___closed__0;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typeclass instance problem is stuck, it is often due to metavariables", 69, 69);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_getMVarDecl___redArg(x_1, x_6, x_9);
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
x_18 = lean_ctor_get(x_16, 6);
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
x_21 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___closed__1;
x_22 = l_Lean_indentExpr(x_20);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
x_23 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_2);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
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
x_31 = lean_ctor_get(x_29, 6);
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
x_34 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___closed__1;
x_35 = l_Lean_indentExpr(x_33);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_35);
lean_ctor_set(x_10, 0, x_34);
x_36 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_10);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_2);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
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
x_49 = lean_ctor_get(x_46, 6);
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
x_52 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___closed__1;
x_53 = l_Lean_indentExpr(x_51);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_2);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
x_59 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_47);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_14 = lean_infer_type(x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Term_getMVarDecl___redArg(x_3, x_10, x_16);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Term_throwTypeMismatchError___redArg(x_19, x_5, x_15, x_2, x_6, x_9, x_10, x_11, x_12, x_18);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_MessageData_ofFormat(x_24);
lean_ctor_set(x_4, 0, x_25);
x_26 = l_Lean_Elab_Term_throwTypeMismatchError___redArg(x_4, x_5, x_15, x_2, x_6, x_9, x_10, x_11, x_12, x_21);
lean_dec(x_4);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_4, 0);
lean_inc(x_27);
lean_dec(x_4);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_MessageData_ofFormat(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_Elab_Term_throwTypeMismatchError___redArg(x_30, x_5, x_15, x_2, x_6, x_9, x_10, x_11, x_12, x_21);
lean_dec(x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_6);
lean_dec(x_4);
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_37 = lean_apply_8(x_36, x_3, x_5, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_39);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_37);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic execution is stuck, goal contains metavariables", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Term_getMVarDecl___redArg(x_1, x_5, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___closed__1;
x_15 = l_Lean_indentExpr(x_13);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_15);
lean_ctor_set(x_9, 0, x_14);
x_16 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___closed__1;
x_23 = l_Lean_indentExpr(x_21);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.reportStuckSyntheticMVar", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__2;
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(235u);
x_4 = l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__0;
x_5 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_Elab_Term_getSyntheticMVarDecl_x3f___redArg(x_1, x_4, x_9);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_20, 1);
x_31 = lean_ctor_get(x_20, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_7, 5);
x_36 = l_Lean_replaceRef(x_32, x_35);
lean_dec(x_35);
lean_dec(x_32);
lean_ctor_set(x_7, 5, x_36);
switch (lean_obj_tag(x_33)) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_20);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l_Lean_Elab_Term_extraMsgToMsg(x_37);
lean_dec(x_37);
lean_inc(x_1);
x_39 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___boxed), 9, 2);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_38);
x_40 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_1, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec(x_7);
lean_dec(x_33);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_41 = lean_box(0);
lean_ctor_set(x_20, 0, x_41);
return x_20;
}
}
case 1:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_20);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_33, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_33, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_33, 4);
lean_inc(x_46);
lean_dec(x_33);
lean_inc(x_1);
x_47 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__1___boxed), 13, 6);
lean_closure_set(x_47, 0, x_46);
lean_closure_set(x_47, 1, x_44);
lean_closure_set(x_47, 2, x_1);
lean_closure_set(x_47, 3, x_42);
lean_closure_set(x_47, 4, x_43);
lean_closure_set(x_47, 5, x_45);
x_48 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_1, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_48;
}
case 2:
{
uint8_t x_49; 
lean_free_object(x_20);
x_49 = lean_ctor_get_uint8(x_33, sizeof(void*)*3);
if (x_49 == 0)
{
lean_dec(x_33);
lean_dec(x_1);
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_30;
goto block_19;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_33, 1);
lean_inc(x_50);
lean_dec(x_33);
lean_inc(x_1);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___boxed), 8, 1);
lean_closure_set(x_51, 0, x_1);
x_52 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5), 10, 3);
lean_closure_set(x_52, 0, lean_box(0));
lean_closure_set(x_52, 1, x_1);
lean_closure_set(x_52, 2, x_51);
x_53 = l_Lean_Elab_Term_withSavedContext___redArg(x_50, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_53;
}
}
default: 
{
lean_dec(x_33);
lean_free_object(x_20);
lean_dec(x_1);
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
x_16 = x_30;
goto block_19;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 1);
x_56 = lean_ctor_get(x_7, 2);
x_57 = lean_ctor_get(x_7, 3);
x_58 = lean_ctor_get(x_7, 4);
x_59 = lean_ctor_get(x_7, 5);
x_60 = lean_ctor_get(x_7, 6);
x_61 = lean_ctor_get(x_7, 7);
x_62 = lean_ctor_get(x_7, 8);
x_63 = lean_ctor_get(x_7, 9);
x_64 = lean_ctor_get(x_7, 10);
x_65 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_66 = lean_ctor_get(x_7, 11);
x_67 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_68 = lean_ctor_get(x_7, 12);
lean_inc(x_68);
lean_inc(x_66);
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
lean_dec(x_7);
x_69 = l_Lean_replaceRef(x_32, x_59);
lean_dec(x_59);
lean_dec(x_32);
x_70 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_70, 0, x_54);
lean_ctor_set(x_70, 1, x_55);
lean_ctor_set(x_70, 2, x_56);
lean_ctor_set(x_70, 3, x_57);
lean_ctor_set(x_70, 4, x_58);
lean_ctor_set(x_70, 5, x_69);
lean_ctor_set(x_70, 6, x_60);
lean_ctor_set(x_70, 7, x_61);
lean_ctor_set(x_70, 8, x_62);
lean_ctor_set(x_70, 9, x_63);
lean_ctor_set(x_70, 10, x_64);
lean_ctor_set(x_70, 11, x_66);
lean_ctor_set(x_70, 12, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*13, x_65);
lean_ctor_set_uint8(x_70, sizeof(void*)*13 + 1, x_67);
switch (lean_obj_tag(x_33)) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_free_object(x_20);
x_71 = lean_ctor_get(x_33, 0);
lean_inc(x_71);
lean_dec(x_33);
x_72 = l_Lean_Elab_Term_extraMsgToMsg(x_71);
lean_dec(x_71);
lean_inc(x_1);
x_73 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___boxed), 9, 2);
lean_closure_set(x_73, 0, x_1);
lean_closure_set(x_73, 1, x_72);
x_74 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_1, x_73, x_3, x_4, x_5, x_6, x_70, x_8, x_30);
return x_74;
}
else
{
lean_object* x_75; 
lean_dec(x_70);
lean_dec(x_33);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_75 = lean_box(0);
lean_ctor_set(x_20, 0, x_75);
return x_20;
}
}
case 1:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_free_object(x_20);
x_76 = lean_ctor_get(x_33, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_33, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_33, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_33, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_33, 4);
lean_inc(x_80);
lean_dec(x_33);
lean_inc(x_1);
x_81 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__1___boxed), 13, 6);
lean_closure_set(x_81, 0, x_80);
lean_closure_set(x_81, 1, x_78);
lean_closure_set(x_81, 2, x_1);
lean_closure_set(x_81, 3, x_76);
lean_closure_set(x_81, 4, x_77);
lean_closure_set(x_81, 5, x_79);
x_82 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_1, x_81, x_3, x_4, x_5, x_6, x_70, x_8, x_30);
return x_82;
}
case 2:
{
uint8_t x_83; 
lean_free_object(x_20);
x_83 = lean_ctor_get_uint8(x_33, sizeof(void*)*3);
if (x_83 == 0)
{
lean_dec(x_33);
lean_dec(x_1);
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_70;
x_15 = x_8;
x_16 = x_30;
goto block_19;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_33, 1);
lean_inc(x_84);
lean_dec(x_33);
lean_inc(x_1);
x_85 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___boxed), 8, 1);
lean_closure_set(x_85, 0, x_1);
x_86 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5), 10, 3);
lean_closure_set(x_86, 0, lean_box(0));
lean_closure_set(x_86, 1, x_1);
lean_closure_set(x_86, 2, x_85);
x_87 = l_Lean_Elab_Term_withSavedContext___redArg(x_84, x_86, x_3, x_4, x_5, x_6, x_70, x_8, x_30);
return x_87;
}
}
default: 
{
lean_dec(x_33);
lean_free_object(x_20);
lean_dec(x_1);
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_70;
x_15 = x_8;
x_16 = x_30;
goto block_19;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_88 = lean_ctor_get(x_20, 1);
lean_inc(x_88);
lean_dec(x_20);
x_89 = lean_ctor_get(x_28, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_28, 1);
lean_inc(x_90);
lean_dec(x_28);
x_91 = lean_ctor_get(x_7, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_7, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_7, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_7, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_7, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_7, 5);
lean_inc(x_96);
x_97 = lean_ctor_get(x_7, 6);
lean_inc(x_97);
x_98 = lean_ctor_get(x_7, 7);
lean_inc(x_98);
x_99 = lean_ctor_get(x_7, 8);
lean_inc(x_99);
x_100 = lean_ctor_get(x_7, 9);
lean_inc(x_100);
x_101 = lean_ctor_get(x_7, 10);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_103 = lean_ctor_get(x_7, 11);
lean_inc(x_103);
x_104 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_105 = lean_ctor_get(x_7, 12);
lean_inc(x_105);
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
 lean_ctor_release(x_7, 12);
 x_106 = x_7;
} else {
 lean_dec_ref(x_7);
 x_106 = lean_box(0);
}
x_107 = l_Lean_replaceRef(x_89, x_96);
lean_dec(x_96);
lean_dec(x_89);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 13, 2);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_91);
lean_ctor_set(x_108, 1, x_92);
lean_ctor_set(x_108, 2, x_93);
lean_ctor_set(x_108, 3, x_94);
lean_ctor_set(x_108, 4, x_95);
lean_ctor_set(x_108, 5, x_107);
lean_ctor_set(x_108, 6, x_97);
lean_ctor_set(x_108, 7, x_98);
lean_ctor_set(x_108, 8, x_99);
lean_ctor_set(x_108, 9, x_100);
lean_ctor_set(x_108, 10, x_101);
lean_ctor_set(x_108, 11, x_103);
lean_ctor_set(x_108, 12, x_105);
lean_ctor_set_uint8(x_108, sizeof(void*)*13, x_102);
lean_ctor_set_uint8(x_108, sizeof(void*)*13 + 1, x_104);
switch (lean_obj_tag(x_90)) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_90, 0);
lean_inc(x_109);
lean_dec(x_90);
x_110 = l_Lean_Elab_Term_extraMsgToMsg(x_109);
lean_dec(x_109);
lean_inc(x_1);
x_111 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___boxed), 9, 2);
lean_closure_set(x_111, 0, x_1);
lean_closure_set(x_111, 1, x_110);
x_112 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_1, x_111, x_3, x_4, x_5, x_6, x_108, x_8, x_88);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_108);
lean_dec(x_90);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_88);
return x_114;
}
}
case 1:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_90, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_90, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_90, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_90, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_90, 4);
lean_inc(x_119);
lean_dec(x_90);
lean_inc(x_1);
x_120 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__1___boxed), 13, 6);
lean_closure_set(x_120, 0, x_119);
lean_closure_set(x_120, 1, x_117);
lean_closure_set(x_120, 2, x_1);
lean_closure_set(x_120, 3, x_115);
lean_closure_set(x_120, 4, x_116);
lean_closure_set(x_120, 5, x_118);
x_121 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_1, x_120, x_3, x_4, x_5, x_6, x_108, x_8, x_88);
return x_121;
}
case 2:
{
uint8_t x_122; 
x_122 = lean_ctor_get_uint8(x_90, sizeof(void*)*3);
if (x_122 == 0)
{
lean_dec(x_90);
lean_dec(x_1);
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_108;
x_15 = x_8;
x_16 = x_88;
goto block_19;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_90, 1);
lean_inc(x_123);
lean_dec(x_90);
lean_inc(x_1);
x_124 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___boxed), 8, 1);
lean_closure_set(x_124, 0, x_1);
x_125 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5), 10, 3);
lean_closure_set(x_125, 0, lean_box(0));
lean_closure_set(x_125, 1, x_1);
lean_closure_set(x_125, 2, x_124);
x_126 = l_Lean_Elab_Term_withSavedContext___redArg(x_123, x_125, x_3, x_4, x_5, x_6, x_108, x_8, x_88);
return x_126;
}
}
default: 
{
lean_dec(x_90);
lean_dec(x_1);
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_108;
x_15 = x_8;
x_16 = x_88;
goto block_19;
}
}
}
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__1;
x_18 = l_panic___at___Lean_Elab_Term_reportStuckSyntheticMVar_spec__0(x_17, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Term_reportStuckSyntheticMVar(x_13, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_2);
{
lean_object* _tmp_2 = x_14;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_10 = x_16;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_spec__0___redArg(x_1, x_2, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_10, 2);
x_14 = lean_box(0);
lean_ctor_set(x_10, 2, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_spec__0___redArg(x_1, x_17, x_13, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
return x_18;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
x_25 = lean_ctor_get(x_10, 2);
x_26 = lean_ctor_get(x_10, 3);
x_27 = lean_ctor_get(x_10, 4);
x_28 = lean_ctor_get(x_10, 5);
x_29 = lean_ctor_get(x_10, 6);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 4, x_27);
lean_ctor_set(x_31, 5, x_28);
lean_ctor_set(x_31, 6, x_29);
x_32 = lean_st_ref_set(x_3, x_31, x_11);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_spec__0___redArg(x_1, x_34, x_25, x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
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
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
else
{
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_spec__0___redArg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_spec__0(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_15;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = l_Lean_Elab_Term_getSyntheticMVarDecl_x3f___redArg(x_8, x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
{
lean_object* _tmp_2 = x_9;
lean_object* _tmp_3 = x_1;
lean_object* _tmp_5 = x_12;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_10, 1);
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Syntax_getPos_x3f(x_19, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_free_object(x_14);
lean_dec(x_19);
lean_free_object(x_10);
lean_inc(x_1);
{
lean_object* _tmp_2 = x_9;
lean_object* _tmp_3 = x_1;
lean_object* _tmp_5 = x_16;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_6 = _tmp_5;
}
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 0, x_23);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_27; 
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 0, x_27);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Syntax_getPos_x3f(x_28, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_dec(x_28);
lean_free_object(x_10);
lean_inc(x_1);
{
lean_object* _tmp_2 = x_9;
lean_object* _tmp_3 = x_1;
lean_object* _tmp_5 = x_16;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_2);
lean_ctor_set(x_10, 0, x_35);
return x_10;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_dec(x_10);
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_38 = x_14;
} else {
 lean_dec_ref(x_14);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
x_40 = lean_unbox(x_39);
x_41 = l_Lean_Syntax_getPos_x3f(x_37, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_dec(x_38);
lean_dec(x_37);
lean_inc(x_1);
{
lean_object* _tmp_2 = x_9;
lean_object* _tmp_3 = x_1;
lean_object* _tmp_5 = x_36;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_1);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_38;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_36);
return x_46;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef_spec__0___redArg(x_1, x_2, x_4, x_5, x_8, x_13);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___closed__0() {
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
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___closed__0;
x_14 = l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef_spec__0___redArg(x_13, x_12, x_11, x_13, x_2, x_10);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_level_eq(x_10, x_12);
if (x_14 == 0)
{
x_7 = x_14;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = lean_level_eq(x_11, x_13);
x_7 = x_15;
goto block_9;
}
block_9:
{
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Level_hash(x_6);
lean_dec(x_6);
x_10 = l_Lean_Level_hash(x_7);
lean_dec(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_1, x_22);
lean_ctor_set(x_2, 2, x_23);
x_24 = lean_array_uset(x_1, x_22, x_2);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
x_31 = lean_array_get_size(x_1);
x_32 = l_Lean_Level_hash(x_29);
lean_dec(x_29);
x_33 = l_Lean_Level_hash(x_30);
lean_dec(x_30);
x_34 = lean_uint64_mix_hash(x_32, x_33);
x_35 = 32;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = 16;
x_39 = lean_uint64_shift_right(x_37, x_38);
x_40 = lean_uint64_xor(x_37, x_39);
x_41 = lean_uint64_to_usize(x_40);
x_42 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_43 = 1;
x_44 = lean_usize_sub(x_42, x_43);
x_45 = lean_usize_land(x_41, x_44);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_7, x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 0);
lean_dec(x_20);
x_21 = lean_array_uget(x_5, x_7);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_19);
x_22 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4(x_1, x_2, x_3, x_21, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_8, 0, x_26);
lean_ctor_set(x_22, 0, x_8);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_8, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_19);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_31);
lean_ctor_set(x_8, 0, x_4);
x_32 = 1;
x_33 = lean_usize_add(x_7, x_32);
x_7 = x_33;
x_15 = x_30;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_8);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
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
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_8, 1);
lean_inc(x_39);
lean_dec(x_8);
x_40 = lean_array_uget(x_5, x_7);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_39);
x_41 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4(x_1, x_2, x_3, x_40, x_39, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_39);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
lean_dec(x_39);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
lean_inc(x_4);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_50, 1, x_49);
x_51 = 1;
x_52 = lean_usize_add(x_7, x_51);
x_7 = x_52;
x_8 = x_50;
x_15 = x_48;
goto _start;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_39);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_41, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_56 = x_41;
} else {
 lean_dec_ref(x_41);
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
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 0);
lean_dec(x_18);
x_19 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_17);
x_20 = lean_apply_9(x_1, x_19, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_17);
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
uint8_t x_33; 
lean_free_object(x_6);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_dec(x_6);
x_38 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_37);
x_39 = lean_apply_9(x_1, x_38, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
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
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; 
lean_dec(x_37);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_dec(x_39);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
lean_inc(x_2);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_2);
lean_ctor_set(x_48, 1, x_47);
x_49 = 1;
x_50 = lean_usize_add(x_5, x_49);
x_5 = x_50;
x_6 = x_48;
x_13 = x_46;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_54 = x_39;
} else {
 lean_dec_ref(x_39);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_2, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
lean_dec(x_2);
x_78 = lean_ctor_get(x_1, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 2);
lean_inc(x_79);
x_80 = l_Lean_Level_normLt(x_79, x_78);
if (x_80 == 0)
{
x_18 = x_76;
x_19 = x_78;
x_20 = x_79;
x_21 = x_77;
x_22 = x_9;
goto block_75;
}
else
{
x_18 = x_76;
x_19 = x_79;
x_20 = x_78;
x_21 = x_77;
x_22 = x_9;
goto block_75;
}
block_17:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_push(x_10, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
block_75:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; uint8_t x_42; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_20);
lean_inc(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_20);
x_26 = lean_array_get_size(x_24);
x_27 = l_Lean_Level_hash(x_19);
lean_dec(x_19);
x_28 = l_Lean_Level_hash(x_20);
lean_dec(x_20);
x_29 = lean_uint64_mix_hash(x_27, x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_24, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__0___redArg(x_25, x_41);
if (x_42 == 0)
{
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_44 = lean_ctor_get(x_18, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_18, 0);
lean_dec(x_45);
x_46 = lean_box(0);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_23, x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_25);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_49, 2, x_41);
x_50 = lean_array_uset(x_24, x_40, x_49);
x_51 = lean_unsigned_to_nat(4u);
x_52 = lean_nat_mul(x_48, x_51);
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_nat_div(x_52, x_53);
lean_dec(x_52);
x_55 = lean_array_get_size(x_50);
x_56 = lean_nat_dec_le(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1___redArg(x_50);
lean_ctor_set(x_18, 1, x_57);
lean_ctor_set(x_18, 0, x_48);
x_10 = x_21;
x_11 = x_22;
x_12 = x_18;
goto block_17;
}
else
{
lean_ctor_set(x_18, 1, x_50);
lean_ctor_set(x_18, 0, x_48);
x_10 = x_21;
x_11 = x_22;
x_12 = x_18;
goto block_17;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_18);
x_58 = lean_box(0);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_23, x_59);
lean_dec(x_23);
x_61 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_41);
x_62 = lean_array_uset(x_24, x_40, x_61);
x_63 = lean_unsigned_to_nat(4u);
x_64 = lean_nat_mul(x_60, x_63);
x_65 = lean_unsigned_to_nat(3u);
x_66 = lean_nat_div(x_64, x_65);
lean_dec(x_64);
x_67 = lean_array_get_size(x_62);
x_68 = lean_nat_dec_le(x_66, x_67);
lean_dec(x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1___redArg(x_62);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_69);
x_10 = x_21;
x_11 = x_22;
x_12 = x_70;
goto block_17;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_60);
lean_ctor_set(x_71, 1, x_62);
x_10 = x_21;
x_11 = x_22;
x_12 = x_71;
goto block_17;
}
}
}
else
{
lean_dec(x_41);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_10 = x_21;
x_11 = x_22;
x_12 = x_18;
goto block_17;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_41);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_1);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_18);
lean_ctor_set(x_72, 1, x_21);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_22);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_array_size(x_14);
x_18 = 0;
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4_spec__4(x_1, x_2, x_3, x_15, x_14, x_17, x_18, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_24);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_20);
lean_free_object(x_4);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec(x_21);
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
lean_free_object(x_4);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_4, 0);
lean_inc(x_38);
lean_dec(x_4);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_5);
x_41 = lean_array_size(x_38);
x_42 = 0;
x_43 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4_spec__4(x_1, x_2, x_3, x_39, x_38, x_41, x_42, x_40, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_38);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_47 = x_43;
} else {
 lean_dec_ref(x_43);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_44);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_52 = x_43;
} else {
 lean_dec_ref(x_43);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
lean_dec(x_45);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_43, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_43, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_57 = x_43;
} else {
 lean_dec_ref(x_43);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_4);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_4, 0);
x_61 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4___lam__0___boxed), 9, 0);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_5);
x_64 = lean_array_size(x_60);
x_65 = 0;
x_66 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4_spec__5(x_61, x_62, x_60, x_64, x_65, x_63, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_60);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_66, 0);
lean_dec(x_70);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
lean_ctor_set(x_4, 0, x_71);
lean_ctor_set(x_66, 0, x_4);
return x_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_dec(x_66);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_dec(x_67);
lean_ctor_set(x_4, 0, x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_4);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_67);
lean_free_object(x_4);
x_75 = !lean_is_exclusive(x_66);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_66, 0);
lean_dec(x_76);
x_77 = lean_ctor_get(x_68, 0);
lean_inc(x_77);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_77);
return x_66;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
lean_dec(x_66);
x_79 = lean_ctor_get(x_68, 0);
lean_inc(x_79);
lean_dec(x_68);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_free_object(x_4);
x_81 = !lean_is_exclusive(x_66);
if (x_81 == 0)
{
return x_66;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_66, 0);
x_83 = lean_ctor_get(x_66, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_66);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; size_t x_89; size_t x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_4, 0);
lean_inc(x_85);
lean_dec(x_4);
x_86 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4___lam__0___boxed), 9, 0);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_5);
x_89 = lean_array_size(x_85);
x_90 = 0;
x_91 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4_spec__5(x_86, x_87, x_85, x_89, x_90, x_88, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_85);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_95 = x_91;
} else {
 lean_dec_ref(x_91);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_95;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_92);
x_99 = lean_ctor_get(x_91, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_100 = x_91;
} else {
 lean_dec_ref(x_91);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_93, 0);
lean_inc(x_101);
lean_dec(x_93);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_91, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_91, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_105 = x_91;
} else {
 lean_dec_ref(x_91);
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
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 0);
lean_dec(x_18);
x_19 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_17);
x_20 = lean_apply_9(x_1, x_19, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_6, 0, x_21);
lean_ctor_set(x_20, 0, x_6);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_6, 0, x_26);
lean_ctor_set(x_20, 0, x_6);
return x_20;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_29 = x_21;
} else {
 lean_dec_ref(x_21);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_29;
 lean_ctor_set_tag(x_30, 1);
}
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_6, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
lean_dec(x_17);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
lean_dec(x_21);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_2);
x_34 = 1;
x_35 = lean_usize_add(x_5, x_34);
x_5 = x_35;
x_13 = x_32;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_free_object(x_6);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
return x_20;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_20);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_6, 1);
lean_inc(x_41);
lean_dec(x_6);
x_42 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_41);
x_43 = lean_apply_9(x_1, x_42, x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
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
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_48 = x_44;
} else {
 lean_dec_ref(x_44);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_48;
 lean_ctor_set_tag(x_49, 1);
}
lean_ctor_set(x_49, 0, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
if (lean_is_scalar(x_46)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_46;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; 
lean_dec(x_41);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_ctor_get(x_44, 0);
lean_inc(x_53);
lean_dec(x_44);
lean_inc(x_2);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_2);
lean_ctor_set(x_54, 1, x_53);
x_55 = 1;
x_56 = lean_usize_add(x_5, x_55);
x_5 = x_56;
x_6 = x_54;
x_13 = x_52;
goto _start;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_41);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_43, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_43, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_60 = x_43;
} else {
 lean_dec_ref(x_43);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_2, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
lean_dec(x_2);
x_78 = lean_ctor_get(x_1, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 2);
lean_inc(x_79);
x_80 = l_Lean_Level_normLt(x_79, x_78);
if (x_80 == 0)
{
x_18 = x_76;
x_19 = x_78;
x_20 = x_79;
x_21 = x_77;
x_22 = x_9;
goto block_75;
}
else
{
x_18 = x_76;
x_19 = x_79;
x_20 = x_78;
x_21 = x_77;
x_22 = x_9;
goto block_75;
}
block_17:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_push(x_10, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
block_75:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; uint8_t x_42; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_20);
lean_inc(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_20);
x_26 = lean_array_get_size(x_24);
x_27 = l_Lean_Level_hash(x_19);
lean_dec(x_19);
x_28 = l_Lean_Level_hash(x_20);
lean_dec(x_20);
x_29 = lean_uint64_mix_hash(x_27, x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_24, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__0___redArg(x_25, x_41);
if (x_42 == 0)
{
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_44 = lean_ctor_get(x_18, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_18, 0);
lean_dec(x_45);
x_46 = lean_box(0);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_23, x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_25);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_49, 2, x_41);
x_50 = lean_array_uset(x_24, x_40, x_49);
x_51 = lean_unsigned_to_nat(4u);
x_52 = lean_nat_mul(x_48, x_51);
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_nat_div(x_52, x_53);
lean_dec(x_52);
x_55 = lean_array_get_size(x_50);
x_56 = lean_nat_dec_le(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1___redArg(x_50);
lean_ctor_set(x_18, 1, x_57);
lean_ctor_set(x_18, 0, x_48);
x_10 = x_21;
x_11 = x_22;
x_12 = x_18;
goto block_17;
}
else
{
lean_ctor_set(x_18, 1, x_50);
lean_ctor_set(x_18, 0, x_48);
x_10 = x_21;
x_11 = x_22;
x_12 = x_18;
goto block_17;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_18);
x_58 = lean_box(0);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_23, x_59);
lean_dec(x_23);
x_61 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_41);
x_62 = lean_array_uset(x_24, x_40, x_61);
x_63 = lean_unsigned_to_nat(4u);
x_64 = lean_nat_mul(x_60, x_63);
x_65 = lean_unsigned_to_nat(3u);
x_66 = lean_nat_div(x_64, x_65);
lean_dec(x_64);
x_67 = lean_array_get_size(x_62);
x_68 = lean_nat_dec_le(x_66, x_67);
lean_dec(x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__1___redArg(x_62);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_69);
x_10 = x_21;
x_11 = x_22;
x_12 = x_70;
goto block_17;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_60);
lean_ctor_set(x_71, 1, x_62);
x_10 = x_21;
x_11 = x_22;
x_12 = x_71;
goto block_17;
}
}
}
else
{
lean_dec(x_41);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_10 = x_21;
x_11 = x_22;
x_12 = x_18;
goto block_17;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_41);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_1);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_18);
lean_ctor_set(x_72, 1, x_21);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_22);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4(x_1, x_2, x_4, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4___lam__0___boxed), 9, 0);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_array_size(x_13);
x_28 = 0;
x_29 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__7(x_24, x_25, x_13, x_27, x_28, x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
lean_dec(x_13);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
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
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_29);
if (x_44 == 0)
{
return x_29;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_29, 0);
x_46 = lean_ctor_get(x_29, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_29);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_14);
if (x_48 == 0)
{
return x_14;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_14, 0);
x_50 = lean_ctor_get(x_14, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_14);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_nat_dec_lt(x_6, x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_inc(x_1);
x_18 = lean_array_get(x_1, x_2, x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_19 = l_Lean_Meta_mkLevelStuckErrorMessage(x_18, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_fget(x_2, x_6);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_11);
x_24 = l_Lean_logErrorAt___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__1(x_23, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
lean_inc(x_3);
{
lean_object* _tmp_4 = x_3;
lean_object* _tmp_5 = x_26;
lean_object* _tmp_12 = x_25;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_13 = _tmp_12;
}
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__0;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__6;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_Meta_getPostponed___redArg(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1;
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__7;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4(x_11, x_12, x_9, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_instInhabitedPostponedEntry;
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_array_get_size(x_18);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_20);
x_23 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_24 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__9___redArg(x_19, x_18, x_23, x_22, x_23, x_20, x_1, x_2, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_array_get(x_19, x_18, x_13);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_26);
x_27 = l_Lean_Meta_mkLevelStuckErrorMessage(x_26, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l_Lean_throwErrorAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__2___redArg(x_30, x_28, x_1, x_2, x_3, x_4, x_5, x_6, x_29);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_30);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_24;
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4_spec__5(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4_spec__7(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forIn___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_processPostponedUniverseConstraints(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_box(0);
x_9 = lean_box(1);
x_10 = lean_unbox(x_8);
x_11 = lean_unbox(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Meta_processPostponed(x_10, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(x_1, x_2, x_3, x_4, x_5, x_6, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
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
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = l_Lean_Name_quickCmp(x_1, x_5);
switch (x_8) {
case 0:
{
uint8_t x_9; 
x_9 = l_Lean_RBNode_isBlack___redArg(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_box(0);
x_11 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___redArg(x_1, x_4);
lean_ctor_set(x_2, 0, x_11);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_2);
x_13 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___redArg(x_1, x_4);
x_14 = l_Lean_RBNode_balLeft___redArg(x_13, x_5, x_6, x_7);
return x_14;
}
}
case 1:
{
lean_object* x_15; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
x_15 = l_Lean_RBNode_appendTrees___redArg(x_4, x_7);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = l_Lean_RBNode_isBlack___redArg(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_box(0);
x_18 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___redArg(x_1, x_7);
lean_ctor_set(x_2, 3, x_18);
x_19 = lean_unbox(x_17);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_19);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_2);
x_20 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___redArg(x_1, x_7);
x_21 = l_Lean_RBNode_balRight___redArg(x_4, x_5, x_6, x_20);
return x_21;
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_26 = l_Lean_Name_quickCmp(x_1, x_23);
switch (x_26) {
case 0:
{
uint8_t x_27; 
x_27 = l_Lean_RBNode_isBlack___redArg(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_box(0);
x_29 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___redArg(x_1, x_22);
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_25);
x_31 = lean_unbox(x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_31);
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___redArg(x_1, x_22);
x_33 = l_Lean_RBNode_balLeft___redArg(x_32, x_23, x_24, x_25);
return x_33;
}
}
case 1:
{
lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_23);
x_34 = l_Lean_RBNode_appendTrees___redArg(x_22, x_25);
return x_34;
}
default: 
{
uint8_t x_35; 
x_35 = l_Lean_RBNode_isBlack___redArg(x_25);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_box(0);
x_37 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___redArg(x_1, x_25);
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_22);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_unbox(x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_39);
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___redArg(x_1, x_25);
x_41 = l_Lean_RBNode_balRight___redArg(x_22, x_23, x_24, x_40);
return x_41;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___redArg(x_1, x_2);
x_4 = l_Lean_RBNode_setBlack___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0___redArg(x_1, x_8);
lean_ctor_set(x_5, 1, x_9);
x_10 = lean_st_ref_set(x_2, x_5, x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get(x_5, 3);
x_21 = lean_ctor_get(x_5, 4);
x_22 = lean_ctor_get(x_5, 5);
x_23 = lean_ctor_get(x_5, 6);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_24 = l_Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0___redArg(x_1, x_18);
x_25 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_21);
lean_ctor_set(x_25, 5, x_22);
lean_ctor_set(x_25, 6, x_23);
x_26 = lean_st_ref_set(x_2, x_25, x_6);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___redArg(x_1, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_erase___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_PostponeBehavior_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_PostponeBehavior_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_PostponeBehavior_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Elab_Term_PostponeBehavior_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_Term_PostponeBehavior_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_Elab_Term_instInhabitedPostponeBehavior() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__0____x40_Lean_Elab_SyntheticMVars___hyg_4157_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.PostponeBehavior.yes", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__1____x40_Lean_Elab_SyntheticMVars___hyg_4157_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reprPostponeBehavior___closed__0____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__2____x40_Lean_Elab_SyntheticMVars___hyg_4157_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.PostponeBehavior.no", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__3____x40_Lean_Elab_SyntheticMVars___hyg_4157_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reprPostponeBehavior___closed__2____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__4____x40_Lean_Elab_SyntheticMVars___hyg_4157_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.PostponeBehavior.partial", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__5____x40_Lean_Elab_SyntheticMVars___hyg_4157_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reprPostponeBehavior___closed__4____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__6____x40_Lean_Elab_SyntheticMVars___hyg_4157_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__7____x40_Lean_Elab_SyntheticMVars___hyg_4157_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4157_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_11; lean_object* x_19; 
switch (x_1) {
case 0:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(1024u);
x_28 = lean_nat_dec_le(x_27, x_2);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_Lean_Elab_Term_reprPostponeBehavior___closed__6____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
x_3 = x_29;
goto block_10;
}
else
{
lean_object* x_30; 
x_30 = l_Lean_Elab_Term_reprPostponeBehavior___closed__7____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
x_3 = x_30;
goto block_10;
}
}
case 1:
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(1024u);
x_32 = lean_nat_dec_le(x_31, x_2);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Lean_Elab_Term_reprPostponeBehavior___closed__6____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
x_11 = x_33;
goto block_18;
}
else
{
lean_object* x_34; 
x_34 = l_Lean_Elab_Term_reprPostponeBehavior___closed__7____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
x_11 = x_34;
goto block_18;
}
}
default: 
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_unsigned_to_nat(1024u);
x_36 = lean_nat_dec_le(x_35, x_2);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_Elab_Term_reprPostponeBehavior___closed__6____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
x_19 = x_37;
goto block_26;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_Elab_Term_reprPostponeBehavior___closed__7____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
x_19 = x_38;
goto block_26;
}
}
}
block_10:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = l_Lean_Elab_Term_reprPostponeBehavior___closed__1____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_8);
x_9 = l_Repr_addAppParen(x_7, x_2);
return x_9;
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = l_Lean_Elab_Term_reprPostponeBehavior___closed__3____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = l_Repr_addAppParen(x_15, x_2);
return x_17;
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = l_Lean_Elab_Term_reprPostponeBehavior___closed__5____x40_Lean_Elab_SyntheticMVars___hyg_4157_;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
x_25 = l_Repr_addAppParen(x_23, x_2);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4157____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4157_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_instReprPostponeBehavior___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4157____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_instReprPostponeBehavior() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instReprPostponeBehavior___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(uint8_t x_1, uint8_t x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_instBEqPostponeBehavior___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_instBEqPostponeBehavior() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instBEqPostponeBehavior___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_PostponeBehavior_ofBool(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
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
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not synthesize default value for parameter '", 50, 50);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' using tactics", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not synthesize default value for field '", 46, 46);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' of '", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__6;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__1;
x_14 = l_Lean_MessageData_ofName(x_12);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__3;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_logErrorAt___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__1(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
default: 
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__5;
x_23 = l_Lean_MessageData_ofName(x_20);
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_2, 0, x_22);
x_24 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__7;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_MessageData_ofName(x_21);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__3;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_logErrorAt___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__1(x_1, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_2);
x_33 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__5;
x_34 = l_Lean_MessageData_ofName(x_31);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__7;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_MessageData_ofName(x_32);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__3;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_logErrorAt___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__1(x_1, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_42;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_2(x_1, x_2, x_3);
x_12 = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
x_12 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover), 11, 2);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, x_2);
x_14 = l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery_spec__0___redArg(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___redArg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
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
x_25 = lean_ctor_get(x_7, 11);
x_26 = lean_ctor_get(x_7, 12);
x_27 = l_Lean_replaceRef(x_11, x_19);
lean_dec(x_19);
lean_dec(x_11);
x_28 = lean_nat_dec_eq(x_17, x_18);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_st_ref_get(x_4, x_12);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_ctor_get(x_31, 2);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_List_isEmpty___redArg(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_free_object(x_29);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_17, x_35);
lean_dec(x_17);
lean_ctor_set(x_7, 5, x_27);
lean_ctor_set(x_7, 3, x_36);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_37 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_28, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_105; uint8_t x_106; uint8_t x_107; 
x_41 = lean_ctor_get(x_37, 1);
x_42 = lean_ctor_get(x_37, 0);
lean_dec(x_42);
x_43 = lean_box(1);
x_44 = lean_box(x_28);
x_45 = lean_box(x_28);
x_46 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_46, 0, x_44);
lean_closure_set(x_46, 1, x_45);
x_105 = lean_box(0);
x_106 = lean_unbox(x_105);
x_107 = l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(x_1, x_106);
if (x_107 == 0)
{
lean_free_object(x_37);
goto block_104;
}
else
{
if (x_28 == 0)
{
lean_object* x_108; 
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_108 = lean_box(0);
lean_ctor_set(x_37, 0, x_108);
return x_37;
}
else
{
lean_free_object(x_37);
goto block_104;
}
}
block_104:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_box(x_28);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_48, 0, x_43);
lean_closure_set(x_48, 1, x_47);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_49 = l_Lean_Elab_Term_withoutPostponing___redArg(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_53 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(x_3, x_4, x_5, x_6, x_7, x_8, x_52);
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_57 = l_Lean_Elab_Term_withoutPostponing___redArg(x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_unbox(x_43);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_62 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_28, x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_62);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_62, 1);
x_67 = lean_ctor_get(x_62, 0);
lean_dec(x_67);
x_68 = lean_box(1);
x_69 = lean_unbox(x_68);
x_70 = l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(x_1, x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = lean_box(0);
lean_ctor_set(x_62, 0, x_71);
return x_62;
}
else
{
lean_object* x_72; 
lean_free_object(x_62);
x_72 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_66);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
lean_dec(x_62);
x_74 = lean_box(1);
x_75 = lean_unbox(x_74);
x_76 = l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(x_1, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_73);
return x_78;
}
else
{
lean_object* x_79; 
x_79 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
return x_79;
}
}
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_62, 1);
lean_inc(x_80);
lean_dec(x_62);
x_9 = x_80;
goto _start;
}
}
else
{
uint8_t x_82; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_62);
if (x_82 == 0)
{
return x_62;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_62, 0);
x_84 = lean_ctor_get(x_62, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_62);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_57, 1);
lean_inc(x_86);
lean_dec(x_57);
x_9 = x_86;
goto _start;
}
}
else
{
uint8_t x_88; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_88 = !lean_is_exclusive(x_57);
if (x_88 == 0)
{
return x_57;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_57, 0);
x_90 = lean_ctor_get(x_57, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_57);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; 
lean_dec(x_46);
x_92 = lean_ctor_get(x_53, 1);
lean_inc(x_92);
lean_dec(x_53);
x_9 = x_92;
goto _start;
}
}
else
{
uint8_t x_94; 
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_94 = !lean_is_exclusive(x_53);
if (x_94 == 0)
{
return x_53;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_53, 0);
x_96 = lean_ctor_get(x_53, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_53);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; 
lean_dec(x_46);
x_98 = lean_ctor_get(x_49, 1);
lean_inc(x_98);
lean_dec(x_49);
x_9 = x_98;
goto _start;
}
}
else
{
uint8_t x_100; 
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_49);
if (x_100 == 0)
{
return x_49;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_49, 0);
x_102 = lean_ctor_get(x_49, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_49);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_165; uint8_t x_166; uint8_t x_167; 
x_109 = lean_ctor_get(x_37, 1);
lean_inc(x_109);
lean_dec(x_37);
x_110 = lean_box(1);
x_111 = lean_box(x_28);
x_112 = lean_box(x_28);
x_113 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_113, 0, x_111);
lean_closure_set(x_113, 1, x_112);
x_165 = lean_box(0);
x_166 = lean_unbox(x_165);
x_167 = l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(x_1, x_166);
if (x_167 == 0)
{
goto block_164;
}
else
{
if (x_28 == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_113);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_168 = lean_box(0);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_109);
return x_169;
}
else
{
goto block_164;
}
}
block_164:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_box(x_28);
x_115 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_115, 0, x_110);
lean_closure_set(x_115, 1, x_114);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_116 = l_Lean_Elab_Term_withoutPostponing___redArg(x_115, x_3, x_4, x_5, x_6, x_7, x_8, x_109);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec(x_116);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_120 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(x_3, x_4, x_5, x_6, x_7, x_8, x_119);
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_124 = l_Lean_Elab_Term_withoutPostponing___redArg(x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_unbox(x_110);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_129 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_28, x_128, x_3, x_4, x_5, x_6, x_7, x_8, x_127);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_133 = x_129;
} else {
 lean_dec_ref(x_129);
 x_133 = lean_box(0);
}
x_134 = lean_box(1);
x_135 = lean_unbox(x_134);
x_136 = l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(x_1, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_137 = lean_box(0);
if (lean_is_scalar(x_133)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_133;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_132);
return x_138;
}
else
{
lean_object* x_139; 
lean_dec(x_133);
x_139 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_132);
return x_139;
}
}
else
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_129, 1);
lean_inc(x_140);
lean_dec(x_129);
x_9 = x_140;
goto _start;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_142 = lean_ctor_get(x_129, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_129, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_144 = x_129;
} else {
 lean_dec_ref(x_129);
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
lean_object* x_146; 
x_146 = lean_ctor_get(x_124, 1);
lean_inc(x_146);
lean_dec(x_124);
x_9 = x_146;
goto _start;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_148 = lean_ctor_get(x_124, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_124, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_150 = x_124;
} else {
 lean_dec_ref(x_124);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
else
{
lean_object* x_152; 
lean_dec(x_113);
x_152 = lean_ctor_get(x_120, 1);
lean_inc(x_152);
lean_dec(x_120);
x_9 = x_152;
goto _start;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_113);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_154 = lean_ctor_get(x_120, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_120, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_156 = x_120;
} else {
 lean_dec_ref(x_120);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
else
{
lean_object* x_158; 
lean_dec(x_113);
x_158 = lean_ctor_get(x_116, 1);
lean_inc(x_158);
lean_dec(x_116);
x_9 = x_158;
goto _start;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_113);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_160 = lean_ctor_get(x_116, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_116, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_162 = x_116;
} else {
 lean_dec_ref(x_116);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
}
}
else
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_37, 1);
lean_inc(x_170);
lean_dec(x_37);
x_9 = x_170;
goto _start;
}
}
else
{
uint8_t x_172; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_172 = !lean_is_exclusive(x_37);
if (x_172 == 0)
{
return x_37;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_37, 0);
x_174 = lean_ctor_get(x_37, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_37);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
lean_object* x_176; 
lean_dec(x_27);
lean_free_object(x_7);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_176 = lean_box(0);
lean_ctor_set(x_29, 0, x_176);
return x_29;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_177 = lean_ctor_get(x_29, 0);
x_178 = lean_ctor_get(x_29, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_29);
x_179 = lean_ctor_get(x_177, 2);
lean_inc(x_179);
lean_dec(x_177);
x_180 = l_List_isEmpty___redArg(x_179);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_unsigned_to_nat(1u);
x_182 = lean_nat_add(x_17, x_181);
lean_dec(x_17);
lean_ctor_set(x_7, 5, x_27);
lean_ctor_set(x_7, 3, x_182);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_183 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_28, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_178);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; uint8_t x_185; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_unbox(x_184);
lean_dec(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_243; uint8_t x_244; uint8_t x_245; 
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_187 = x_183;
} else {
 lean_dec_ref(x_183);
 x_187 = lean_box(0);
}
x_188 = lean_box(1);
x_189 = lean_box(x_28);
x_190 = lean_box(x_28);
x_191 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_191, 0, x_189);
lean_closure_set(x_191, 1, x_190);
x_243 = lean_box(0);
x_244 = lean_unbox(x_243);
x_245 = l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(x_1, x_244);
if (x_245 == 0)
{
lean_dec(x_187);
goto block_242;
}
else
{
if (x_28 == 0)
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_191);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_246 = lean_box(0);
if (lean_is_scalar(x_187)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_187;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_186);
return x_247;
}
else
{
lean_dec(x_187);
goto block_242;
}
}
block_242:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_box(x_28);
x_193 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_193, 0, x_188);
lean_closure_set(x_193, 1, x_192);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_194 = l_Lean_Elab_Term_withoutPostponing___redArg(x_193, x_3, x_4, x_5, x_6, x_7, x_8, x_186);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; uint8_t x_196; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_unbox(x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
lean_dec(x_194);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_198 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(x_3, x_4, x_5, x_6, x_7, x_8, x_197);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; uint8_t x_200; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_unbox(x_199);
lean_dec(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec(x_198);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_202 = l_Lean_Elab_Term_withoutPostponing___redArg(x_191, x_3, x_4, x_5, x_6, x_7, x_8, x_201);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_unbox(x_203);
lean_dec(x_203);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
x_206 = lean_unbox(x_188);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_207 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_28, x_206, x_3, x_4, x_5, x_6, x_7, x_8, x_205);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_unbox(x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; uint8_t x_214; 
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_211 = x_207;
} else {
 lean_dec_ref(x_207);
 x_211 = lean_box(0);
}
x_212 = lean_box(1);
x_213 = lean_unbox(x_212);
x_214 = l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(x_1, x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_215 = lean_box(0);
if (lean_is_scalar(x_211)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_211;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_210);
return x_216;
}
else
{
lean_object* x_217; 
lean_dec(x_211);
x_217 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_210);
return x_217;
}
}
else
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_207, 1);
lean_inc(x_218);
lean_dec(x_207);
x_9 = x_218;
goto _start;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_220 = lean_ctor_get(x_207, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_207, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_222 = x_207;
} else {
 lean_dec_ref(x_207);
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
lean_object* x_224; 
x_224 = lean_ctor_get(x_202, 1);
lean_inc(x_224);
lean_dec(x_202);
x_9 = x_224;
goto _start;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_226 = lean_ctor_get(x_202, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_202, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_228 = x_202;
} else {
 lean_dec_ref(x_202);
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
lean_object* x_230; 
lean_dec(x_191);
x_230 = lean_ctor_get(x_198, 1);
lean_inc(x_230);
lean_dec(x_198);
x_9 = x_230;
goto _start;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_191);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_232 = lean_ctor_get(x_198, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_198, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_234 = x_198;
} else {
 lean_dec_ref(x_198);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
else
{
lean_object* x_236; 
lean_dec(x_191);
x_236 = lean_ctor_get(x_194, 1);
lean_inc(x_236);
lean_dec(x_194);
x_9 = x_236;
goto _start;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_191);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_238 = lean_ctor_get(x_194, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_194, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_240 = x_194;
} else {
 lean_dec_ref(x_194);
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
}
else
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_183, 1);
lean_inc(x_248);
lean_dec(x_183);
x_9 = x_248;
goto _start;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_250 = lean_ctor_get(x_183, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_183, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_252 = x_183;
} else {
 lean_dec_ref(x_183);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_27);
lean_free_object(x_7);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_254 = lean_box(0);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_178);
return x_255;
}
}
}
else
{
lean_object* x_256; 
lean_free_object(x_7);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_256 = l_Lean_throwMaxRecDepthAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__3___redArg(x_27, x_12);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_257 = lean_ctor_get(x_7, 0);
x_258 = lean_ctor_get(x_7, 1);
x_259 = lean_ctor_get(x_7, 2);
x_260 = lean_ctor_get(x_7, 3);
x_261 = lean_ctor_get(x_7, 4);
x_262 = lean_ctor_get(x_7, 5);
x_263 = lean_ctor_get(x_7, 6);
x_264 = lean_ctor_get(x_7, 7);
x_265 = lean_ctor_get(x_7, 8);
x_266 = lean_ctor_get(x_7, 9);
x_267 = lean_ctor_get(x_7, 10);
x_268 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_269 = lean_ctor_get(x_7, 11);
x_270 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_271 = lean_ctor_get(x_7, 12);
lean_inc(x_271);
lean_inc(x_269);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_7);
x_272 = l_Lean_replaceRef(x_11, x_262);
lean_dec(x_262);
lean_dec(x_11);
x_273 = lean_nat_dec_eq(x_260, x_261);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_274 = lean_st_ref_get(x_4, x_12);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_277 = x_274;
} else {
 lean_dec_ref(x_274);
 x_277 = lean_box(0);
}
x_278 = lean_ctor_get(x_275, 2);
lean_inc(x_278);
lean_dec(x_275);
x_279 = l_List_isEmpty___redArg(x_278);
lean_dec(x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_277);
x_280 = lean_unsigned_to_nat(1u);
x_281 = lean_nat_add(x_260, x_280);
lean_dec(x_260);
x_282 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_282, 0, x_257);
lean_ctor_set(x_282, 1, x_258);
lean_ctor_set(x_282, 2, x_259);
lean_ctor_set(x_282, 3, x_281);
lean_ctor_set(x_282, 4, x_261);
lean_ctor_set(x_282, 5, x_272);
lean_ctor_set(x_282, 6, x_263);
lean_ctor_set(x_282, 7, x_264);
lean_ctor_set(x_282, 8, x_265);
lean_ctor_set(x_282, 9, x_266);
lean_ctor_set(x_282, 10, x_267);
lean_ctor_set(x_282, 11, x_269);
lean_ctor_set(x_282, 12, x_271);
lean_ctor_set_uint8(x_282, sizeof(void*)*13, x_268);
lean_ctor_set_uint8(x_282, sizeof(void*)*13 + 1, x_270);
lean_inc(x_8);
lean_inc(x_282);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_283 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_273, x_273, x_3, x_4, x_5, x_6, x_282, x_8, x_276);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; uint8_t x_285; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_unbox(x_284);
lean_dec(x_284);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_343; uint8_t x_344; uint8_t x_345; 
x_286 = lean_ctor_get(x_283, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_287 = x_283;
} else {
 lean_dec_ref(x_283);
 x_287 = lean_box(0);
}
x_288 = lean_box(1);
x_289 = lean_box(x_273);
x_290 = lean_box(x_273);
x_291 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_291, 0, x_289);
lean_closure_set(x_291, 1, x_290);
x_343 = lean_box(0);
x_344 = lean_unbox(x_343);
x_345 = l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(x_1, x_344);
if (x_345 == 0)
{
lean_dec(x_287);
goto block_342;
}
else
{
if (x_273 == 0)
{
lean_object* x_346; lean_object* x_347; 
lean_dec(x_291);
lean_dec(x_282);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_346 = lean_box(0);
if (lean_is_scalar(x_287)) {
 x_347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_347 = x_287;
}
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_286);
return x_347;
}
else
{
lean_dec(x_287);
goto block_342;
}
}
block_342:
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_box(x_273);
x_293 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_293, 0, x_288);
lean_closure_set(x_293, 1, x_292);
lean_inc(x_8);
lean_inc(x_282);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_294 = l_Lean_Elab_Term_withoutPostponing___redArg(x_293, x_3, x_4, x_5, x_6, x_282, x_8, x_286);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; uint8_t x_296; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_unbox(x_295);
lean_dec(x_295);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_294, 1);
lean_inc(x_297);
lean_dec(x_294);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_298 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(x_3, x_4, x_5, x_6, x_282, x_8, x_297);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; uint8_t x_300; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_unbox(x_299);
lean_dec(x_299);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
lean_inc(x_8);
lean_inc(x_282);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_302 = l_Lean_Elab_Term_withoutPostponing___redArg(x_291, x_3, x_4, x_5, x_6, x_282, x_8, x_301);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; uint8_t x_304; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_unbox(x_303);
lean_dec(x_303);
if (x_304 == 0)
{
lean_object* x_305; uint8_t x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_302, 1);
lean_inc(x_305);
lean_dec(x_302);
x_306 = lean_unbox(x_288);
lean_inc(x_8);
lean_inc(x_282);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_307 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_273, x_306, x_3, x_4, x_5, x_6, x_282, x_8, x_305);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; uint8_t x_309; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_unbox(x_308);
lean_dec(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; uint8_t x_314; 
x_310 = lean_ctor_get(x_307, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_311 = x_307;
} else {
 lean_dec_ref(x_307);
 x_311 = lean_box(0);
}
x_312 = lean_box(1);
x_313 = lean_unbox(x_312);
x_314 = l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(x_1, x_313);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; 
lean_dec(x_282);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_315 = lean_box(0);
if (lean_is_scalar(x_311)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_311;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_310);
return x_316;
}
else
{
lean_object* x_317; 
lean_dec(x_311);
x_317 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_2, x_3, x_4, x_5, x_6, x_282, x_8, x_310);
return x_317;
}
}
else
{
lean_object* x_318; 
x_318 = lean_ctor_get(x_307, 1);
lean_inc(x_318);
lean_dec(x_307);
x_7 = x_282;
x_9 = x_318;
goto _start;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_282);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_320 = lean_ctor_get(x_307, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_307, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_322 = x_307;
} else {
 lean_dec_ref(x_307);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
return x_323;
}
}
else
{
lean_object* x_324; 
x_324 = lean_ctor_get(x_302, 1);
lean_inc(x_324);
lean_dec(x_302);
x_7 = x_282;
x_9 = x_324;
goto _start;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_282);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_326 = lean_ctor_get(x_302, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_302, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_328 = x_302;
} else {
 lean_dec_ref(x_302);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_327);
return x_329;
}
}
else
{
lean_object* x_330; 
lean_dec(x_291);
x_330 = lean_ctor_get(x_298, 1);
lean_inc(x_330);
lean_dec(x_298);
x_7 = x_282;
x_9 = x_330;
goto _start;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_291);
lean_dec(x_282);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_332 = lean_ctor_get(x_298, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_298, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_334 = x_298;
} else {
 lean_dec_ref(x_298);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 2, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_332);
lean_ctor_set(x_335, 1, x_333);
return x_335;
}
}
else
{
lean_object* x_336; 
lean_dec(x_291);
x_336 = lean_ctor_get(x_294, 1);
lean_inc(x_336);
lean_dec(x_294);
x_7 = x_282;
x_9 = x_336;
goto _start;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_291);
lean_dec(x_282);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_338 = lean_ctor_get(x_294, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_294, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_340 = x_294;
} else {
 lean_dec_ref(x_294);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 2, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_339);
return x_341;
}
}
}
else
{
lean_object* x_348; 
x_348 = lean_ctor_get(x_283, 1);
lean_inc(x_348);
lean_dec(x_283);
x_7 = x_282;
x_9 = x_348;
goto _start;
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_282);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_350 = lean_ctor_get(x_283, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_283, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_352 = x_283;
} else {
 lean_dec_ref(x_283);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; 
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_354 = lean_box(0);
if (lean_is_scalar(x_277)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_277;
}
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_276);
return x_355;
}
}
else
{
lean_object* x_356; 
lean_dec(x_271);
lean_dec(x_269);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_356 = l_Lean_throwMaxRecDepthAt___at___Lean_Elab_liftMacroM___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux_spec__0_spec__3___redArg(x_272, x_12);
return x_356;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("postpone", 8, 8);
return x_1;
}
}
static lean_object* _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not ready yet", 13, 13);
return x_1;
}
}
static lean_object* _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succeeded", 9, 9);
return x_1;
}
}
static lean_object* _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__5;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resuming ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_21; uint8_t x_32; lean_object* x_33; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_63; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_16 = x_4;
} else {
 lean_dec_ref(x_4);
 x_16 = lean_box(0);
}
x_36 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__0;
lean_inc(x_1);
x_37 = l_Lean_Name_mkStr2(x_1, x_36);
lean_inc(x_37);
x_74 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_37, x_10, x_12);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_63 = x_77;
goto block_73;
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_74);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_74, 1);
x_80 = lean_ctor_get(x_74, 0);
lean_dec(x_80);
x_81 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__8;
lean_inc(x_14);
x_82 = l_Lean_Expr_mvar___override(x_14);
x_83 = l_Lean_MessageData_ofExpr(x_82);
lean_ctor_set_tag(x_74, 7);
lean_ctor_set(x_74, 1, x_83);
lean_ctor_set(x_74, 0, x_81);
x_84 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_74);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_closure((void*)(l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___lam__0___boxed), 8, 1);
lean_closure_set(x_86, 0, x_85);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_87 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_14, x_86, x_6, x_7, x_8, x_9, x_10, x_11, x_79);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_37);
x_90 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_37, x_88, x_8, x_9, x_10, x_11, x_89);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_63 = x_91;
goto block_73;
}
else
{
uint8_t x_92; 
lean_dec(x_37);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
return x_87;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_87, 0);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_87);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_96 = lean_ctor_get(x_74, 1);
lean_inc(x_96);
lean_dec(x_74);
x_97 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__8;
lean_inc(x_14);
x_98 = l_Lean_Expr_mvar___override(x_14);
x_99 = l_Lean_MessageData_ofExpr(x_98);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
x_101 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10;
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_closure((void*)(l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___lam__0___boxed), 8, 1);
lean_closure_set(x_103, 0, x_102);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_104 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_14, x_103, x_6, x_7, x_8, x_9, x_10, x_11, x_96);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_37);
x_107 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_37, x_105, x_8, x_9, x_10, x_11, x_106);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_63 = x_108;
goto block_73;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_37);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_109 = lean_ctor_get(x_104, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_104, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_111 = x_104;
} else {
 lean_dec_ref(x_104);
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
block_20:
{
lean_object* x_18; 
if (lean_is_scalar(x_16)) {
 x_18 = lean_alloc_ctor(1, 2, 0);
} else {
 x_18 = x_16;
}
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_5);
x_4 = x_15;
x_5 = x_18;
x_12 = x_17;
goto _start;
}
block_31:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_14);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_4 = x_15;
x_12 = x_24;
goto _start;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_17 = x_26;
goto block_20;
}
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
block_35:
{
if (x_32 == 0)
{
x_17 = x_33;
goto block_20;
}
else
{
lean_dec(x_16);
lean_dec(x_14);
x_4 = x_15;
x_12 = x_33;
goto _start;
}
}
block_47:
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_37, x_44, x_39, x_41, x_42, x_43, x_40);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_39);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_32 = x_38;
x_33 = x_46;
goto block_35;
}
block_62:
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_inc(x_37);
x_54 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_37, x_51, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_37);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_32 = x_48;
x_33 = x_57;
goto block_35;
}
else
{
if (x_48 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__3;
x_38 = x_48;
x_39 = x_49;
x_40 = x_58;
x_41 = x_50;
x_42 = x_51;
x_43 = x_52;
x_44 = x_59;
goto block_47;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_61 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__6;
x_38 = x_48;
x_39 = x_49;
x_40 = x_60;
x_41 = x_50;
x_42 = x_51;
x_43 = x_52;
x_44 = x_61;
goto block_47;
}
}
}
block_73:
{
lean_object* x_64; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_64 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar(x_14, x_2, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_unbox(x_65);
lean_dec(x_65);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_48 = x_68;
x_49 = x_8;
x_50 = x_9;
x_51 = x_10;
x_52 = x_11;
x_53 = x_67;
goto block_62;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___redArg(x_14, x_7, x_69);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_unbox(x_65);
lean_dec(x_65);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_48 = x_72;
x_49 = x_8;
x_50 = x_9;
x_51 = x_10;
x_52 = x_11;
x_53 = x_71;
goto block_62;
}
}
else
{
lean_dec(x_37);
x_21 = x_64;
goto block_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_21; uint8_t x_32; lean_object* x_33; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_63; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_16 = x_4;
} else {
 lean_dec_ref(x_4);
 x_16 = lean_box(0);
}
x_36 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__0;
lean_inc(x_1);
x_37 = l_Lean_Name_mkStr2(x_1, x_36);
lean_inc(x_37);
x_74 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_37, x_10, x_12);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_63 = x_77;
goto block_73;
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_74);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_74, 1);
x_80 = lean_ctor_get(x_74, 0);
lean_dec(x_80);
x_81 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__8;
lean_inc(x_14);
x_82 = l_Lean_Expr_mvar___override(x_14);
x_83 = l_Lean_MessageData_ofExpr(x_82);
lean_ctor_set_tag(x_74, 7);
lean_ctor_set(x_74, 1, x_83);
lean_ctor_set(x_74, 0, x_81);
x_84 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_74);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_closure((void*)(l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___lam__0___boxed), 8, 1);
lean_closure_set(x_86, 0, x_85);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_87 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_14, x_86, x_6, x_7, x_8, x_9, x_10, x_11, x_79);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_37);
x_90 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_37, x_88, x_8, x_9, x_10, x_11, x_89);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_63 = x_91;
goto block_73;
}
else
{
uint8_t x_92; 
lean_dec(x_37);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
return x_87;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_87, 0);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_87);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_96 = lean_ctor_get(x_74, 1);
lean_inc(x_96);
lean_dec(x_74);
x_97 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__8;
lean_inc(x_14);
x_98 = l_Lean_Expr_mvar___override(x_14);
x_99 = l_Lean_MessageData_ofExpr(x_98);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
x_101 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10;
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_closure((void*)(l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___lam__0___boxed), 8, 1);
lean_closure_set(x_103, 0, x_102);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_104 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_14, x_103, x_6, x_7, x_8, x_9, x_10, x_11, x_96);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_37);
x_107 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_37, x_105, x_8, x_9, x_10, x_11, x_106);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_63 = x_108;
goto block_73;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_37);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_109 = lean_ctor_get(x_104, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_104, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_111 = x_104;
} else {
 lean_dec_ref(x_104);
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
block_20:
{
lean_object* x_18; lean_object* x_19; 
if (lean_is_scalar(x_16)) {
 x_18 = lean_alloc_ctor(1, 2, 0);
} else {
 x_18 = x_16;
}
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_5);
x_19 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0(x_1, x_2, x_3, x_15, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
return x_19;
}
block_31:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_14);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_17 = x_26;
goto block_20;
}
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
block_35:
{
if (x_32 == 0)
{
x_17 = x_33;
goto block_20;
}
else
{
lean_object* x_34; 
lean_dec(x_16);
lean_dec(x_14);
x_34 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_33);
return x_34;
}
}
block_47:
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_37, x_44, x_43, x_39, x_38, x_42, x_41);
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_39);
lean_dec(x_43);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_32 = x_40;
x_33 = x_46;
goto block_35;
}
block_62:
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_inc(x_37);
x_54 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_37, x_51, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_37);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_32 = x_48;
x_33 = x_57;
goto block_35;
}
else
{
if (x_48 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__3;
x_38 = x_51;
x_39 = x_50;
x_40 = x_48;
x_41 = x_58;
x_42 = x_52;
x_43 = x_49;
x_44 = x_59;
goto block_47;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_61 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__6;
x_38 = x_51;
x_39 = x_50;
x_40 = x_48;
x_41 = x_60;
x_42 = x_52;
x_43 = x_49;
x_44 = x_61;
goto block_47;
}
}
}
block_73:
{
lean_object* x_64; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_64 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar(x_14, x_2, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_unbox(x_65);
lean_dec(x_65);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_48 = x_68;
x_49 = x_8;
x_50 = x_9;
x_51 = x_10;
x_52 = x_11;
x_53 = x_67;
goto block_62;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___redArg(x_14, x_7, x_69);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_unbox(x_65);
lean_dec(x_65);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_48 = x_72;
x_49 = x_8;
x_50 = x_9;
x_51 = x_10;
x_52 = x_11;
x_53 = x_71;
goto block_62;
}
}
else
{
lean_dec(x_37);
x_21 = x_64;
goto block_31;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resuming synthetic metavariables, mayPostpone: ", 47, 47);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", postponeOnError: ", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__1;
if (x_12 == 0)
{
lean_object* x_23; 
x_23 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__4;
x_14 = x_23;
goto block_22;
}
else
{
lean_object* x_24; 
x_24 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__5;
x_14 = x_24;
goto block_22;
}
block_11:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_MessageData_ofFormat(x_6);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__3;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
if (x_2 == 0)
{
lean_object* x_20; 
x_20 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__4;
x_4 = x_19;
x_5 = x_20;
goto block_11;
}
else
{
lean_object* x_21; 
x_21 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__5;
x_4 = x_19;
x_5 = x_21;
goto block_11;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resuming", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__0;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_10 = lean_box(x_1);
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___boxed), 3, 2);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_10);
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__0;
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1;
lean_inc(x_7);
x_14 = l_Lean_Elab_Term_traceAtCmdPos(x_13, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_4, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_take(x_4, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_20, 2);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 2, x_24);
x_25 = lean_st_ref_set(x_4, x_20, x_21);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_17, 2);
lean_inc(x_27);
lean_dec(x_17);
lean_inc(x_27);
x_28 = l_List_reverse___redArg(x_27);
lean_inc(x_4);
x_29 = l_List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0(x_12, x_1, x_2, x_28, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_take(x_4, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_33, 2);
lean_inc(x_30);
x_37 = l_List_appendTR___redArg(x_36, x_30);
lean_ctor_set(x_33, 2, x_37);
x_38 = lean_st_ref_set(x_4, x_33, x_34);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = l_List_lengthTR___redArg(x_27);
lean_dec(x_27);
x_42 = l_List_lengthTR___redArg(x_30);
lean_dec(x_30);
x_43 = lean_nat_dec_eq(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_box(1);
lean_ctor_set(x_38, 0, x_44);
return x_38;
}
else
{
lean_object* x_45; 
x_45 = lean_box(0);
lean_ctor_set(x_38, 0, x_45);
return x_38;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_dec(x_38);
x_47 = l_List_lengthTR___redArg(x_27);
lean_dec(x_27);
x_48 = l_List_lengthTR___redArg(x_30);
lean_dec(x_30);
x_49 = lean_nat_dec_eq(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_54 = lean_ctor_get(x_33, 0);
x_55 = lean_ctor_get(x_33, 1);
x_56 = lean_ctor_get(x_33, 2);
x_57 = lean_ctor_get(x_33, 3);
x_58 = lean_ctor_get(x_33, 4);
x_59 = lean_ctor_get(x_33, 5);
x_60 = lean_ctor_get(x_33, 6);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_33);
lean_inc(x_30);
x_61 = l_List_appendTR___redArg(x_56, x_30);
x_62 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_62, 0, x_54);
lean_ctor_set(x_62, 1, x_55);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_57);
lean_ctor_set(x_62, 4, x_58);
lean_ctor_set(x_62, 5, x_59);
lean_ctor_set(x_62, 6, x_60);
x_63 = lean_st_ref_set(x_4, x_62, x_34);
lean_dec(x_4);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = l_List_lengthTR___redArg(x_27);
lean_dec(x_27);
x_67 = l_List_lengthTR___redArg(x_30);
lean_dec(x_30);
x_68 = lean_nat_dec_eq(x_66, x_67);
lean_dec(x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_box(1);
if (lean_is_scalar(x_65)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_65;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_64);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_box(0);
if (lean_is_scalar(x_65)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_65;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_64);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_27);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_29);
if (x_73 == 0)
{
return x_29;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_29, 0);
x_75 = lean_ctor_get(x_29, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_29);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_77 = lean_ctor_get(x_20, 0);
x_78 = lean_ctor_get(x_20, 1);
x_79 = lean_ctor_get(x_20, 3);
x_80 = lean_ctor_get(x_20, 4);
x_81 = lean_ctor_get(x_20, 5);
x_82 = lean_ctor_get(x_20, 6);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_20);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_78);
lean_ctor_set(x_84, 2, x_83);
lean_ctor_set(x_84, 3, x_79);
lean_ctor_set(x_84, 4, x_80);
lean_ctor_set(x_84, 5, x_81);
lean_ctor_set(x_84, 6, x_82);
x_85 = lean_st_ref_set(x_4, x_84, x_21);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_ctor_get(x_17, 2);
lean_inc(x_87);
lean_dec(x_17);
lean_inc(x_87);
x_88 = l_List_reverse___redArg(x_87);
lean_inc(x_4);
x_89 = l_List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0(x_12, x_1, x_2, x_88, x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_86);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_st_ref_take(x_4, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_93, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_93, 3);
lean_inc(x_98);
x_99 = lean_ctor_get(x_93, 4);
lean_inc(x_99);
x_100 = lean_ctor_get(x_93, 5);
lean_inc(x_100);
x_101 = lean_ctor_get(x_93, 6);
lean_inc(x_101);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 lean_ctor_release(x_93, 2);
 lean_ctor_release(x_93, 3);
 lean_ctor_release(x_93, 4);
 lean_ctor_release(x_93, 5);
 lean_ctor_release(x_93, 6);
 x_102 = x_93;
} else {
 lean_dec_ref(x_93);
 x_102 = lean_box(0);
}
lean_inc(x_90);
x_103 = l_List_appendTR___redArg(x_97, x_90);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 7, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_95);
lean_ctor_set(x_104, 1, x_96);
lean_ctor_set(x_104, 2, x_103);
lean_ctor_set(x_104, 3, x_98);
lean_ctor_set(x_104, 4, x_99);
lean_ctor_set(x_104, 5, x_100);
lean_ctor_set(x_104, 6, x_101);
x_105 = lean_st_ref_set(x_4, x_104, x_94);
lean_dec(x_4);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
x_108 = l_List_lengthTR___redArg(x_87);
lean_dec(x_87);
x_109 = l_List_lengthTR___redArg(x_90);
lean_dec(x_90);
x_110 = lean_nat_dec_eq(x_108, x_109);
lean_dec(x_109);
lean_dec(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_box(1);
if (lean_is_scalar(x_107)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_107;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_106);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_box(0);
if (lean_is_scalar(x_107)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_107;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_106);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_87);
lean_dec(x_4);
x_115 = lean_ctor_get(x_89, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_89, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_117 = x_89;
} else {
 lean_dec_ref(x_89);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_instantiate_expr_mvars(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_2, x_6);
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
lean_ctor_set(x_12, 0, x_9);
x_16 = lean_st_ref_set(x_2, x_12, x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_10);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_12, 1);
x_22 = lean_ctor_get(x_12, 2);
x_23 = lean_ctor_get(x_12, 3);
x_24 = lean_ctor_get(x_12, 4);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
x_26 = lean_st_ref_set(x_2, x_25, x_13);
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
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateExprMVars___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_spec__0___redArg(x_1, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_43; uint64_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_43 = lean_ctor_get(x_7, 0);
lean_inc(x_43);
x_44 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_45 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_7, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_7, 4);
lean_inc(x_49);
x_50 = lean_ctor_get(x_7, 5);
lean_inc(x_50);
x_51 = lean_ctor_get(x_7, 6);
lean_inc(x_51);
x_52 = !lean_is_exclusive(x_43);
if (x_52 == 0)
{
uint8_t x_53; uint8_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_54 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
lean_ctor_set_uint8(x_43, 9, x_1);
x_55 = 2;
x_56 = lean_uint64_shift_right(x_44, x_55);
x_57 = lean_uint64_shift_left(x_56, x_55);
x_58 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_59 = lean_uint64_lor(x_57, x_58);
x_60 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_60, 0, x_43);
lean_ctor_set(x_60, 1, x_46);
lean_ctor_set(x_60, 2, x_47);
lean_ctor_set(x_60, 3, x_48);
lean_ctor_set(x_60, 4, x_49);
lean_ctor_set(x_60, 5, x_50);
lean_ctor_set(x_60, 6, x_51);
lean_ctor_set_uint64(x_60, sizeof(void*)*7, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*7 + 8, x_45);
lean_ctor_set_uint8(x_60, sizeof(void*)*7 + 9, x_53);
lean_ctor_set_uint8(x_60, sizeof(void*)*7 + 10, x_54);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_60);
lean_inc(x_2);
x_61 = lean_infer_type(x_2, x_60, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_64 = l_Lean_Meta_isExprDefEq(x_62, x_3, x_60, x_8, x_9, x_10, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_67;
goto block_42;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
lean_inc(x_2);
x_69 = l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0(x_4, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_unbox(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_70);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_72;
goto block_42;
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_74 = l_Lean_MVarId_assign___at___Lean_Elab_Term_exprToSyntax_spec__0___redArg(x_4, x_2, x_8, x_73);
lean_dec(x_8);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
lean_ctor_set(x_74, 0, x_70);
return x_74;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_64;
}
}
else
{
uint8_t x_79; 
lean_dec(x_60);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_61);
if (x_79 == 0)
{
return x_61;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_61, 0);
x_81 = lean_ctor_get(x_61, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_61);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; lean_object* x_108; lean_object* x_109; 
x_83 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_84 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
x_85 = lean_ctor_get_uint8(x_43, 0);
x_86 = lean_ctor_get_uint8(x_43, 1);
x_87 = lean_ctor_get_uint8(x_43, 2);
x_88 = lean_ctor_get_uint8(x_43, 3);
x_89 = lean_ctor_get_uint8(x_43, 4);
x_90 = lean_ctor_get_uint8(x_43, 5);
x_91 = lean_ctor_get_uint8(x_43, 6);
x_92 = lean_ctor_get_uint8(x_43, 7);
x_93 = lean_ctor_get_uint8(x_43, 8);
x_94 = lean_ctor_get_uint8(x_43, 10);
x_95 = lean_ctor_get_uint8(x_43, 11);
x_96 = lean_ctor_get_uint8(x_43, 12);
x_97 = lean_ctor_get_uint8(x_43, 13);
x_98 = lean_ctor_get_uint8(x_43, 14);
x_99 = lean_ctor_get_uint8(x_43, 15);
x_100 = lean_ctor_get_uint8(x_43, 16);
x_101 = lean_ctor_get_uint8(x_43, 17);
lean_dec(x_43);
x_102 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_102, 0, x_85);
lean_ctor_set_uint8(x_102, 1, x_86);
lean_ctor_set_uint8(x_102, 2, x_87);
lean_ctor_set_uint8(x_102, 3, x_88);
lean_ctor_set_uint8(x_102, 4, x_89);
lean_ctor_set_uint8(x_102, 5, x_90);
lean_ctor_set_uint8(x_102, 6, x_91);
lean_ctor_set_uint8(x_102, 7, x_92);
lean_ctor_set_uint8(x_102, 8, x_93);
lean_ctor_set_uint8(x_102, 9, x_1);
lean_ctor_set_uint8(x_102, 10, x_94);
lean_ctor_set_uint8(x_102, 11, x_95);
lean_ctor_set_uint8(x_102, 12, x_96);
lean_ctor_set_uint8(x_102, 13, x_97);
lean_ctor_set_uint8(x_102, 14, x_98);
lean_ctor_set_uint8(x_102, 15, x_99);
lean_ctor_set_uint8(x_102, 16, x_100);
lean_ctor_set_uint8(x_102, 17, x_101);
x_103 = 2;
x_104 = lean_uint64_shift_right(x_44, x_103);
x_105 = lean_uint64_shift_left(x_104, x_103);
x_106 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_107 = lean_uint64_lor(x_105, x_106);
x_108 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_108, 0, x_102);
lean_ctor_set(x_108, 1, x_46);
lean_ctor_set(x_108, 2, x_47);
lean_ctor_set(x_108, 3, x_48);
lean_ctor_set(x_108, 4, x_49);
lean_ctor_set(x_108, 5, x_50);
lean_ctor_set(x_108, 6, x_51);
lean_ctor_set_uint64(x_108, sizeof(void*)*7, x_107);
lean_ctor_set_uint8(x_108, sizeof(void*)*7 + 8, x_45);
lean_ctor_set_uint8(x_108, sizeof(void*)*7 + 9, x_83);
lean_ctor_set_uint8(x_108, sizeof(void*)*7 + 10, x_84);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_108);
lean_inc(x_2);
x_109 = lean_infer_type(x_2, x_108, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_112 = l_Lean_Meta_isExprDefEq(x_110, x_3, x_108, x_8, x_9, x_10, x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_unbox(x_113);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_115;
goto block_42;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
lean_inc(x_2);
x_117 = l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0(x_4, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_116);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_unbox(x_118);
if (x_119 == 0)
{
lean_object* x_120; 
lean_dec(x_118);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
x_19 = x_8;
x_20 = x_9;
x_21 = x_10;
x_22 = x_120;
goto block_42;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
x_121 = lean_ctor_get(x_117, 1);
lean_inc(x_121);
lean_dec(x_117);
x_122 = l_Lean_MVarId_assign___at___Lean_Elab_Term_exprToSyntax_spec__0___redArg(x_4, x_2, x_8, x_121);
lean_dec(x_8);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_118);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_112;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_108);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_126 = lean_ctor_get(x_109, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_109, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_128 = x_109;
} else {
 lean_dec_ref(x_109);
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
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_42:
{
lean_object* x_23; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_23 = l_Lean_Meta_coerce_x3f(x_2, x_3, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_26);
x_27 = l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0(x_4, x_26, x_16, x_17, x_18, x_19, x_20, x_21, x_25);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_4);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_12 = x_30;
goto block_15;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lean_MVarId_assign___at___Lean_Elab_Term_exprToSyntax_spec__0___redArg(x_4, x_26, x_19, x_31);
lean_dec(x_19);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_28);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_4);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_dec(x_23);
x_12 = x_37;
goto block_15;
}
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_23);
if (x_38 == 0)
{
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_26; lean_object* x_49; 
lean_inc(x_1);
x_49 = l_Lean_MVarId_getType(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_instantiateExprMVars___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_spec__0___redArg(x_50, x_9, x_51);
x_26 = x_52;
goto block_48;
}
else
{
x_26 = x_49;
goto block_48;
}
block_25:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_Elab_Term_runTactic(x_1, x_2, x_3, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
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
block_48:
{
if (lean_obj_tag(x_26) == 0)
{
if (x_4 == 0)
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(x_4);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
if (x_5 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_dec(x_26);
x_13 = x_33;
goto block_25;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
x_37 = l_Lean_Expr_hasExprMVar(x_35);
lean_dec(x_35);
if (x_37 == 0)
{
lean_free_object(x_26);
x_13 = x_36;
goto block_25;
}
else
{
lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_box(0);
lean_ctor_set(x_26, 0, x_38);
return x_26;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_26);
x_41 = l_Lean_Expr_hasExprMVar(x_39);
lean_dec(x_39);
if (x_41 == 0)
{
x_13 = x_40;
goto block_25;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Term_getSyntheticMVarDecl_x3f___redArg(x_1, x_5, x_10);
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
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(1);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_8, 5);
x_25 = l_Lean_replaceRef(x_21, x_24);
lean_dec(x_24);
lean_ctor_set(x_8, 5, x_25);
switch (lean_obj_tag(x_22)) {
case 0:
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar(x_1, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
return x_27;
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 2);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_box(1);
lean_inc(x_1);
x_31 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lam__0___boxed), 11, 4);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_29);
lean_closure_set(x_31, 2, x_28);
lean_closure_set(x_31, 3, x_1);
x_32 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_1, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
return x_32;
}
case 2:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_21);
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_22, 2);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_22, sizeof(void*)*3);
lean_dec(x_22);
x_37 = lean_box(x_3);
x_38 = lean_box(x_36);
x_39 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lam__1___boxed), 12, 5);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_33);
lean_closure_set(x_39, 2, x_35);
lean_closure_set(x_39, 3, x_37);
lean_closure_set(x_39, 4, x_38);
x_40 = l_Lean_Elab_Term_withSavedContext___redArg(x_34, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
return x_40;
}
default: 
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_22, 0);
lean_inc(x_41);
lean_dec(x_22);
x_42 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(x_41, x_21, x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
x_45 = lean_ctor_get(x_8, 2);
x_46 = lean_ctor_get(x_8, 3);
x_47 = lean_ctor_get(x_8, 4);
x_48 = lean_ctor_get(x_8, 5);
x_49 = lean_ctor_get(x_8, 6);
x_50 = lean_ctor_get(x_8, 7);
x_51 = lean_ctor_get(x_8, 8);
x_52 = lean_ctor_get(x_8, 9);
x_53 = lean_ctor_get(x_8, 10);
x_54 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_55 = lean_ctor_get(x_8, 11);
x_56 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_57 = lean_ctor_get(x_8, 12);
lean_inc(x_57);
lean_inc(x_55);
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
lean_dec(x_8);
x_58 = l_Lean_replaceRef(x_21, x_48);
lean_dec(x_48);
x_59 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_59, 0, x_43);
lean_ctor_set(x_59, 1, x_44);
lean_ctor_set(x_59, 2, x_45);
lean_ctor_set(x_59, 3, x_46);
lean_ctor_set(x_59, 4, x_47);
lean_ctor_set(x_59, 5, x_58);
lean_ctor_set(x_59, 6, x_49);
lean_ctor_set(x_59, 7, x_50);
lean_ctor_set(x_59, 8, x_51);
lean_ctor_set(x_59, 9, x_52);
lean_ctor_set(x_59, 10, x_53);
lean_ctor_set(x_59, 11, x_55);
lean_ctor_set(x_59, 12, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*13, x_54);
lean_ctor_set_uint8(x_59, sizeof(void*)*13 + 1, x_56);
switch (lean_obj_tag(x_22)) {
case 0:
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_21);
x_60 = lean_ctor_get(x_22, 0);
lean_inc(x_60);
lean_dec(x_22);
x_61 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar(x_1, x_60, x_4, x_5, x_6, x_7, x_59, x_9, x_20);
return x_61;
}
case 1:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_21);
x_62 = lean_ctor_get(x_22, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_22, 2);
lean_inc(x_63);
lean_dec(x_22);
x_64 = lean_box(1);
lean_inc(x_1);
x_65 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lam__0___boxed), 11, 4);
lean_closure_set(x_65, 0, x_64);
lean_closure_set(x_65, 1, x_63);
lean_closure_set(x_65, 2, x_62);
lean_closure_set(x_65, 3, x_1);
x_66 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_1, x_65, x_4, x_5, x_6, x_7, x_59, x_9, x_20);
return x_66;
}
case 2:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_21);
x_67 = lean_ctor_get(x_22, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_22, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_22, 2);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_22, sizeof(void*)*3);
lean_dec(x_22);
x_71 = lean_box(x_3);
x_72 = lean_box(x_70);
x_73 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lam__1___boxed), 12, 5);
lean_closure_set(x_73, 0, x_1);
lean_closure_set(x_73, 1, x_67);
lean_closure_set(x_73, 2, x_69);
lean_closure_set(x_73, 3, x_71);
lean_closure_set(x_73, 4, x_72);
x_74 = l_Lean_Elab_Term_withSavedContext___redArg(x_68, x_73, x_4, x_5, x_6, x_7, x_59, x_9, x_20);
return x_74;
}
default: 
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_22, 0);
lean_inc(x_75);
lean_dec(x_22);
x_76 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(x_75, x_21, x_1, x_2, x_4, x_5, x_6, x_7, x_59, x_9, x_20);
return x_76;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 5);
lean_dec(x_13);
x_14 = l_Lean_Environment_setExporting(x_12, x_2);
lean_ctor_set(x_9, 5, x_3);
lean_ctor_set(x_9, 0, x_14);
x_15 = lean_st_ref_set(x_1, x_9, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_4, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_dec(x_21);
lean_ctor_set(x_18, 1, x_5);
x_22 = lean_st_ref_set(x_4, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
x_32 = lean_ctor_get(x_18, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_5);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_31);
lean_ctor_set(x_33, 4, x_32);
x_34 = lean_st_ref_set(x_4, x_33, x_19);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
x_41 = lean_ctor_get(x_9, 2);
x_42 = lean_ctor_get(x_9, 3);
x_43 = lean_ctor_get(x_9, 4);
x_44 = lean_ctor_get(x_9, 6);
x_45 = lean_ctor_get(x_9, 7);
x_46 = lean_ctor_get(x_9, 8);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_47 = l_Lean_Environment_setExporting(x_39, x_2);
x_48 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
lean_ctor_set(x_48, 2, x_41);
lean_ctor_set(x_48, 3, x_42);
lean_ctor_set(x_48, 4, x_43);
lean_ctor_set(x_48, 5, x_3);
lean_ctor_set(x_48, 6, x_44);
lean_ctor_set(x_48, 7, x_45);
lean_ctor_set(x_48, 8, x_46);
x_49 = lean_st_ref_set(x_1, x_48, x_10);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_st_ref_take(x_4, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 4);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 5, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_5);
lean_ctor_set(x_59, 2, x_55);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_57);
x_60 = lean_st_ref_set(x_4, x_59, x_53);
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
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
}
static lean_object* _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__6;
x_2 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__5;
x_3 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__4;
x_4 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__3;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get_uint8(x_11, sizeof(void*)*8);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_7, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 5);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_Environment_setExporting(x_18, x_21);
x_23 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__2;
lean_ctor_set(x_15, 5, x_23);
lean_ctor_set(x_15, 0, x_22);
x_24 = lean_st_ref_set(x_7, x_15, x_16);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_take(x_5, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_27, 1);
lean_dec(x_30);
x_31 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__7;
lean_ctor_set(x_27, 1, x_31);
x_32 = lean_st_ref_set(x_5, x_27, x_28);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_7);
lean_inc(x_5);
x_34 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_35);
x_38 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___lam__0(x_7, x_13, x_23, x_5, x_31, x_37, x_36);
lean_dec(x_37);
lean_dec(x_5);
lean_dec(x_7);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_35);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_box(0);
x_46 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___lam__0(x_7, x_13, x_23, x_5, x_31, x_45, x_44);
lean_dec(x_5);
lean_dec(x_7);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 0, x_43);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_27, 0);
x_52 = lean_ctor_get(x_27, 2);
x_53 = lean_ctor_get(x_27, 3);
x_54 = lean_ctor_get(x_27, 4);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_27);
x_55 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__7;
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_52);
lean_ctor_set(x_56, 3, x_53);
lean_ctor_set(x_56, 4, x_54);
x_57 = lean_st_ref_set(x_5, x_56, x_28);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
lean_inc(x_7);
lean_inc(x_5);
x_59 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_60);
x_63 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___lam__0(x_7, x_13, x_23, x_5, x_55, x_62, x_61);
lean_dec(x_62);
lean_dec(x_5);
lean_dec(x_7);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_59, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_59, 1);
lean_inc(x_68);
lean_dec(x_59);
x_69 = lean_box(0);
x_70 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___lam__0(x_7, x_13, x_23, x_5, x_55, x_69, x_68);
lean_dec(x_5);
lean_dec(x_7);
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
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
 lean_ctor_set_tag(x_73, 1);
}
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_74 = lean_ctor_get(x_15, 0);
x_75 = lean_ctor_get(x_15, 1);
x_76 = lean_ctor_get(x_15, 2);
x_77 = lean_ctor_get(x_15, 3);
x_78 = lean_ctor_get(x_15, 4);
x_79 = lean_ctor_get(x_15, 6);
x_80 = lean_ctor_get(x_15, 7);
x_81 = lean_ctor_get(x_15, 8);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_15);
x_82 = lean_box(0);
x_83 = lean_unbox(x_82);
x_84 = l_Lean_Environment_setExporting(x_74, x_83);
x_85 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__2;
x_86 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_75);
lean_ctor_set(x_86, 2, x_76);
lean_ctor_set(x_86, 3, x_77);
lean_ctor_set(x_86, 4, x_78);
lean_ctor_set(x_86, 5, x_85);
lean_ctor_set(x_86, 6, x_79);
lean_ctor_set(x_86, 7, x_80);
lean_ctor_set(x_86, 8, x_81);
x_87 = lean_st_ref_set(x_7, x_86, x_16);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_st_ref_take(x_5, x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_90, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 4);
lean_inc(x_95);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 lean_ctor_release(x_90, 3);
 lean_ctor_release(x_90, 4);
 x_96 = x_90;
} else {
 lean_dec_ref(x_90);
 x_96 = lean_box(0);
}
x_97 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__7;
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 5, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_92);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_98, 2, x_93);
lean_ctor_set(x_98, 3, x_94);
lean_ctor_set(x_98, 4, x_95);
x_99 = lean_st_ref_set(x_5, x_98, x_91);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
lean_inc(x_7);
lean_inc(x_5);
x_101 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_102);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_102);
x_105 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___lam__0(x_7, x_13, x_85, x_5, x_97, x_104, x_103);
lean_dec(x_104);
lean_dec(x_5);
lean_dec(x_7);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_102);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_ctor_get(x_101, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_101, 1);
lean_inc(x_110);
lean_dec(x_101);
x_111 = lean_box(0);
x_112 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___lam__0(x_7, x_13, x_85, x_5, x_97, x_111, x_110);
lean_dec(x_5);
lean_dec(x_7);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
 lean_ctor_set_tag(x_115, 1);
}
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0___lam__0___boxed), 8, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg(x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l_Lean_Core_betaReduce(x_13, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Meta_zetaReduce(x_16, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = lean_apply_8(x_3, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(1);
x_25 = lean_box(0);
x_26 = lean_unbox(x_24);
x_27 = l_Lean_Meta_mkAuxTheorem(x_22, x_1, x_26, x_25, x_2, x_6, x_7, x_8, x_9, x_23);
return x_27;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_21;
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
lean_dec(x_3);
lean_dec(x_1);
return x_18;
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
lean_dec(x_3);
lean_dec(x_1);
return x_15;
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
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 8);
lean_inc(x_19);
x_20 = lean_ctor_get(x_9, 9);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 10);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_9, sizeof(void*)*13);
x_23 = lean_ctor_get(x_9, 11);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*13 + 1);
x_25 = lean_ctor_get(x_9, 12);
lean_inc(x_25);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 lean_ctor_release(x_9, 4);
 lean_ctor_release(x_9, 5);
 lean_ctor_release(x_9, 6);
 lean_ctor_release(x_9, 7);
 lean_ctor_release(x_9, 8);
 lean_ctor_release(x_9, 9);
 lean_ctor_release(x_9, 10);
 lean_ctor_release(x_9, 11);
 lean_ctor_release(x_9, 12);
 x_26 = x_9;
} else {
 lean_dec_ref(x_9);
 x_26 = lean_box(0);
}
if (x_24 == 0)
{
x_27 = x_24;
goto block_30;
}
else
{
uint8_t x_31; 
lean_inc(x_1);
x_31 = l_Lean_Syntax_hasMissing(x_1);
x_27 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 13, 2);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_13);
lean_ctor_set(x_28, 2, x_14);
lean_ctor_set(x_28, 3, x_15);
lean_ctor_set(x_28, 4, x_16);
lean_ctor_set(x_28, 5, x_1);
lean_ctor_set(x_28, 6, x_17);
lean_ctor_set(x_28, 7, x_18);
lean_ctor_set(x_28, 8, x_19);
lean_ctor_set(x_28, 9, x_20);
lean_ctor_set(x_28, 10, x_21);
lean_ctor_set(x_28, 11, x_23);
lean_ctor_set(x_28, 12, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*13, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*13 + 1, x_27);
x_29 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_28, x_10, x_11);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at___Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_withReuseContext___at___Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_2);
x_13 = lean_apply_1(x_1, x_2);
x_14 = l_Lean_Elab_Term_withReuseContext___at___Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2_spec__2___redArg(x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot_go), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_5, 6);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
goto block_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
goto block_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_apply_10(x_2, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_23;
}
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__2___closed__0;
x_14 = l_Lean_Language_SnapshotTask_cancelRec___redArg(x_13, x_12, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_apply_10(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; lean_object* x_80; lean_object* x_116; 
lean_inc(x_1);
x_58 = lean_apply_1(x_1, x_3);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_10, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_6, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_6, 1);
lean_inc(x_63);
x_64 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_65 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 1);
x_66 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 2);
x_67 = lean_ctor_get(x_6, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_6, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_6, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_6, 5);
lean_inc(x_70);
x_71 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 3);
x_72 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 4);
x_73 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 5);
x_74 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 6);
x_75 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 7);
x_76 = lean_ctor_get(x_6, 6);
lean_inc(x_76);
x_77 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_78 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_79 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
lean_dec(x_6);
x_116 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__0___boxed), 12, 2);
lean_closure_set(x_116, 0, x_2);
lean_closure_set(x_116, 1, x_60);
if (lean_obj_tag(x_76) == 0)
{
goto block_119;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_76, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec(x_120);
if (lean_obj_tag(x_121) == 0)
{
goto block_119;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__2), 11, 2);
lean_closure_set(x_123, 0, x_122);
lean_closure_set(x_123, 1, x_116);
x_80 = x_123;
goto block_115;
}
}
block_34:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_16);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set(x_32, 3, x_19);
lean_ctor_set(x_32, 4, x_30);
lean_ctor_set(x_32, 5, x_29);
lean_ctor_set(x_32, 6, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*7, x_21);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 1, x_22);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 2, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 3, x_25);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 4, x_18);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 5, x_13);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 6, x_14);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 7, x_17);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 8, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 9, x_26);
lean_ctor_set_uint8(x_32, sizeof(void*)*7 + 10, x_15);
x_33 = lean_apply_9(x_23, x_4, x_5, x_32, x_7, x_8, x_9, x_10, x_11, x_12);
return x_33;
}
block_57:
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_42);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_13 = x_35;
x_14 = x_36;
x_15 = x_37;
x_16 = x_38;
x_17 = x_39;
x_18 = x_40;
x_19 = x_41;
x_20 = x_43;
x_21 = x_44;
x_22 = x_45;
x_23 = x_46;
x_24 = x_47;
x_25 = x_48;
x_26 = x_51;
x_27 = x_50;
x_28 = x_49;
x_29 = x_52;
x_30 = x_53;
x_31 = x_56;
goto block_34;
}
block_115:
{
if (lean_obj_tag(x_76) == 0)
{
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_1);
x_13 = x_73;
x_14 = x_74;
x_15 = x_79;
x_16 = x_63;
x_17 = x_75;
x_18 = x_72;
x_19 = x_68;
x_20 = x_62;
x_21 = x_64;
x_22 = x_65;
x_23 = x_80;
x_24 = x_67;
x_25 = x_71;
x_26 = x_78;
x_27 = x_77;
x_28 = x_66;
x_29 = x_70;
x_30 = x_69;
x_31 = x_76;
goto block_34;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
lean_dec(x_76);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_1);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_35 = x_73;
x_36 = x_74;
x_37 = x_79;
x_38 = x_63;
x_39 = x_75;
x_40 = x_72;
x_41 = x_68;
x_42 = x_83;
x_43 = x_62;
x_44 = x_64;
x_45 = x_65;
x_46 = x_80;
x_47 = x_67;
x_48 = x_71;
x_49 = x_66;
x_50 = x_77;
x_51 = x_78;
x_52 = x_70;
x_53 = x_69;
x_54 = x_82;
goto block_57;
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_dec(x_81);
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_ctor_get(x_85, 0);
x_89 = lean_ctor_get(x_85, 1);
x_90 = lean_apply_1(x_1, x_88);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Syntax_eqWithInfoAndTraceReuse(x_61, x_59, x_91);
lean_dec(x_61);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_92);
lean_free_object(x_85);
lean_dec(x_89);
lean_free_object(x_82);
x_94 = lean_box(0);
x_35 = x_73;
x_36 = x_74;
x_37 = x_79;
x_38 = x_63;
x_39 = x_75;
x_40 = x_72;
x_41 = x_68;
x_42 = x_86;
x_43 = x_62;
x_44 = x_64;
x_45 = x_65;
x_46 = x_80;
x_47 = x_67;
x_48 = x_71;
x_49 = x_66;
x_50 = x_77;
x_51 = x_78;
x_52 = x_70;
x_53 = x_69;
x_54 = x_94;
goto block_57;
}
else
{
lean_ctor_set(x_85, 0, x_92);
x_35 = x_73;
x_36 = x_74;
x_37 = x_79;
x_38 = x_63;
x_39 = x_75;
x_40 = x_72;
x_41 = x_68;
x_42 = x_86;
x_43 = x_62;
x_44 = x_64;
x_45 = x_65;
x_46 = x_80;
x_47 = x_67;
x_48 = x_71;
x_49 = x_66;
x_50 = x_77;
x_51 = x_78;
x_52 = x_70;
x_53 = x_69;
x_54 = x_82;
goto block_57;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_95 = lean_ctor_get(x_85, 0);
x_96 = lean_ctor_get(x_85, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_85);
x_97 = lean_apply_1(x_1, x_95);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_Syntax_eqWithInfoAndTraceReuse(x_61, x_59, x_98);
lean_dec(x_61);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_99);
lean_dec(x_96);
lean_free_object(x_82);
x_101 = lean_box(0);
x_35 = x_73;
x_36 = x_74;
x_37 = x_79;
x_38 = x_63;
x_39 = x_75;
x_40 = x_72;
x_41 = x_68;
x_42 = x_86;
x_43 = x_62;
x_44 = x_64;
x_45 = x_65;
x_46 = x_80;
x_47 = x_67;
x_48 = x_71;
x_49 = x_66;
x_50 = x_77;
x_51 = x_78;
x_52 = x_70;
x_53 = x_69;
x_54 = x_101;
goto block_57;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_96);
lean_ctor_set(x_82, 0, x_102);
x_35 = x_73;
x_36 = x_74;
x_37 = x_79;
x_38 = x_63;
x_39 = x_75;
x_40 = x_72;
x_41 = x_68;
x_42 = x_86;
x_43 = x_62;
x_44 = x_64;
x_45 = x_65;
x_46 = x_80;
x_47 = x_67;
x_48 = x_71;
x_49 = x_66;
x_50 = x_77;
x_51 = x_78;
x_52 = x_70;
x_53 = x_69;
x_54 = x_82;
goto block_57;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_103 = lean_ctor_get(x_82, 0);
lean_inc(x_103);
lean_dec(x_82);
x_104 = lean_ctor_get(x_81, 1);
lean_inc(x_104);
lean_dec(x_81);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_107 = x_103;
} else {
 lean_dec_ref(x_103);
 x_107 = lean_box(0);
}
x_108 = lean_apply_1(x_1, x_105);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_Syntax_eqWithInfoAndTraceReuse(x_61, x_59, x_109);
lean_dec(x_61);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_110);
lean_dec(x_107);
lean_dec(x_106);
x_112 = lean_box(0);
x_35 = x_73;
x_36 = x_74;
x_37 = x_79;
x_38 = x_63;
x_39 = x_75;
x_40 = x_72;
x_41 = x_68;
x_42 = x_104;
x_43 = x_62;
x_44 = x_64;
x_45 = x_65;
x_46 = x_80;
x_47 = x_67;
x_48 = x_71;
x_49 = x_66;
x_50 = x_77;
x_51 = x_78;
x_52 = x_70;
x_53 = x_69;
x_54 = x_112;
goto block_57;
}
else
{
lean_object* x_113; lean_object* x_114; 
if (lean_is_scalar(x_107)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_107;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_106);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_35 = x_73;
x_36 = x_74;
x_37 = x_79;
x_38 = x_63;
x_39 = x_75;
x_40 = x_72;
x_41 = x_68;
x_42 = x_104;
x_43 = x_62;
x_44 = x_64;
x_45 = x_65;
x_46 = x_80;
x_47 = x_67;
x_48 = x_71;
x_49 = x_66;
x_50 = x_77;
x_51 = x_78;
x_52 = x_70;
x_53 = x_69;
x_54 = x_114;
goto block_57;
}
}
}
}
}
block_119:
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_box(0);
x_118 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__1), 11, 2);
lean_closure_set(x_118, 0, x_116);
lean_closure_set(x_118, 1, x_117);
x_80 = x_118;
goto block_115;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_Lean_Syntax_getArgs(x_2);
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_5 = l_Array_toSubarray___redArg(x_3, x_4, x_1);
x_6 = l_Array_ofSubarray___redArg(x_5);
lean_dec(x_5);
x_7 = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0___closed__1;
x_8 = lean_box(2);
x_9 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_6);
x_10 = l_Lean_Syntax_getArg(x_2, x_1);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runTactic_spec__5___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_MVarId_admit(x_14, x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 1;
x_18 = lean_usize_add(x_5, x_17);
lean_inc(x_2);
{
size_t _tmp_4 = x_18;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_10 = x_16;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runTactic_spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runTactic_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
static lean_object* _init_l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_instMonadTermElabM___lam__1), 11, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__0;
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 2);
x_17 = lean_ctor_get(x_12, 3);
x_18 = lean_ctor_get(x_12, 4);
x_19 = lean_ctor_get(x_12, 1);
lean_dec(x_19);
x_20 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__1;
x_21 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__2;
lean_inc(x_15);
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
lean_ctor_set(x_12, 4, x_25);
lean_ctor_set(x_12, 3, x_26);
lean_ctor_set(x_12, 2, x_27);
lean_ctor_set(x_12, 1, x_20);
lean_ctor_set(x_12, 0, x_24);
lean_ctor_set(x_10, 1, x_21);
x_28 = l_ReaderT_instMonad___redArg(x_10);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 2);
x_35 = lean_ctor_get(x_30, 3);
x_36 = lean_ctor_get(x_30, 4);
x_37 = lean_ctor_get(x_30, 1);
lean_dec(x_37);
x_38 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__3;
x_39 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__4;
lean_inc(x_33);
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
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 2);
x_53 = lean_ctor_get(x_48, 3);
x_54 = lean_ctor_get(x_48, 4);
x_55 = lean_ctor_get(x_48, 1);
lean_dec(x_55);
x_56 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__5;
x_57 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__6;
lean_inc(x_51);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_58, 0, x_51);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_51);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_61, 0, x_54);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_62, 0, x_53);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_63, 0, x_52);
lean_ctor_set(x_48, 4, x_61);
lean_ctor_set(x_48, 3, x_62);
lean_ctor_set(x_48, 2, x_63);
lean_ctor_set(x_48, 1, x_56);
lean_ctor_set(x_48, 0, x_60);
lean_ctor_set(x_46, 1, x_57);
x_64 = l_Lean_instInhabitedLocalContext;
x_65 = l_instInhabitedOfMonad___redArg(x_46, x_64);
x_66 = lean_panic_fn(x_65, x_1);
x_67 = lean_apply_7(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_68 = lean_ctor_get(x_48, 0);
x_69 = lean_ctor_get(x_48, 2);
x_70 = lean_ctor_get(x_48, 3);
x_71 = lean_ctor_get(x_48, 4);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_48);
x_72 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__5;
x_73 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__6;
lean_inc(x_68);
x_74 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_74, 0, x_68);
x_75 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_75, 0, x_68);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_77, 0, x_71);
x_78 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_78, 0, x_70);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_79, 0, x_69);
x_80 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_72);
lean_ctor_set(x_80, 2, x_79);
lean_ctor_set(x_80, 3, x_78);
lean_ctor_set(x_80, 4, x_77);
lean_ctor_set(x_46, 1, x_73);
lean_ctor_set(x_46, 0, x_80);
x_81 = l_Lean_instInhabitedLocalContext;
x_82 = l_instInhabitedOfMonad___redArg(x_46, x_81);
x_83 = lean_panic_fn(x_82, x_1);
x_84 = lean_apply_7(x_83, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_85 = lean_ctor_get(x_46, 0);
lean_inc(x_85);
lean_dec(x_46);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_85, 4);
lean_inc(x_89);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 lean_ctor_release(x_85, 2);
 lean_ctor_release(x_85, 3);
 lean_ctor_release(x_85, 4);
 x_90 = x_85;
} else {
 lean_dec_ref(x_85);
 x_90 = lean_box(0);
}
x_91 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__5;
x_92 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__6;
lean_inc(x_86);
x_93 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_93, 0, x_86);
x_94 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_94, 0, x_86);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_96, 0, x_89);
x_97 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_97, 0, x_88);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_98, 0, x_87);
if (lean_is_scalar(x_90)) {
 x_99 = lean_alloc_ctor(0, 5, 0);
} else {
 x_99 = x_90;
}
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_91);
lean_ctor_set(x_99, 2, x_98);
lean_ctor_set(x_99, 3, x_97);
lean_ctor_set(x_99, 4, x_96);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_92);
x_101 = l_Lean_instInhabitedLocalContext;
x_102 = l_instInhabitedOfMonad___redArg(x_100, x_101);
x_103 = lean_panic_fn(x_102, x_1);
x_104 = lean_apply_7(x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_105 = lean_ctor_get(x_30, 0);
x_106 = lean_ctor_get(x_30, 2);
x_107 = lean_ctor_get(x_30, 3);
x_108 = lean_ctor_get(x_30, 4);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_30);
x_109 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__3;
x_110 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__4;
lean_inc(x_105);
x_111 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_111, 0, x_105);
x_112 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_112, 0, x_105);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_114, 0, x_108);
x_115 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_115, 0, x_107);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_116, 0, x_106);
x_117 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_109);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_117, 3, x_115);
lean_ctor_set(x_117, 4, x_114);
lean_ctor_set(x_28, 1, x_110);
lean_ctor_set(x_28, 0, x_117);
x_118 = l_ReaderT_instMonad___redArg(x_28);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_119, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_119, 4);
lean_inc(x_124);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 lean_ctor_release(x_119, 4);
 x_125 = x_119;
} else {
 lean_dec_ref(x_119);
 x_125 = lean_box(0);
}
x_126 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__5;
x_127 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__6;
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
if (lean_is_scalar(x_120)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_120;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_127);
x_136 = l_Lean_instInhabitedLocalContext;
x_137 = l_instInhabitedOfMonad___redArg(x_135, x_136);
x_138 = lean_panic_fn(x_137, x_1);
x_139 = lean_apply_7(x_138, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_140 = lean_ctor_get(x_28, 0);
lean_inc(x_140);
lean_dec(x_28);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 2);
lean_inc(x_142);
x_143 = lean_ctor_get(x_140, 3);
lean_inc(x_143);
x_144 = lean_ctor_get(x_140, 4);
lean_inc(x_144);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 lean_ctor_release(x_140, 2);
 lean_ctor_release(x_140, 3);
 lean_ctor_release(x_140, 4);
 x_145 = x_140;
} else {
 lean_dec_ref(x_140);
 x_145 = lean_box(0);
}
x_146 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__3;
x_147 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__4;
lean_inc(x_141);
x_148 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_148, 0, x_141);
x_149 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_149, 0, x_141);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_151, 0, x_144);
x_152 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_152, 0, x_143);
x_153 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_153, 0, x_142);
if (lean_is_scalar(x_145)) {
 x_154 = lean_alloc_ctor(0, 5, 0);
} else {
 x_154 = x_145;
}
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_146);
lean_ctor_set(x_154, 2, x_153);
lean_ctor_set(x_154, 3, x_152);
lean_ctor_set(x_154, 4, x_151);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_147);
x_156 = l_ReaderT_instMonad___redArg(x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_157, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_157, 3);
lean_inc(x_161);
x_162 = lean_ctor_get(x_157, 4);
lean_inc(x_162);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 lean_ctor_release(x_157, 2);
 lean_ctor_release(x_157, 3);
 lean_ctor_release(x_157, 4);
 x_163 = x_157;
} else {
 lean_dec_ref(x_157);
 x_163 = lean_box(0);
}
x_164 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__5;
x_165 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__6;
lean_inc(x_159);
x_166 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_166, 0, x_159);
x_167 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_167, 0, x_159);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_169, 0, x_162);
x_170 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_170, 0, x_161);
x_171 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_171, 0, x_160);
if (lean_is_scalar(x_163)) {
 x_172 = lean_alloc_ctor(0, 5, 0);
} else {
 x_172 = x_163;
}
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_164);
lean_ctor_set(x_172, 2, x_171);
lean_ctor_set(x_172, 3, x_170);
lean_ctor_set(x_172, 4, x_169);
if (lean_is_scalar(x_158)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_158;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_165);
x_174 = l_Lean_instInhabitedLocalContext;
x_175 = l_instInhabitedOfMonad___redArg(x_173, x_174);
x_176 = lean_panic_fn(x_175, x_1);
x_177 = lean_apply_7(x_176, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_178 = lean_ctor_get(x_12, 0);
x_179 = lean_ctor_get(x_12, 2);
x_180 = lean_ctor_get(x_12, 3);
x_181 = lean_ctor_get(x_12, 4);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_12);
x_182 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__1;
x_183 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__2;
lean_inc(x_178);
x_184 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_184, 0, x_178);
x_185 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_185, 0, x_178);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_187, 0, x_181);
x_188 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_188, 0, x_180);
x_189 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_189, 0, x_179);
x_190 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_190, 0, x_186);
lean_ctor_set(x_190, 1, x_182);
lean_ctor_set(x_190, 2, x_189);
lean_ctor_set(x_190, 3, x_188);
lean_ctor_set(x_190, 4, x_187);
lean_ctor_set(x_10, 1, x_183);
lean_ctor_set(x_10, 0, x_190);
x_191 = l_ReaderT_instMonad___redArg(x_10);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_193 = x_191;
} else {
 lean_dec_ref(x_191);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_192, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_192, 2);
lean_inc(x_195);
x_196 = lean_ctor_get(x_192, 3);
lean_inc(x_196);
x_197 = lean_ctor_get(x_192, 4);
lean_inc(x_197);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 lean_ctor_release(x_192, 4);
 x_198 = x_192;
} else {
 lean_dec_ref(x_192);
 x_198 = lean_box(0);
}
x_199 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__3;
x_200 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__4;
lean_inc(x_194);
x_201 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_201, 0, x_194);
x_202 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_202, 0, x_194);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_204, 0, x_197);
x_205 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_205, 0, x_196);
x_206 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_206, 0, x_195);
if (lean_is_scalar(x_198)) {
 x_207 = lean_alloc_ctor(0, 5, 0);
} else {
 x_207 = x_198;
}
lean_ctor_set(x_207, 0, x_203);
lean_ctor_set(x_207, 1, x_199);
lean_ctor_set(x_207, 2, x_206);
lean_ctor_set(x_207, 3, x_205);
lean_ctor_set(x_207, 4, x_204);
if (lean_is_scalar(x_193)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_193;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_200);
x_209 = l_ReaderT_instMonad___redArg(x_208);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_211 = x_209;
} else {
 lean_dec_ref(x_209);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 2);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 3);
lean_inc(x_214);
x_215 = lean_ctor_get(x_210, 4);
lean_inc(x_215);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 lean_ctor_release(x_210, 4);
 x_216 = x_210;
} else {
 lean_dec_ref(x_210);
 x_216 = lean_box(0);
}
x_217 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__5;
x_218 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__6;
lean_inc(x_212);
x_219 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_219, 0, x_212);
x_220 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_220, 0, x_212);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_222, 0, x_215);
x_223 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_223, 0, x_214);
x_224 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_224, 0, x_213);
if (lean_is_scalar(x_216)) {
 x_225 = lean_alloc_ctor(0, 5, 0);
} else {
 x_225 = x_216;
}
lean_ctor_set(x_225, 0, x_221);
lean_ctor_set(x_225, 1, x_217);
lean_ctor_set(x_225, 2, x_224);
lean_ctor_set(x_225, 3, x_223);
lean_ctor_set(x_225, 4, x_222);
if (lean_is_scalar(x_211)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_211;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_218);
x_227 = l_Lean_instInhabitedLocalContext;
x_228 = l_instInhabitedOfMonad___redArg(x_226, x_227);
x_229 = lean_panic_fn(x_228, x_1);
x_230 = lean_apply_7(x_229, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_231 = lean_ctor_get(x_10, 0);
lean_inc(x_231);
lean_dec(x_10);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 2);
lean_inc(x_233);
x_234 = lean_ctor_get(x_231, 3);
lean_inc(x_234);
x_235 = lean_ctor_get(x_231, 4);
lean_inc(x_235);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 lean_ctor_release(x_231, 2);
 lean_ctor_release(x_231, 3);
 lean_ctor_release(x_231, 4);
 x_236 = x_231;
} else {
 lean_dec_ref(x_231);
 x_236 = lean_box(0);
}
x_237 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__1;
x_238 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__2;
lean_inc(x_232);
x_239 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_239, 0, x_232);
x_240 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_240, 0, x_232);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_242, 0, x_235);
x_243 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_243, 0, x_234);
x_244 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_244, 0, x_233);
if (lean_is_scalar(x_236)) {
 x_245 = lean_alloc_ctor(0, 5, 0);
} else {
 x_245 = x_236;
}
lean_ctor_set(x_245, 0, x_241);
lean_ctor_set(x_245, 1, x_237);
lean_ctor_set(x_245, 2, x_244);
lean_ctor_set(x_245, 3, x_243);
lean_ctor_set(x_245, 4, x_242);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_238);
x_247 = l_ReaderT_instMonad___redArg(x_246);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_249 = x_247;
} else {
 lean_dec_ref(x_247);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_248, 2);
lean_inc(x_251);
x_252 = lean_ctor_get(x_248, 3);
lean_inc(x_252);
x_253 = lean_ctor_get(x_248, 4);
lean_inc(x_253);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 lean_ctor_release(x_248, 2);
 lean_ctor_release(x_248, 3);
 lean_ctor_release(x_248, 4);
 x_254 = x_248;
} else {
 lean_dec_ref(x_248);
 x_254 = lean_box(0);
}
x_255 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__3;
x_256 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__4;
lean_inc(x_250);
x_257 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_257, 0, x_250);
x_258 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_258, 0, x_250);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
x_260 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_260, 0, x_253);
x_261 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_261, 0, x_252);
x_262 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_262, 0, x_251);
if (lean_is_scalar(x_254)) {
 x_263 = lean_alloc_ctor(0, 5, 0);
} else {
 x_263 = x_254;
}
lean_ctor_set(x_263, 0, x_259);
lean_ctor_set(x_263, 1, x_255);
lean_ctor_set(x_263, 2, x_262);
lean_ctor_set(x_263, 3, x_261);
lean_ctor_set(x_263, 4, x_260);
if (lean_is_scalar(x_249)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_249;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_256);
x_265 = l_ReaderT_instMonad___redArg(x_264);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_267 = x_265;
} else {
 lean_dec_ref(x_265);
 x_267 = lean_box(0);
}
x_268 = lean_ctor_get(x_266, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_266, 2);
lean_inc(x_269);
x_270 = lean_ctor_get(x_266, 3);
lean_inc(x_270);
x_271 = lean_ctor_get(x_266, 4);
lean_inc(x_271);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 lean_ctor_release(x_266, 2);
 lean_ctor_release(x_266, 3);
 lean_ctor_release(x_266, 4);
 x_272 = x_266;
} else {
 lean_dec_ref(x_266);
 x_272 = lean_box(0);
}
x_273 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__5;
x_274 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__6;
lean_inc(x_268);
x_275 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_275, 0, x_268);
x_276 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_276, 0, x_268);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_278, 0, x_271);
x_279 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_279, 0, x_270);
x_280 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_280, 0, x_269);
if (lean_is_scalar(x_272)) {
 x_281 = lean_alloc_ctor(0, 5, 0);
} else {
 x_281 = x_272;
}
lean_ctor_set(x_281, 0, x_277);
lean_ctor_set(x_281, 1, x_273);
lean_ctor_set(x_281, 2, x_280);
lean_ctor_set(x_281, 3, x_279);
lean_ctor_set(x_281, 4, x_278);
if (lean_is_scalar(x_267)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_267;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_274);
x_283 = l_Lean_instInhabitedLocalContext;
x_284 = l_instInhabitedOfMonad___redArg(x_282, x_283);
x_285 = lean_panic_fn(x_284, x_1);
x_286 = lean_apply_7(x_285, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_286;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_4, x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget(x_3, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_16 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_4 = x_20;
x_6 = x_17;
x_13 = x_18;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_16;
}
}
else
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.MetavarContext", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.instantiateLCtxMVars", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid auxiliary declaration found in local context: ", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" does not have an associated full name.", 39, 39);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_20; 
x_20 = lean_usize_dec_eq(x_4, x_5);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_array_uget(x_3, x_4);
if (lean_obj_tag(x_21) == 0)
{
x_14 = x_6;
x_15 = x_13;
goto block_19;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; lean_object* x_24; 
x_23 = lean_ctor_get_uint8(x_22, sizeof(void*)*4 + 1);
x_24 = lean_box(x_23);
if (lean_obj_tag(x_24) == 2)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 3);
lean_inc(x_27);
lean_dec(x_22);
x_28 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_27, x_10, x_13);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_RBNode_find___at___Lean_resolveLocalName___at___Lean_unresolveNameGlobalAvoidingLocals___at___Lean_PrettyPrinter_Delaborator_delabConst_spec__0_spec__0_spec__0___redArg(x_1, x_25);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_6);
x_32 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__0;
x_33 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__1;
x_34 = lean_unsigned_to_nat(610u);
x_35 = lean_unsigned_to_nat(12u);
x_36 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__2;
x_37 = lean_box(1);
x_38 = lean_unbox(x_37);
lean_inc(x_2);
x_39 = l_Lean_Name_toString(x_26, x_38, x_2);
x_40 = lean_string_append(x_36, x_39);
lean_dec(x_39);
x_41 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__3;
x_42 = lean_string_append(x_40, x_41);
x_43 = l_mkPanicMessageWithDecl(x_32, x_33, x_34, x_35, x_42);
lean_dec(x_42);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_44 = l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6(x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_30);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_14 = x_45;
x_15 = x_46;
goto block_19;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_44;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_31, 0);
lean_inc(x_47);
lean_dec(x_31);
x_48 = l_Lean_LocalContext_mkAuxDecl(x_6, x_25, x_26, x_29, x_47);
x_14 = x_48;
x_15 = x_30;
goto block_19;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_24);
x_49 = lean_ctor_get(x_22, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_22, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_22, 3);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_22, sizeof(void*)*4);
lean_dec(x_22);
x_53 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_51, x_10, x_13);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_LocalContext_mkLocalDecl(x_6, x_49, x_50, x_54, x_52, x_23);
x_14 = x_56;
x_15 = x_55;
goto block_19;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_57 = lean_ctor_get(x_22, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_22, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_22, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_22, 4);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_22, sizeof(void*)*5);
x_62 = lean_ctor_get_uint8(x_22, sizeof(void*)*5 + 1);
lean_dec(x_22);
x_63 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_59, x_10, x_13);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_60, x_10, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_LocalContext_mkLetDecl(x_6, x_57, x_58, x_64, x_67, x_61, x_62);
x_14 = x_69;
x_15 = x_68;
goto block_19;
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_6);
lean_ctor_set(x_70, 1, x_13);
return x_70;
}
block_19:
{
size_t x_16; size_t x_17; 
x_16 = 1;
x_17 = lean_usize_add(x_4, x_16);
x_4 = x_17;
x_6 = x_14;
x_13 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_12);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_14, x_14);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_21 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__7(x_1, x_2, x_12, x_19, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get_size(x_22);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_11);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_24, x_24);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_11);
return x_28;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_31 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8(x_1, x_2, x_22, x_29, x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_31;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArrayNode(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7___closed__0;
x_16 = lean_usize_shift_right(x_4, x_5);
x_17 = lean_usize_to_nat(x_16);
x_18 = lean_array_get(x_15, x_14, x_17);
x_19 = 1;
x_20 = lean_usize_shift_left(x_19, x_5);
x_21 = lean_usize_sub(x_20, x_19);
x_22 = lean_usize_land(x_4, x_21);
x_23 = 5;
x_24 = lean_usize_sub(x_5, x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_25 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7(x_1, x_2, x_18, x_22, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_17, x_28);
lean_dec(x_17);
x_30 = lean_array_get_size(x_14);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_25;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_25;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
lean_dec(x_25);
x_33 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_34 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_35 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__7(x_1, x_2, x_14, x_33, x_34, x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
return x_35;
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_25;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_3, 0);
x_37 = lean_usize_to_nat(x_4);
x_38 = lean_array_get_size(x_36);
x_39 = lean_nat_dec_lt(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_13);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_le(x_38, x_38);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_6);
lean_ctor_set(x_42, 1, x_13);
return x_42;
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; 
x_43 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_44 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_45 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8(x_1, x_2, x_36, x_43, x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get_usize(x_3, 4);
x_18 = lean_ctor_get(x_3, 3);
x_19 = lean_nat_dec_le(x_18, x_5);
if (x_19 == 0)
{
size_t x_20; lean_object* x_21; 
x_20 = lean_usize_of_nat(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_21 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7(x_1, x_2, x_15, x_20, x_17, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_array_get_size(x_16);
x_25 = lean_nat_dec_lt(x_13, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_21;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_24, x_24);
if (x_26 == 0)
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_21;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
lean_dec(x_21);
x_27 = 0;
x_28 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_29 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8(x_1, x_2, x_16, x_27, x_28, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
return x_29;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_21;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_nat_sub(x_5, x_18);
x_31 = lean_array_get_size(x_16);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_12);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_31, x_31);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_12);
return x_35;
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; 
x_36 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_37 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_38 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8(x_1, x_2, x_16, x_36, x_37, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_38;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_41 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7(x_1, x_2, x_39, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
x_44 = lean_array_get_size(x_40);
x_45 = lean_nat_dec_lt(x_13, x_44);
if (x_45 == 0)
{
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_41;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_44, x_44);
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_41;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
lean_dec(x_41);
x_47 = 0;
x_48 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_49 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8(x_1, x_2, x_40, x_47, x_48, x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
return x_49;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 1);
x_14 = l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__2;
x_4 = l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__3;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__4;
x_3 = l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_alloc_closure((void*)(l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___lam__0___boxed), 1, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__5;
x_13 = l_Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7(x_9, x_10, x_1, x_12, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_inc(x_1);
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
lean_inc(x_5);
x_22 = l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_17, x_5, x_24);
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
x_40 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_39, x_1, x_13);
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
x_57 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_52, x_1, x_13);
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
x_78 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_72, x_1, x_13);
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
x_111 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_105, x_1, x_13);
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
lean_dec(x_5);
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
lean_inc(x_5);
x_131 = l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6(x_124, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_124);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_125, x_5, x_133);
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
x_162 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_155, x_1, x_161);
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
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_isProp(x_10, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 5);
lean_dec(x_13);
x_14 = l_Lean_Environment_setExporting(x_12, x_2);
lean_ctor_set(x_9, 5, x_3);
lean_ctor_set(x_9, 0, x_14);
x_15 = lean_st_ref_set(x_1, x_9, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_4, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_dec(x_21);
lean_ctor_set(x_18, 1, x_5);
x_22 = lean_st_ref_set(x_4, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
x_32 = lean_ctor_get(x_18, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_5);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_31);
lean_ctor_set(x_33, 4, x_32);
x_34 = lean_st_ref_set(x_4, x_33, x_19);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
x_41 = lean_ctor_get(x_9, 2);
x_42 = lean_ctor_get(x_9, 3);
x_43 = lean_ctor_get(x_9, 4);
x_44 = lean_ctor_get(x_9, 6);
x_45 = lean_ctor_get(x_9, 7);
x_46 = lean_ctor_get(x_9, 8);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_47 = l_Lean_Environment_setExporting(x_39, x_2);
x_48 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
lean_ctor_set(x_48, 2, x_41);
lean_ctor_set(x_48, 3, x_42);
lean_ctor_set(x_48, 4, x_43);
lean_ctor_set(x_48, 5, x_3);
lean_ctor_set(x_48, 6, x_44);
lean_ctor_set(x_48, 7, x_45);
lean_ctor_set(x_48, 8, x_46);
x_49 = lean_st_ref_set(x_1, x_48, x_10);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_st_ref_take(x_4, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 4);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 5, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_5);
lean_ctor_set(x_59, 2, x_55);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_57);
x_60 = lean_st_ref_set(x_4, x_59, x_53);
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
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__4(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_10, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 5);
lean_dec(x_20);
x_21 = l_Lean_Environment_setExporting(x_19, x_1);
x_22 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__2;
lean_ctor_set(x_16, 5, x_22);
lean_ctor_set(x_16, 0, x_21);
x_23 = lean_st_ref_set(x_10, x_16, x_17);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_take(x_8, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_26, 1);
lean_dec(x_29);
x_30 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__7;
lean_ctor_set(x_26, 1, x_30);
x_31 = lean_st_ref_set(x_8, x_26, x_27);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get_uint8(x_32, sizeof(void*)*8);
lean_dec(x_32);
lean_inc(x_10);
lean_inc(x_8);
x_35 = l_Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_39 = l_Lean_Elab_Term_runTactic___lam__3(x_10, x_34, x_22, x_8, x_30, x_38, x_37);
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_10);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_36);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_box(0);
x_47 = l_Lean_Elab_Term_runTactic___lam__3(x_10, x_34, x_22, x_8, x_30, x_46, x_45);
lean_dec(x_8);
lean_dec(x_10);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 0, x_44);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_26, 0);
x_53 = lean_ctor_get(x_26, 2);
x_54 = lean_ctor_get(x_26, 3);
x_55 = lean_ctor_get(x_26, 4);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_26);
x_56 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__7;
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_53);
lean_ctor_set(x_57, 3, x_54);
lean_ctor_set(x_57, 4, x_55);
x_58 = lean_st_ref_set(x_8, x_57, x_27);
x_59 = lean_ctor_get(x_13, 0);
lean_inc(x_59);
lean_dec(x_13);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get_uint8(x_59, sizeof(void*)*8);
lean_dec(x_59);
lean_inc(x_10);
lean_inc(x_8);
x_62 = l_Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_63);
x_66 = l_Lean_Elab_Term_runTactic___lam__3(x_10, x_61, x_22, x_8, x_56, x_65, x_64);
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_10);
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
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
lean_dec(x_62);
x_72 = lean_box(0);
x_73 = l_Lean_Elab_Term_runTactic___lam__3(x_10, x_61, x_22, x_8, x_56, x_72, x_71);
lean_dec(x_8);
lean_dec(x_10);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
 lean_ctor_set_tag(x_76, 1);
}
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_77 = lean_ctor_get(x_16, 0);
x_78 = lean_ctor_get(x_16, 1);
x_79 = lean_ctor_get(x_16, 2);
x_80 = lean_ctor_get(x_16, 3);
x_81 = lean_ctor_get(x_16, 4);
x_82 = lean_ctor_get(x_16, 6);
x_83 = lean_ctor_get(x_16, 7);
x_84 = lean_ctor_get(x_16, 8);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_16);
x_85 = l_Lean_Environment_setExporting(x_77, x_1);
x_86 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__2;
x_87 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_78);
lean_ctor_set(x_87, 2, x_79);
lean_ctor_set(x_87, 3, x_80);
lean_ctor_set(x_87, 4, x_81);
lean_ctor_set(x_87, 5, x_86);
lean_ctor_set(x_87, 6, x_82);
lean_ctor_set(x_87, 7, x_83);
lean_ctor_set(x_87, 8, x_84);
x_88 = lean_st_ref_set(x_10, x_87, x_17);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_st_ref_take(x_8, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_91, 4);
lean_inc(x_96);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 lean_ctor_release(x_91, 3);
 lean_ctor_release(x_91, 4);
 x_97 = x_91;
} else {
 lean_dec_ref(x_91);
 x_97 = lean_box(0);
}
x_98 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__7;
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 5, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_93);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_99, 2, x_94);
lean_ctor_set(x_99, 3, x_95);
lean_ctor_set(x_99, 4, x_96);
x_100 = lean_st_ref_set(x_8, x_99, x_92);
x_101 = lean_ctor_get(x_13, 0);
lean_inc(x_101);
lean_dec(x_13);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get_uint8(x_101, sizeof(void*)*8);
lean_dec(x_101);
lean_inc(x_10);
lean_inc(x_8);
x_104 = l_Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_102);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_105);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_105);
x_108 = l_Lean_Elab_Term_runTactic___lam__3(x_10, x_103, x_86, x_8, x_98, x_107, x_106);
lean_dec(x_107);
lean_dec(x_8);
lean_dec(x_10);
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
lean_ctor_set(x_111, 0, x_105);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_112 = lean_ctor_get(x_104, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_104, 1);
lean_inc(x_113);
lean_dec(x_104);
x_114 = lean_box(0);
x_115 = l_Lean_Elab_Term_runTactic___lam__3(x_10, x_103, x_86, x_8, x_98, x_114, x_113);
lean_dec(x_8);
lean_dec(x_10);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
 lean_ctor_set_tag(x_118, 1);
}
lean_ctor_set(x_118, 0, x_112);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__5(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_1 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_2);
x_16 = l_Lean_Expr_mvar___override(x_2);
x_17 = l_Lean_instantiateExprMVars___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_spec__0___redArg(x_16, x_10, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_isFVar(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_box(x_3);
x_22 = lean_box(x_1);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lam__4___boxed), 11, 4);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_18);
lean_closure_set(x_23, 2, x_22);
lean_closure_set(x_23, 3, x_4);
lean_inc(x_10);
x_24 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_2, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_MVarId_assign___at___Lean_Elab_Term_exprToSyntax_spec__0___redArg(x_5, x_25, x_10, x_26);
lean_dec(x_10);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_32 = l_Lean_MVarId_assign___at___Lean_Elab_Term_exprToSyntax_spec__0___redArg(x_5, x_18, x_10, x_19);
lean_dec(x_10);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__6(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runTactic_spec__5___redArg(x_1, x_19, x_17, x_20, x_21, x_19, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Elab_logException___at___Lean_Elab_withLogging___at_____private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore_spec__2_spec__2(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
return x_24;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__7(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 5);
lean_dec(x_13);
x_14 = l_Lean_Environment_setExporting(x_12, x_2);
lean_ctor_set(x_9, 5, x_3);
lean_ctor_set(x_9, 0, x_14);
x_15 = lean_st_ref_set(x_1, x_9, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_4, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_dec(x_21);
lean_ctor_set(x_18, 1, x_5);
x_22 = lean_st_ref_set(x_4, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
x_32 = lean_ctor_get(x_18, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_5);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_31);
lean_ctor_set(x_33, 4, x_32);
x_34 = lean_st_ref_set(x_4, x_33, x_19);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
x_41 = lean_ctor_get(x_9, 2);
x_42 = lean_ctor_get(x_9, 3);
x_43 = lean_ctor_get(x_9, 4);
x_44 = lean_ctor_get(x_9, 6);
x_45 = lean_ctor_get(x_9, 7);
x_46 = lean_ctor_get(x_9, 8);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_47 = l_Lean_Environment_setExporting(x_39, x_2);
x_48 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
lean_ctor_set(x_48, 2, x_41);
lean_ctor_set(x_48, 3, x_42);
lean_ctor_set(x_48, 4, x_43);
lean_ctor_set(x_48, 5, x_3);
lean_ctor_set(x_48, 6, x_44);
lean_ctor_set(x_48, 7, x_45);
lean_ctor_set(x_48, 8, x_46);
x_49 = lean_st_ref_set(x_1, x_48, x_10);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_st_ref_take(x_4, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 4);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 5, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_5);
lean_ctor_set(x_59, 2, x_55);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_57);
x_60 = lean_st_ref_set(x_4, x_59, x_53);
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
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_31; 
x_8 = lean_st_ref_take(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 8);
lean_inc(x_19);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 lean_ctor_release(x_9, 4);
 lean_ctor_release(x_9, 5);
 lean_ctor_release(x_9, 6);
 lean_ctor_release(x_9, 7);
 lean_ctor_release(x_9, 8);
 x_20 = x_9;
} else {
 lean_dec_ref(x_9);
 x_20 = lean_box(0);
}
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_18, 2);
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_34);
x_35 = lean_nat_dec_lt(x_2, x_34);
if (x_35 == 0)
{
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_5);
lean_ctor_set(x_18, 2, x_3);
x_21 = x_18;
goto block_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_Lean_Elab_instInhabitedInfoTree;
x_37 = lean_nat_sub(x_34, x_4);
lean_dec(x_34);
x_38 = l_Lean_PersistentArray_get_x21___redArg(x_36, x_32, x_37);
lean_dec(x_37);
x_39 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_33, x_5, x_38);
lean_ctor_set(x_18, 2, x_3);
lean_ctor_set(x_18, 0, x_39);
x_21 = x_18;
goto block_30;
}
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_18, 2);
x_41 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
x_42 = lean_ctor_get(x_18, 0);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_18);
x_44 = lean_ctor_get(x_40, 2);
lean_inc(x_44);
x_45 = lean_nat_dec_lt(x_2, x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_5);
x_46 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_3);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_41);
x_21 = x_46;
goto block_30;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = l_Lean_Elab_instInhabitedInfoTree;
x_48 = lean_nat_sub(x_44, x_4);
lean_dec(x_44);
x_49 = l_Lean_PersistentArray_get_x21___redArg(x_47, x_40, x_48);
lean_dec(x_48);
x_50 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_42, x_5, x_49);
x_51 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
lean_ctor_set(x_51, 2, x_3);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_41);
x_21 = x_51;
goto block_30;
}
}
block_30:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 9, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
lean_ctor_set(x_22, 5, x_16);
lean_ctor_set(x_22, 6, x_17);
lean_ctor_set(x_22, 7, x_21);
lean_ctor_set(x_22, 8, x_19);
x_23 = lean_st_ref_set(x_1, x_22, x_10);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lam__9), 11, 1);
lean_closure_set(x_15, 0, x_13);
x_16 = l_Lean_Elab_withInfoTreeContext___at___Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__12(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lam__9), 11, 1);
lean_closure_set(x_15, 0, x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_Elab_withInfoTreeContext___at___Lean_Elab_Tactic_evalTactic_eval_spec__5___redArg(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(1);
x_19 = lean_box(1);
x_20 = lean_box(0);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lam__12___boxed), 11, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_unbox(x_18);
x_23 = l_Lean_Elab_Term_withoutTacticIncrementality___at___Lean_Elab_Tactic_evalTactic_eval_spec__7___redArg(x_22, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
return x_23;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_runTactic___lam__13___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsolved goals\n", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_runTactic___lam__13___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_runTactic___lam__13___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__13(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_35; lean_object* x_36; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; uint8_t x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_281; lean_object* x_282; 
x_253 = lean_st_ref_get(x_13, x_14);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec(x_254);
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_256);
lean_dec(x_253);
x_257 = lean_ctor_get_uint8(x_255, sizeof(void*)*8);
lean_dec(x_255);
if (x_257 == 0)
{
lean_dec(x_7);
x_281 = x_257;
x_282 = x_256;
goto block_299;
}
else
{
lean_object* x_300; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_300 = l_Lean_MVarId_withContext___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__5___redArg(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_256);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_unbox(x_301);
lean_dec(x_301);
x_281 = x_303;
x_282 = x_302;
goto block_299;
}
else
{
uint8_t x_304; 
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
lean_dec(x_1);
x_304 = !lean_is_exclusive(x_300);
if (x_304 == 0)
{
return x_300;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_300, 0);
x_306 = lean_ctor_get(x_300, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_300);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
return x_307;
}
}
}
block_24:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_apply_2(x_15, x_18, x_17);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_16);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_dec(x_16);
return x_19;
}
}
block_34:
{
lean_object* x_28; lean_object* x_29; 
lean_inc(x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_apply_2(x_25, x_28, x_27);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_26);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_dec(x_26);
return x_29;
}
}
block_41:
{
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_25 = x_35;
x_26 = x_37;
x_27 = x_38;
goto block_34;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_15 = x_35;
x_16 = x_39;
x_17 = x_40;
goto block_24;
}
}
block_59:
{
uint8_t x_52; 
x_52 = l_Lean_Exception_isInterrupt(x_50);
if (x_52 == 0)
{
if (x_3 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_5);
lean_dec(x_4);
x_53 = lean_box(0);
x_54 = l_Lean_Elab_Term_runTactic___lam__6(x_3, x_50, x_42, x_53, x_43, x_49, x_47, x_46, x_44, x_48, x_51);
lean_dec(x_49);
lean_dec(x_43);
x_35 = x_45;
x_36 = x_54;
goto block_41;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_inc(x_44);
x_55 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError(x_4, x_5, x_43, x_49, x_47, x_46, x_44, x_48, x_51);
lean_dec(x_4);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Elab_Term_runTactic___lam__6(x_3, x_50, x_42, x_56, x_43, x_49, x_47, x_46, x_44, x_48, x_57);
lean_dec(x_49);
lean_dec(x_43);
lean_dec(x_56);
x_35 = x_45;
x_36 = x_58;
goto block_41;
}
}
else
{
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
x_15 = x_45;
x_16 = x_50;
x_17 = x_51;
goto block_24;
}
}
block_73:
{
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_5);
lean_dec(x_4);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_25 = x_63;
x_26 = x_69;
x_27 = x_70;
goto block_34;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_dec(x_68);
x_42 = x_60;
x_43 = x_61;
x_44 = x_62;
x_45 = x_63;
x_46 = x_64;
x_47 = x_65;
x_48 = x_67;
x_49 = x_66;
x_50 = x_71;
x_51 = x_72;
goto block_59;
}
}
block_100:
{
uint8_t x_85; 
x_85 = l_List_isEmpty___redArg(x_83);
if (x_85 == 0)
{
if (x_3 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_77);
x_86 = l_Lean_Elab_Term_runTactic___lam__13___closed__1;
x_87 = l_Lean_Elab_goalsToMessageData(x_83);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10;
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
lean_inc(x_75);
x_91 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_90, x_75, x_82, x_80, x_79, x_76, x_81, x_84);
x_60 = x_74;
x_61 = x_75;
x_62 = x_76;
x_63 = x_78;
x_64 = x_79;
x_65 = x_80;
x_66 = x_82;
x_67 = x_81;
x_68 = x_91;
goto block_73;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_inc(x_76);
lean_inc(x_5);
x_92 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError(x_4, x_5, x_75, x_82, x_80, x_79, x_76, x_81, x_84);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
lean_inc(x_81);
lean_inc(x_76);
lean_inc(x_79);
lean_inc(x_80);
x_94 = l_Lean_Elab_Term_reportUnsolvedGoals(x_83, x_80, x_79, x_76, x_81, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
lean_inc(x_81);
lean_inc(x_76);
lean_inc(x_79);
lean_inc(x_80);
lean_inc(x_82);
lean_inc(x_75);
x_97 = lean_apply_8(x_77, x_95, x_75, x_82, x_80, x_79, x_76, x_81, x_96);
x_60 = x_74;
x_61 = x_75;
x_62 = x_76;
x_63 = x_78;
x_64 = x_79;
x_65 = x_80;
x_66 = x_82;
x_67 = x_81;
x_68 = x_97;
goto block_73;
}
else
{
lean_dec(x_77);
x_60 = x_74;
x_61 = x_75;
x_62 = x_76;
x_63 = x_78;
x_64 = x_79;
x_65 = x_80;
x_66 = x_82;
x_67 = x_81;
x_68 = x_94;
goto block_73;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_83);
x_98 = lean_box(0);
lean_inc(x_81);
lean_inc(x_76);
lean_inc(x_79);
lean_inc(x_80);
lean_inc(x_82);
lean_inc(x_75);
x_99 = lean_apply_8(x_77, x_98, x_75, x_82, x_80, x_79, x_76, x_81, x_84);
x_60 = x_74;
x_61 = x_75;
x_62 = x_76;
x_63 = x_78;
x_64 = x_79;
x_65 = x_80;
x_66 = x_82;
x_67 = x_81;
x_68 = x_99;
goto block_73;
}
}
block_252:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_114 = lean_st_ref_get(x_109, x_108);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_st_ref_take(x_109, x_116);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = !lean_is_exclusive(x_118);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_121 = lean_ctor_get(x_118, 0);
x_122 = lean_ctor_get(x_118, 5);
lean_dec(x_122);
x_123 = l_Lean_Environment_setExporting(x_121, x_113);
x_124 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__2;
lean_ctor_set(x_118, 5, x_124);
lean_ctor_set(x_118, 0, x_123);
x_125 = lean_st_ref_set(x_109, x_118, x_119);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_st_ref_take(x_111, x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = !lean_is_exclusive(x_128);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; 
x_131 = lean_ctor_get(x_128, 1);
lean_dec(x_131);
x_132 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__7;
lean_ctor_set(x_128, 1, x_132);
x_133 = lean_st_ref_set(x_111, x_128, x_129);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_st_ref_get(x_109, x_134);
x_136 = lean_ctor_get(x_115, 0);
lean_inc(x_136);
lean_dec(x_115);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 7);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_ctor_get(x_135, 1);
lean_inc(x_139);
lean_dec(x_135);
x_140 = lean_ctor_get_uint8(x_136, sizeof(void*)*8);
lean_dec(x_136);
x_141 = lean_ctor_get_uint8(x_138, sizeof(void*)*3);
lean_dec(x_138);
x_142 = lean_box(x_140);
lean_inc(x_111);
lean_inc(x_109);
x_143 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lam__7___boxed), 7, 5);
lean_closure_set(x_143, 0, x_109);
lean_closure_set(x_143, 1, x_142);
lean_closure_set(x_143, 2, x_124);
lean_closure_set(x_143, 3, x_111);
lean_closure_set(x_143, 4, x_132);
if (x_141 == 0)
{
lean_object* x_144; 
lean_dec(x_105);
lean_dec(x_1);
lean_inc(x_109);
lean_inc(x_107);
lean_inc(x_111);
lean_inc(x_104);
lean_inc(x_101);
lean_inc(x_103);
lean_inc(x_106);
x_144 = l_Lean_Elab_Tactic_run(x_106, x_112, x_103, x_101, x_104, x_111, x_107, x_109, x_139);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_74 = x_106;
x_75 = x_103;
x_76 = x_107;
x_77 = x_102;
x_78 = x_143;
x_79 = x_111;
x_80 = x_104;
x_81 = x_109;
x_82 = x_101;
x_83 = x_145;
x_84 = x_146;
goto block_100;
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_102);
x_147 = lean_ctor_get(x_144, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
lean_dec(x_144);
x_42 = x_106;
x_43 = x_103;
x_44 = x_107;
x_45 = x_143;
x_46 = x_111;
x_47 = x_104;
x_48 = x_109;
x_49 = x_101;
x_50 = x_147;
x_51 = x_148;
goto block_59;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = l_Lean_Elab_getResetInfoTrees___at_____private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___Lean_Elab_withSaveParentDeclInfoContext___at___Lean_Elab_Term_withDeclName_spec__1_spec__1_spec__1___redArg(x_109, x_139);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
lean_inc(x_109);
lean_inc(x_107);
lean_inc(x_111);
lean_inc(x_104);
lean_inc(x_101);
lean_inc(x_103);
lean_inc(x_106);
x_152 = l_Lean_Elab_Tactic_run(x_106, x_112, x_103, x_101, x_104, x_111, x_107, x_109, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
lean_inc(x_153);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_153);
x_156 = l_Lean_Elab_Term_runTactic___lam__8(x_109, x_110, x_150, x_105, x_1, x_155, x_154);
lean_dec(x_155);
lean_dec(x_105);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_74 = x_106;
x_75 = x_103;
x_76 = x_107;
x_77 = x_102;
x_78 = x_143;
x_79 = x_111;
x_80 = x_104;
x_81 = x_109;
x_82 = x_101;
x_83 = x_153;
x_84 = x_157;
goto block_100;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_102);
x_158 = lean_ctor_get(x_152, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_152, 1);
lean_inc(x_159);
lean_dec(x_152);
x_160 = lean_box(0);
x_161 = l_Lean_Elab_Term_runTactic___lam__8(x_109, x_110, x_150, x_105, x_1, x_160, x_159);
lean_dec(x_105);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_42 = x_106;
x_43 = x_103;
x_44 = x_107;
x_45 = x_143;
x_46 = x_111;
x_47 = x_104;
x_48 = x_109;
x_49 = x_101;
x_50 = x_158;
x_51 = x_162;
goto block_59;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; 
x_163 = lean_ctor_get(x_128, 0);
x_164 = lean_ctor_get(x_128, 2);
x_165 = lean_ctor_get(x_128, 3);
x_166 = lean_ctor_get(x_128, 4);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_128);
x_167 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__7;
x_168 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_168, 0, x_163);
lean_ctor_set(x_168, 1, x_167);
lean_ctor_set(x_168, 2, x_164);
lean_ctor_set(x_168, 3, x_165);
lean_ctor_set(x_168, 4, x_166);
x_169 = lean_st_ref_set(x_111, x_168, x_129);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_171 = lean_st_ref_get(x_109, x_170);
x_172 = lean_ctor_get(x_115, 0);
lean_inc(x_172);
lean_dec(x_115);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_173, 7);
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
lean_dec(x_171);
x_176 = lean_ctor_get_uint8(x_172, sizeof(void*)*8);
lean_dec(x_172);
x_177 = lean_ctor_get_uint8(x_174, sizeof(void*)*3);
lean_dec(x_174);
x_178 = lean_box(x_176);
lean_inc(x_111);
lean_inc(x_109);
x_179 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lam__7___boxed), 7, 5);
lean_closure_set(x_179, 0, x_109);
lean_closure_set(x_179, 1, x_178);
lean_closure_set(x_179, 2, x_124);
lean_closure_set(x_179, 3, x_111);
lean_closure_set(x_179, 4, x_167);
if (x_177 == 0)
{
lean_object* x_180; 
lean_dec(x_105);
lean_dec(x_1);
lean_inc(x_109);
lean_inc(x_107);
lean_inc(x_111);
lean_inc(x_104);
lean_inc(x_101);
lean_inc(x_103);
lean_inc(x_106);
x_180 = l_Lean_Elab_Tactic_run(x_106, x_112, x_103, x_101, x_104, x_111, x_107, x_109, x_175);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_74 = x_106;
x_75 = x_103;
x_76 = x_107;
x_77 = x_102;
x_78 = x_179;
x_79 = x_111;
x_80 = x_104;
x_81 = x_109;
x_82 = x_101;
x_83 = x_181;
x_84 = x_182;
goto block_100;
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_102);
x_183 = lean_ctor_get(x_180, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_180, 1);
lean_inc(x_184);
lean_dec(x_180);
x_42 = x_106;
x_43 = x_103;
x_44 = x_107;
x_45 = x_179;
x_46 = x_111;
x_47 = x_104;
x_48 = x_109;
x_49 = x_101;
x_50 = x_183;
x_51 = x_184;
goto block_59;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = l_Lean_Elab_getResetInfoTrees___at_____private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___Lean_Elab_withSaveParentDeclInfoContext___at___Lean_Elab_Term_withDeclName_spec__1_spec__1_spec__1___redArg(x_109, x_175);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
lean_inc(x_109);
lean_inc(x_107);
lean_inc(x_111);
lean_inc(x_104);
lean_inc(x_101);
lean_inc(x_103);
lean_inc(x_106);
x_188 = l_Lean_Elab_Tactic_run(x_106, x_112, x_103, x_101, x_104, x_111, x_107, x_109, x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
lean_inc(x_189);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_189);
x_192 = l_Lean_Elab_Term_runTactic___lam__8(x_109, x_110, x_186, x_105, x_1, x_191, x_190);
lean_dec(x_191);
lean_dec(x_105);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_74 = x_106;
x_75 = x_103;
x_76 = x_107;
x_77 = x_102;
x_78 = x_179;
x_79 = x_111;
x_80 = x_104;
x_81 = x_109;
x_82 = x_101;
x_83 = x_189;
x_84 = x_193;
goto block_100;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_102);
x_194 = lean_ctor_get(x_188, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 1);
lean_inc(x_195);
lean_dec(x_188);
x_196 = lean_box(0);
x_197 = l_Lean_Elab_Term_runTactic___lam__8(x_109, x_110, x_186, x_105, x_1, x_196, x_195);
lean_dec(x_105);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_42 = x_106;
x_43 = x_103;
x_44 = x_107;
x_45 = x_179;
x_46 = x_111;
x_47 = x_104;
x_48 = x_109;
x_49 = x_101;
x_50 = x_194;
x_51 = x_198;
goto block_59;
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; 
x_199 = lean_ctor_get(x_118, 0);
x_200 = lean_ctor_get(x_118, 1);
x_201 = lean_ctor_get(x_118, 2);
x_202 = lean_ctor_get(x_118, 3);
x_203 = lean_ctor_get(x_118, 4);
x_204 = lean_ctor_get(x_118, 6);
x_205 = lean_ctor_get(x_118, 7);
x_206 = lean_ctor_get(x_118, 8);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_118);
x_207 = l_Lean_Environment_setExporting(x_199, x_113);
x_208 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__2;
x_209 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_200);
lean_ctor_set(x_209, 2, x_201);
lean_ctor_set(x_209, 3, x_202);
lean_ctor_set(x_209, 4, x_203);
lean_ctor_set(x_209, 5, x_208);
lean_ctor_set(x_209, 6, x_204);
lean_ctor_set(x_209, 7, x_205);
lean_ctor_set(x_209, 8, x_206);
x_210 = lean_st_ref_set(x_109, x_209, x_119);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_st_ref_take(x_111, x_211);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_ctor_get(x_213, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_213, 2);
lean_inc(x_216);
x_217 = lean_ctor_get(x_213, 3);
lean_inc(x_217);
x_218 = lean_ctor_get(x_213, 4);
lean_inc(x_218);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 lean_ctor_release(x_213, 4);
 x_219 = x_213;
} else {
 lean_dec_ref(x_213);
 x_219 = lean_box(0);
}
x_220 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__7;
if (lean_is_scalar(x_219)) {
 x_221 = lean_alloc_ctor(0, 5, 0);
} else {
 x_221 = x_219;
}
lean_ctor_set(x_221, 0, x_215);
lean_ctor_set(x_221, 1, x_220);
lean_ctor_set(x_221, 2, x_216);
lean_ctor_set(x_221, 3, x_217);
lean_ctor_set(x_221, 4, x_218);
x_222 = lean_st_ref_set(x_111, x_221, x_214);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_st_ref_get(x_109, x_223);
x_225 = lean_ctor_get(x_115, 0);
lean_inc(x_225);
lean_dec(x_115);
x_226 = lean_ctor_get(x_224, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_226, 7);
lean_inc(x_227);
lean_dec(x_226);
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
lean_dec(x_224);
x_229 = lean_ctor_get_uint8(x_225, sizeof(void*)*8);
lean_dec(x_225);
x_230 = lean_ctor_get_uint8(x_227, sizeof(void*)*3);
lean_dec(x_227);
x_231 = lean_box(x_229);
lean_inc(x_111);
lean_inc(x_109);
x_232 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lam__7___boxed), 7, 5);
lean_closure_set(x_232, 0, x_109);
lean_closure_set(x_232, 1, x_231);
lean_closure_set(x_232, 2, x_208);
lean_closure_set(x_232, 3, x_111);
lean_closure_set(x_232, 4, x_220);
if (x_230 == 0)
{
lean_object* x_233; 
lean_dec(x_105);
lean_dec(x_1);
lean_inc(x_109);
lean_inc(x_107);
lean_inc(x_111);
lean_inc(x_104);
lean_inc(x_101);
lean_inc(x_103);
lean_inc(x_106);
x_233 = l_Lean_Elab_Tactic_run(x_106, x_112, x_103, x_101, x_104, x_111, x_107, x_109, x_228);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_74 = x_106;
x_75 = x_103;
x_76 = x_107;
x_77 = x_102;
x_78 = x_232;
x_79 = x_111;
x_80 = x_104;
x_81 = x_109;
x_82 = x_101;
x_83 = x_234;
x_84 = x_235;
goto block_100;
}
else
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_102);
x_236 = lean_ctor_get(x_233, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_233, 1);
lean_inc(x_237);
lean_dec(x_233);
x_42 = x_106;
x_43 = x_103;
x_44 = x_107;
x_45 = x_232;
x_46 = x_111;
x_47 = x_104;
x_48 = x_109;
x_49 = x_101;
x_50 = x_236;
x_51 = x_237;
goto block_59;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_238 = l_Lean_Elab_getResetInfoTrees___at_____private_Lean_Elab_InfoTree_Main_0__Lean_Elab_withSavedPartialInfoContext___at___Lean_Elab_withSaveParentDeclInfoContext___at___Lean_Elab_Term_withDeclName_spec__1_spec__1_spec__1___redArg(x_109, x_228);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
lean_inc(x_109);
lean_inc(x_107);
lean_inc(x_111);
lean_inc(x_104);
lean_inc(x_101);
lean_inc(x_103);
lean_inc(x_106);
x_241 = l_Lean_Elab_Tactic_run(x_106, x_112, x_103, x_101, x_104, x_111, x_107, x_109, x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
lean_inc(x_242);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_242);
x_245 = l_Lean_Elab_Term_runTactic___lam__8(x_109, x_110, x_239, x_105, x_1, x_244, x_243);
lean_dec(x_244);
lean_dec(x_105);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
lean_dec(x_245);
x_74 = x_106;
x_75 = x_103;
x_76 = x_107;
x_77 = x_102;
x_78 = x_232;
x_79 = x_111;
x_80 = x_104;
x_81 = x_109;
x_82 = x_101;
x_83 = x_242;
x_84 = x_246;
goto block_100;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_102);
x_247 = lean_ctor_get(x_241, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_241, 1);
lean_inc(x_248);
lean_dec(x_241);
x_249 = lean_box(0);
x_250 = l_Lean_Elab_Term_runTactic___lam__8(x_109, x_110, x_239, x_105, x_1, x_249, x_248);
lean_dec(x_105);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
lean_dec(x_250);
x_42 = x_106;
x_43 = x_103;
x_44 = x_107;
x_45 = x_232;
x_46 = x_111;
x_47 = x_104;
x_48 = x_109;
x_49 = x_101;
x_50 = x_247;
x_51 = x_251;
goto block_59;
}
}
}
}
block_280:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_268 = lean_box(x_258);
x_269 = lean_box(x_257);
lean_inc(x_1);
lean_inc(x_260);
x_270 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lam__5___boxed), 13, 5);
lean_closure_set(x_270, 0, x_268);
lean_closure_set(x_270, 1, x_260);
lean_closure_set(x_270, 2, x_269);
lean_closure_set(x_270, 3, x_2);
lean_closure_set(x_270, 4, x_1);
x_271 = lean_unsigned_to_nat(0u);
x_272 = l_Lean_Syntax_getArg(x_4, x_271);
x_273 = lean_unsigned_to_nat(1u);
lean_inc(x_4);
x_274 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2), 13, 4);
lean_closure_set(x_274, 0, lean_box(0));
lean_closure_set(x_274, 1, x_273);
lean_closure_set(x_274, 2, x_6);
lean_closure_set(x_274, 3, x_4);
x_275 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lam__10), 11, 2);
lean_closure_set(x_275, 0, x_272);
lean_closure_set(x_275, 1, x_274);
lean_inc(x_4);
x_276 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lam__11), 11, 2);
lean_closure_set(x_276, 0, x_4);
lean_closure_set(x_276, 1, x_275);
lean_inc(x_5);
x_277 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___boxed), 12, 3);
lean_closure_set(x_277, 0, lean_box(0));
lean_closure_set(x_277, 1, x_5);
lean_closure_set(x_277, 2, x_276);
if (x_257 == 0)
{
x_101 = x_262;
x_102 = x_270;
x_103 = x_261;
x_104 = x_263;
x_105 = x_273;
x_106 = x_260;
x_107 = x_265;
x_108 = x_267;
x_109 = x_266;
x_110 = x_271;
x_111 = x_264;
x_112 = x_277;
x_113 = x_257;
goto block_252;
}
else
{
if (x_259 == 0)
{
x_101 = x_262;
x_102 = x_270;
x_103 = x_261;
x_104 = x_263;
x_105 = x_273;
x_106 = x_260;
x_107 = x_265;
x_108 = x_267;
x_109 = x_266;
x_110 = x_271;
x_111 = x_264;
x_112 = x_277;
x_113 = x_257;
goto block_252;
}
else
{
lean_object* x_278; uint8_t x_279; 
x_278 = lean_box(0);
x_279 = lean_unbox(x_278);
x_101 = x_262;
x_102 = x_270;
x_103 = x_261;
x_104 = x_263;
x_105 = x_273;
x_106 = x_260;
x_107 = x_265;
x_108 = x_267;
x_109 = x_266;
x_110 = x_271;
x_111 = x_264;
x_112 = x_277;
x_113 = x_279;
goto block_252;
}
}
}
block_299:
{
lean_object* x_283; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_283 = l_Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_282);
if (lean_obj_tag(x_283) == 0)
{
if (x_281 == 0)
{
lean_object* x_284; 
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
lean_dec(x_283);
lean_inc(x_1);
x_258 = x_281;
x_259 = x_281;
x_260 = x_1;
x_261 = x_8;
x_262 = x_9;
x_263 = x_10;
x_264 = x_11;
x_265 = x_12;
x_266 = x_13;
x_267 = x_284;
goto block_280;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
lean_inc(x_1);
x_286 = l_Lean_Elab_Term_getMVarDecl___redArg(x_1, x_11, x_285);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
x_290 = lean_ctor_get(x_287, 2);
lean_inc(x_290);
x_291 = lean_ctor_get(x_287, 4);
lean_inc(x_291);
x_292 = lean_ctor_get_uint8(x_287, sizeof(void*)*7);
lean_dec(x_287);
x_293 = lean_box(0);
x_294 = lean_unsigned_to_nat(0u);
x_295 = l_Lean_Meta_mkFreshExprMVarAt(x_289, x_291, x_290, x_292, x_293, x_294, x_10, x_11, x_12, x_13, x_288);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = l_Lean_Expr_mvarId_x21(x_296);
lean_dec(x_296);
x_258 = x_281;
x_259 = x_281;
x_260 = x_298;
x_261 = x_8;
x_262 = x_9;
x_263 = x_10;
x_264 = x_11;
x_265 = x_12;
x_266 = x_13;
x_267 = x_297;
goto block_280;
}
}
else
{
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
lean_dec(x_1);
return x_283;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lam__0), 10, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lam__1___boxed), 8, 0);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lam__2___boxed), 8, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_box(x_4);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lam__13___boxed), 14, 7);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_13);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_2);
lean_closure_set(x_16, 4, x_3);
lean_closure_set(x_16, 5, x_12);
lean_closure_set(x_16, 6, x_14);
x_17 = l_Lean_Elab_Term_withoutAutoBoundImplicit___redArg(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_box(0);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; 
lean_free_object(x_10);
x_18 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_processPostponedUniverseConstraints(x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(1);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(x_1, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_processPostponedUniverseConstraints(x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_25;
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
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___redArg(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
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
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0(x_1, x_4, x_3);
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
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateExprMVars___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateExprMVars___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateExprMVars___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lam__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lam__1(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
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
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___lam__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runTactic_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runTactic_spec__5___redArg(x_12, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runTactic_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runTactic_spec__5(x_14, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__7(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_runTactic___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_runTactic___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Elab_Term_runTactic___lam__3(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Elab_Term_runTactic___lam__4(x_12, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Elab_Term_runTactic___lam__5(x_14, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Elab_Term_runTactic___lam__6(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Elab_Term_runTactic___lam__7(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_runTactic___lam__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Elab_Term_runTactic___lam__12(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lam__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Elab_Term_runTactic___lam__13(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
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
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_20 = lean_unbox(x_18);
x_21 = lean_unbox(x_19);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_20, x_21, x_1, x_2, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_7 = x_23;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = lean_unbox(x_8);
x_11 = lean_unbox(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_10, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 2);
x_10 = l_List_appendTR___redArg(x_9, x_2);
lean_ctor_set(x_6, 2, x_10);
x_11 = lean_st_ref_set(x_1, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_25 = l_List_appendTR___redArg(x_20, x_2);
x_26 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_19);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set(x_26, 4, x_22);
lean_ctor_set(x_26, 5, x_23);
lean_ctor_set(x_26, 6, x_24);
x_27 = lean_st_ref_set(x_1, x_26, x_7);
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
x_30 = lean_box(0);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_31; lean_object* x_43; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 2, x_18);
x_19 = lean_st_ref_set(x_4, x_14, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_11, 2);
lean_inc(x_21);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_43 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_box(0);
x_47 = lean_unbox(x_46);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_48 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_2, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_box(0);
x_51 = lean_unbox(x_50);
x_52 = l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(x_2, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_box(0);
x_54 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__1(x_44, x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_31 = x_54;
goto block_42;
}
else
{
lean_object* x_55; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_55 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultLoop(x_3, x_4, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__1(x_44, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_57);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_56);
x_31 = x_58;
goto block_42;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_dec(x_55);
x_22 = x_59;
x_23 = x_60;
goto block_30;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_61 = lean_ctor_get(x_48, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
lean_dec(x_48);
x_22 = x_61;
x_23 = x_62;
goto block_30;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_63 = lean_ctor_get(x_43, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_43, 1);
lean_inc(x_64);
lean_dec(x_43);
x_22 = x_63;
x_23 = x_64;
goto block_30;
}
block_30:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_box(0);
x_25 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__0(x_4, x_21, x_24, x_23);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 0, x_22);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
block_42:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_32);
x_35 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__0(x_4, x_21, x_34, x_33);
lean_dec(x_34);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_84; lean_object* x_94; 
x_65 = lean_ctor_get(x_14, 0);
x_66 = lean_ctor_get(x_14, 1);
x_67 = lean_ctor_get(x_14, 3);
x_68 = lean_ctor_get(x_14, 4);
x_69 = lean_ctor_get(x_14, 5);
x_70 = lean_ctor_get(x_14, 6);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_14);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_72, 0, x_65);
lean_ctor_set(x_72, 1, x_66);
lean_ctor_set(x_72, 2, x_71);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set(x_72, 4, x_68);
lean_ctor_set(x_72, 5, x_69);
lean_ctor_set(x_72, 6, x_70);
x_73 = lean_st_ref_set(x_4, x_72, x_15);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_ctor_get(x_11, 2);
lean_inc(x_75);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_94 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_box(0);
x_98 = lean_unbox(x_97);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_99 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_2, x_98, x_3, x_4, x_5, x_6, x_7, x_8, x_96);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_box(0);
x_102 = lean_unbox(x_101);
x_103 = l_Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4273_(x_2, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_box(0);
x_105 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__1(x_95, x_104, x_3, x_4, x_5, x_6, x_7, x_8, x_100);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_84 = x_105;
goto block_93;
}
else
{
lean_object* x_106; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_106 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultLoop(x_3, x_4, x_5, x_6, x_7, x_8, x_100);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__1(x_95, x_107, x_3, x_4, x_5, x_6, x_7, x_8, x_108);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_107);
x_84 = x_109;
goto block_93;
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_95);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_110 = lean_ctor_get(x_106, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_dec(x_106);
x_76 = x_110;
x_77 = x_111;
goto block_83;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_95);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_112 = lean_ctor_get(x_99, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_99, 1);
lean_inc(x_113);
lean_dec(x_99);
x_76 = x_112;
x_77 = x_113;
goto block_83;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_114 = lean_ctor_get(x_94, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_94, 1);
lean_inc(x_115);
lean_dec(x_94);
x_76 = x_114;
x_77 = x_115;
goto block_83;
}
block_83:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_box(0);
x_79 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__0(x_4, x_75, x_78, x_77);
lean_dec(x_4);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
block_93:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_85);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_85);
x_88 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__0(x_4, x_75, x_87, x_86);
lean_dec(x_87);
lean_dec(x_4);
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
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
lean_dec(x_85);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withSynthesize___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_apply_3(x_1, lean_box(0), x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withSynthesize___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_apply_3(x_3, lean_box(0), x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_withSynthesize___redArg___lam__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Elab_Term_withSynthesize___redArg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_Elab_Term_withSynthesize(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_30; 
x_16 = lean_ctor_get(x_13, 2);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 2, x_17);
x_18 = lean_st_ref_set(x_3, x_13, x_14);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_10, 2);
lean_inc(x_20);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_30 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = lean_unbox(x_33);
x_36 = lean_unbox(x_34);
lean_inc(x_3);
x_37 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_35, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_37, 1);
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_inc(x_31);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 1, x_41);
lean_ctor_set(x_37, 0, x_31);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_43 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__0(x_3, x_20, x_42, x_39);
lean_dec(x_42);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_31);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_31);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_dec(x_37);
x_49 = lean_box(0);
lean_inc(x_31);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_31);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__0(x_3, x_20, x_51, x_48);
lean_dec(x_51);
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
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_31);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_31);
x_56 = lean_ctor_get(x_37, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_37, 1);
lean_inc(x_57);
lean_dec(x_37);
x_21 = x_56;
x_22 = x_57;
goto block_29;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_58 = lean_ctor_get(x_30, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_30, 1);
lean_inc(x_59);
lean_dec(x_30);
x_21 = x_58;
x_22 = x_59;
goto block_29;
}
block_29:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_box(0);
x_24 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__0(x_3, x_20, x_23, x_22);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_21);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_79; 
x_60 = lean_ctor_get(x_13, 0);
x_61 = lean_ctor_get(x_13, 1);
x_62 = lean_ctor_get(x_13, 3);
x_63 = lean_ctor_get(x_13, 4);
x_64 = lean_ctor_get(x_13, 5);
x_65 = lean_ctor_get(x_13, 6);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_13);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_61);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_62);
lean_ctor_set(x_67, 4, x_63);
lean_ctor_set(x_67, 5, x_64);
lean_ctor_set(x_67, 6, x_65);
x_68 = lean_st_ref_set(x_3, x_67, x_14);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_ctor_get(x_10, 2);
lean_inc(x_70);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_79 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_69);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_85; lean_object* x_86; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_box(0);
x_83 = lean_box(0);
x_84 = lean_unbox(x_82);
x_85 = lean_unbox(x_83);
lean_inc(x_3);
x_86 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_84, x_85, x_2, x_3, x_4, x_5, x_6, x_7, x_81);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = lean_box(0);
lean_inc(x_80);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_88;
 lean_ctor_set_tag(x_90, 1);
}
lean_ctor_set(x_90, 0, x_80);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__0(x_3, x_70, x_91, x_87);
lean_dec(x_91);
lean_dec(x_3);
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
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_80);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_80);
x_96 = lean_ctor_get(x_86, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_86, 1);
lean_inc(x_97);
lean_dec(x_86);
x_71 = x_96;
x_72 = x_97;
goto block_78;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_98 = lean_ctor_get(x_79, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_79, 1);
lean_inc(x_99);
lean_dec(x_79);
x_71 = x_98;
x_72 = x_99;
goto block_78;
}
block_78:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_box(0);
x_74 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg___lam__0(x_3, x_70, x_73, x_72);
lean_dec(x_3);
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
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withSynthesizeLight___redArg___lam__0), 9, 0);
x_4 = lean_apply_3(x_1, lean_box(0), x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withSynthesizeLight___redArg___lam__0), 9, 0);
x_6 = lean_apply_3(x_3, lean_box(0), x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = lean_box(1);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_box(1);
x_15 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_dec(x_1);
lean_ctor_set(x_7, 5, x_15);
x_16 = lean_unbox(x_14);
lean_inc(x_6);
x_17 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(x_13, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_18, x_6, x_19);
lean_dec(x_6);
return x_20;
}
else
{
lean_dec(x_6);
return x_17;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
x_23 = lean_ctor_get(x_7, 2);
x_24 = lean_ctor_get(x_7, 3);
x_25 = lean_ctor_get(x_7, 4);
x_26 = lean_ctor_get(x_7, 5);
x_27 = lean_ctor_get(x_7, 6);
x_28 = lean_ctor_get(x_7, 7);
x_29 = lean_ctor_get(x_7, 8);
x_30 = lean_ctor_get(x_7, 9);
x_31 = lean_ctor_get(x_7, 10);
x_32 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_33 = lean_ctor_get(x_7, 11);
x_34 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_35 = lean_ctor_get(x_7, 12);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_31);
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
lean_dec(x_7);
x_36 = lean_box(1);
lean_inc(x_1);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_37, 0, x_1);
lean_closure_set(x_37, 1, x_2);
lean_closure_set(x_37, 2, x_36);
lean_closure_set(x_37, 3, x_36);
x_38 = lean_box(1);
x_39 = l_Lean_replaceRef(x_1, x_26);
lean_dec(x_26);
lean_dec(x_1);
x_40 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_40, 0, x_21);
lean_ctor_set(x_40, 1, x_22);
lean_ctor_set(x_40, 2, x_23);
lean_ctor_set(x_40, 3, x_24);
lean_ctor_set(x_40, 4, x_25);
lean_ctor_set(x_40, 5, x_39);
lean_ctor_set(x_40, 6, x_27);
lean_ctor_set(x_40, 7, x_28);
lean_ctor_set(x_40, 8, x_29);
lean_ctor_set(x_40, 9, x_30);
lean_ctor_set(x_40, 10, x_31);
lean_ctor_set(x_40, 11, x_33);
lean_ctor_set(x_40, 12, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*13, x_32);
lean_ctor_set_uint8(x_40, sizeof(void*)*13 + 1, x_34);
x_41 = lean_unbox(x_38);
lean_inc(x_6);
x_42 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___redArg(x_37, x_41, x_3, x_4, x_5, x_6, x_40, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_43, x_6, x_44);
lean_dec(x_6);
return x_45;
}
else
{
lean_dec(x_6);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runPendingTacticsAt_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_6);
lean_inc(x_1);
x_12 = l_Lean_Elab_Term_runTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___redArg(x_1, x_6, x_13);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
else
{
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runPendingTacticsAt_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_4, x_3);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_21 = lean_array_uget(x_2, x_4);
x_22 = l_Lean_getDelayedMVarRoot___at___Lean_Elab_Term_isLetRecAuxMVar_spec__0(x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Term_getSyntheticMVarDecl_x3f___redArg(x_23, x_7, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_23);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_1);
x_13 = x_1;
x_14 = x_27;
goto block_18;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 2)
{
uint8_t x_30; 
x_30 = lean_ctor_get_uint8(x_29, sizeof(void*)*3);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_29, 2);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_box(x_19);
x_36 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runPendingTacticsAt_spec__0___lam__0___boxed), 11, 4);
lean_closure_set(x_36, 0, x_23);
lean_closure_set(x_36, 1, x_32);
lean_closure_set(x_36, 2, x_34);
lean_closure_set(x_36, 3, x_35);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_37 = l_Lean_Elab_Term_withSavedContext___redArg(x_33, x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
lean_inc(x_1);
x_13 = x_1;
x_14 = x_38;
goto block_18;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_37;
}
}
else
{
lean_object* x_39; 
lean_dec(x_29);
lean_dec(x_23);
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_dec(x_25);
lean_inc(x_1);
x_13 = x_1;
x_14 = x_39;
goto block_18;
}
}
else
{
lean_object* x_40; 
lean_dec(x_29);
lean_dec(x_23);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
lean_inc(x_1);
x_13 = x_1;
x_14 = x_40;
goto block_18;
}
}
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_4 = x_16;
x_5 = x_13;
x_12 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runPendingTacticsAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_9 = l_Lean_Meta_getMVars(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_array_size(x_10);
x_14 = 0;
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runPendingTacticsAt_spec__0(x_12, x_10, x_13, x_14, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runPendingTacticsAt_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runPendingTacticsAt_spec__0___lam__0(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runPendingTacticsAt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_Term_runPendingTacticsAt_spec__0(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resume", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__0;
x_2 = l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__5____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__6____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn___closed__5____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_2 = l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__7____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__8____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn___closed__7____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_2 = l_Lean_Elab_Term_initFn___closed__6____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__9____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__10____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn___closed__9____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_2 = l_Lean_Elab_Term_initFn___closed__8____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__11____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_2 = l_Lean_Elab_Term_initFn___closed__10____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__12____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__0;
x_2 = l_Lean_Elab_Term_initFn___closed__11____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__13____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("SyntheticMVars", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__14____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn___closed__13____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_2 = l_Lean_Elab_Term_initFn___closed__12____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__15____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__16____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn___closed__15____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_2 = l_Lean_Elab_Term_initFn___closed__14____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn___closed__17____x40_Lean_Elab_SyntheticMVars___hyg_7474_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(7474u);
x_2 = l_Lean_Elab_Term_initFn___closed__16____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7474_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_3 = lean_box(0);
x_4 = l_Lean_Elab_Term_initFn___closed__17____x40_Lean_Elab_SyntheticMVars___hyg_7474_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_NumObjs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_OccursCheck(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AbstractNestedProofs(uint8_t builtin, lean_object*);
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
res = initialize_Lean_Meta_AbstractNestedProofs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__0 = _init_l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__0);
l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__1 = _init_l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_occursCheck_visitMVar___at___Lean_occursCheck_visit___at___Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0_spec__0_spec__0___closed__1);
l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__0 = _init_l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__0();
lean_mark_persistent(l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__0);
l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__1 = _init_l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__1();
lean_mark_persistent(l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__1);
l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__2 = _init_l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__2();
lean_mark_persistent(l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__2);
l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__3 = _init_l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__3();
lean_mark_persistent(l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__3);
l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__4 = _init_l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__4();
lean_mark_persistent(l_Lean_occursCheck___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_spec__0___closed__4);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__2___closed__0 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__2___closed__0();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lam__2___closed__0);
l_panic___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar_spec__0___closed__0 = _init_l_panic___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar_spec__0___closed__0();
lean_mark_persistent(l_panic___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar_spec__0___closed__0);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__0 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__0);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lam__0___closed__3);
l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg___closed__0 = _init_l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_getDefaultInstancesPriorities___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault_spec__0___redArg___closed__0);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__0 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__0();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__0);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__0 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__0);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__3);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__4 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__4);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__5 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__5);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__6 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__6();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__6);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__7 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__7();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__7);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__8 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__8();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__8);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__9 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__9();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__9);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__10);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__11 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__11();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__11);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__12 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__12();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lam__0___closed__12);
l_panic___at___Lean_Elab_Term_reportStuckSyntheticMVar_spec__0___closed__0 = _init_l_panic___at___Lean_Elab_Term_reportStuckSyntheticMVar_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_Elab_Term_reportStuckSyntheticMVar_spec__0___closed__0);
l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___closed__0 = _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___closed__0);
l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___closed__1 = _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__0___closed__1);
l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___closed__0 = _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___closed__0);
l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___closed__1 = _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportStuckSyntheticMVar___lam__2___closed__1);
l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__0 = _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__0);
l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__1 = _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___closed__0 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___closed__0();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___closed__0);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__0 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__0();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__0);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__4 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__4();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__4);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__5 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__5();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__5);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__6 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__6();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__6);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__7 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__7();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__7);
l_Lean_Elab_Term_instInhabitedPostponeBehavior = _init_l_Lean_Elab_Term_instInhabitedPostponeBehavior();
l_Lean_Elab_Term_reprPostponeBehavior___closed__0____x40_Lean_Elab_SyntheticMVars___hyg_4157_ = _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__0____x40_Lean_Elab_SyntheticMVars___hyg_4157_();
lean_mark_persistent(l_Lean_Elab_Term_reprPostponeBehavior___closed__0____x40_Lean_Elab_SyntheticMVars___hyg_4157_);
l_Lean_Elab_Term_reprPostponeBehavior___closed__1____x40_Lean_Elab_SyntheticMVars___hyg_4157_ = _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__1____x40_Lean_Elab_SyntheticMVars___hyg_4157_();
lean_mark_persistent(l_Lean_Elab_Term_reprPostponeBehavior___closed__1____x40_Lean_Elab_SyntheticMVars___hyg_4157_);
l_Lean_Elab_Term_reprPostponeBehavior___closed__2____x40_Lean_Elab_SyntheticMVars___hyg_4157_ = _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__2____x40_Lean_Elab_SyntheticMVars___hyg_4157_();
lean_mark_persistent(l_Lean_Elab_Term_reprPostponeBehavior___closed__2____x40_Lean_Elab_SyntheticMVars___hyg_4157_);
l_Lean_Elab_Term_reprPostponeBehavior___closed__3____x40_Lean_Elab_SyntheticMVars___hyg_4157_ = _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__3____x40_Lean_Elab_SyntheticMVars___hyg_4157_();
lean_mark_persistent(l_Lean_Elab_Term_reprPostponeBehavior___closed__3____x40_Lean_Elab_SyntheticMVars___hyg_4157_);
l_Lean_Elab_Term_reprPostponeBehavior___closed__4____x40_Lean_Elab_SyntheticMVars___hyg_4157_ = _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__4____x40_Lean_Elab_SyntheticMVars___hyg_4157_();
lean_mark_persistent(l_Lean_Elab_Term_reprPostponeBehavior___closed__4____x40_Lean_Elab_SyntheticMVars___hyg_4157_);
l_Lean_Elab_Term_reprPostponeBehavior___closed__5____x40_Lean_Elab_SyntheticMVars___hyg_4157_ = _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__5____x40_Lean_Elab_SyntheticMVars___hyg_4157_();
lean_mark_persistent(l_Lean_Elab_Term_reprPostponeBehavior___closed__5____x40_Lean_Elab_SyntheticMVars___hyg_4157_);
l_Lean_Elab_Term_reprPostponeBehavior___closed__6____x40_Lean_Elab_SyntheticMVars___hyg_4157_ = _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__6____x40_Lean_Elab_SyntheticMVars___hyg_4157_();
lean_mark_persistent(l_Lean_Elab_Term_reprPostponeBehavior___closed__6____x40_Lean_Elab_SyntheticMVars___hyg_4157_);
l_Lean_Elab_Term_reprPostponeBehavior___closed__7____x40_Lean_Elab_SyntheticMVars___hyg_4157_ = _init_l_Lean_Elab_Term_reprPostponeBehavior___closed__7____x40_Lean_Elab_SyntheticMVars___hyg_4157_();
lean_mark_persistent(l_Lean_Elab_Term_reprPostponeBehavior___closed__7____x40_Lean_Elab_SyntheticMVars___hyg_4157_);
l_Lean_Elab_Term_instReprPostponeBehavior___closed__0 = _init_l_Lean_Elab_Term_instReprPostponeBehavior___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_instReprPostponeBehavior___closed__0);
l_Lean_Elab_Term_instReprPostponeBehavior = _init_l_Lean_Elab_Term_instReprPostponeBehavior();
lean_mark_persistent(l_Lean_Elab_Term_instReprPostponeBehavior);
l_Lean_Elab_Term_instBEqPostponeBehavior___closed__0 = _init_l_Lean_Elab_Term_instBEqPostponeBehavior___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_instBEqPostponeBehavior___closed__0);
l_Lean_Elab_Term_instBEqPostponeBehavior = _init_l_Lean_Elab_Term_instBEqPostponeBehavior();
lean_mark_persistent(l_Lean_Elab_Term_instBEqPostponeBehavior);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__0 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__0();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__0);
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
l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__0 = _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__0();
lean_mark_persistent(l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__0);
l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__1 = _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__1();
lean_mark_persistent(l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__1);
l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__2 = _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__2();
lean_mark_persistent(l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__2);
l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__3 = _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__3();
lean_mark_persistent(l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__3);
l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__4 = _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__4();
lean_mark_persistent(l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__4);
l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__5 = _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__5();
lean_mark_persistent(l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__5);
l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__6 = _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__6();
lean_mark_persistent(l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__6);
l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__7 = _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__7();
lean_mark_persistent(l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__7);
l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__8 = _init_l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__8();
lean_mark_persistent(l_List_filterAuxM___at___List_filterAuxM___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep_spec__0_spec__0___closed__8);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__0 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__0);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__3);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__4 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__4);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__5 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lam__0___closed__5);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__0 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__0();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__0);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1);
l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__0);
l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__1);
l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__2 = _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__2);
l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__3 = _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__3);
l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__4 = _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__4();
lean_mark_persistent(l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__4);
l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__5 = _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__5();
lean_mark_persistent(l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__5);
l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__6 = _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__6();
lean_mark_persistent(l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__6);
l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__7 = _init_l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__7();
lean_mark_persistent(l_Lean_withoutExporting___at___Lean_Meta_abstractProof___at___Lean_Elab_Term_runTactic_spec__0_spec__0___redArg___closed__7);
l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__2___closed__0 = _init_l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__2___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_withNarrowedTacticReuse___at___Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2_spec__2___redArg___lam__2___closed__0);
l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0___closed__0 = _init_l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0___closed__0);
l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0___closed__1 = _init_l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at___Lean_Elab_Term_runTactic_spec__2___redArg___lam__0___closed__1);
l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__0 = _init_l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__0();
lean_mark_persistent(l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__0);
l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__1 = _init_l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__1();
lean_mark_persistent(l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__1);
l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__2 = _init_l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__2();
lean_mark_persistent(l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__2);
l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__3 = _init_l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__3();
lean_mark_persistent(l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__3);
l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__4 = _init_l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__4();
lean_mark_persistent(l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__4);
l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__5 = _init_l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__5();
lean_mark_persistent(l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__5);
l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__6 = _init_l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__6();
lean_mark_persistent(l_panic___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__6___closed__6);
l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__0 = _init_l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__0);
l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__1);
l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__2);
l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7_spec__7_spec__8___closed__3);
l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7___closed__0 = _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7___closed__0();
lean_mark_persistent(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at___Lean_LocalContext_foldlM___at___Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6_spec__7_spec__7_spec__7___closed__0);
l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__0 = _init_l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__0();
lean_mark_persistent(l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__0);
l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__1 = _init_l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__1();
lean_mark_persistent(l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__1);
l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__2 = _init_l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__2();
lean_mark_persistent(l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__2);
l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__3 = _init_l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__3();
lean_mark_persistent(l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__3);
l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__4 = _init_l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__4();
lean_mark_persistent(l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__4);
l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__5 = _init_l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__5();
lean_mark_persistent(l_Lean_instantiateLCtxMVars___at___Lean_instantiateMVarDeclMVars___at___Lean_Elab_Term_runTactic_spec__6_spec__6___closed__5);
l_Lean_Elab_Term_runTactic___lam__13___closed__0 = _init_l_Lean_Elab_Term_runTactic___lam__13___closed__0();
lean_mark_persistent(l_Lean_Elab_Term_runTactic___lam__13___closed__0);
l_Lean_Elab_Term_runTactic___lam__13___closed__1 = _init_l_Lean_Elab_Term_runTactic___lam__13___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_runTactic___lam__13___closed__1);
l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__0____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__1____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__2____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__3____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__4____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__5____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__5____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__5____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__6____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__6____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__6____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__7____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__7____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__7____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__8____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__8____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__8____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__9____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__9____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__9____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__10____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__10____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__10____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__11____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__11____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__11____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__12____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__12____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__12____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__13____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__13____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__13____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__14____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__14____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__14____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__15____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__15____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__15____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__16____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__16____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__16____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
l_Lean_Elab_Term_initFn___closed__17____x40_Lean_Elab_SyntheticMVars___hyg_7474_ = _init_l_Lean_Elab_Term_initFn___closed__17____x40_Lean_Elab_SyntheticMVars___hyg_7474_();
lean_mark_persistent(l_Lean_Elab_Term_initFn___closed__17____x40_Lean_Elab_SyntheticMVars___hyg_7474_);
if (builtin) {res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7474_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
