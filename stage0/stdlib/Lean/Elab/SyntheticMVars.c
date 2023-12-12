// Lean compiler output
// Module: Lean.Elab.SyntheticMVars
// Imports: Init Lean.Meta.Tactic.Util Lean.Util.ForEachExpr Lean.Util.OccursCheck Lean.Elab.Tactic.Basic
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
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__15;
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__20;
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_instantiateMVarDeclMVars___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Elab_Term_addTermInfo___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__6;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__5;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_reportStuckSyntheticMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2;
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__2;
static lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_Elab_Term_runTactic___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_hashset_mk_idx(lean_object*, uint64_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__2;
static lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__2;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__1;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1;
static lean_object* l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__1;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__5;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__22;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__2;
LEAN_EXPORT lean_object* l_List_elem___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___closed__1;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__1;
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_withSynthesizeLight___rarg___closed__1;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
static lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__5;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object*);
static lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__2;
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__5(lean_object*, lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__19;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_processPostponedUniverseContraints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__3(lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedInfoTree;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withSavedContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__7;
lean_object* l_Lean_Elab_Term_withoutPostponing___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__11;
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_appendTrees___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__14;
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runPendingTacticsAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__1;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstancesStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__13;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedPostponedEntry;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__2;
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__1;
extern uint8_t l_Lean_instInhabitedBinderInfo;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_traceAtCmdPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__5;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1;
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__15;
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedDefaultInstances;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
extern lean_object* l_Lean_Meta_defaultInstanceExtension;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__18;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__4;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__7;
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_instBEqLevel;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__8;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_Elab_Term_runTactic___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize(lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15___closed__1;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__16;
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__7;
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__2;
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__12;
lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeSomeUsingDefault_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runTactic___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658_(lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__3;
LEAN_EXPORT lean_object* l_List_replace___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__16;
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_coerce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__21;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__14;
lean_object* l_Lean_getDelayedMVarRoot___at_Lean_Elab_Term_isLetRecAuxMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__8;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isBlack___rarg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_postponeExceptionId;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__17;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__6;
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_getDelayedMVarAssignment_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__2;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runTactic___spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__3;
lean_object* l_Lean_logAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getSyntheticMVarDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1;
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__5;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__1;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Term_runTactic___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__1;
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__7;
lean_object* lean_expr_dbg_to_string(lean_object*);
uint8_t l_Lean_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Level_normLtAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__17;
lean_object* l_Lean_RBNode_find___at_Lean_Meta_addDefaultInstanceEntry___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
extern lean_object* l_Lean_Level_instHashableLevel;
lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPostponed___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstancesStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___at_Lean_Elab_Term_runTactic___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__1;
lean_object* l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4;
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__4;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__11;
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__9;
lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*8 + 1, x_13);
x_14 = 1;
x_15 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 2);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 2);
x_21 = lean_ctor_get(x_4, 3);
x_22 = lean_ctor_get(x_4, 4);
x_23 = lean_ctor_get(x_4, 5);
x_24 = lean_ctor_get(x_4, 6);
x_25 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 3);
x_26 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 4);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 5);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 6);
x_29 = lean_ctor_get(x_4, 7);
x_30 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 7);
x_31 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 8);
lean_inc(x_29);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_32 = 0;
x_33 = lean_alloc_ctor(0, 8, 9);
lean_ctor_set(x_33, 0, x_16);
lean_ctor_set(x_33, 1, x_17);
lean_ctor_set(x_33, 2, x_18);
lean_ctor_set(x_33, 3, x_21);
lean_ctor_set(x_33, 4, x_22);
lean_ctor_set(x_33, 5, x_23);
lean_ctor_set(x_33, 6, x_24);
lean_ctor_set(x_33, 7, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*8, x_19);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 1, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 2, x_20);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 3, x_25);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 4, x_26);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 5, x_27);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 6, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 7, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 8, x_31);
x_34 = 1;
x_35 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_32, x_34, x_33, x_5, x_6, x_7, x_8, x_9, x_10);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_4);
if (x_36 == 0)
{
uint8_t x_37; uint8_t x_38; lean_object* x_39; 
lean_ctor_set_uint8(x_4, sizeof(void*)*8 + 1, x_3);
x_37 = 0;
x_38 = 1;
x_39 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_37, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; 
x_40 = lean_ctor_get(x_4, 0);
x_41 = lean_ctor_get(x_4, 1);
x_42 = lean_ctor_get(x_4, 2);
x_43 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_44 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 2);
x_45 = lean_ctor_get(x_4, 3);
x_46 = lean_ctor_get(x_4, 4);
x_47 = lean_ctor_get(x_4, 5);
x_48 = lean_ctor_get(x_4, 6);
x_49 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 3);
x_50 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 4);
x_51 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 5);
x_52 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 6);
x_53 = lean_ctor_get(x_4, 7);
x_54 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 7);
x_55 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 8);
lean_inc(x_53);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 8, 9);
lean_ctor_set(x_56, 0, x_40);
lean_ctor_set(x_56, 1, x_41);
lean_ctor_set(x_56, 2, x_42);
lean_ctor_set(x_56, 3, x_45);
lean_ctor_set(x_56, 4, x_46);
lean_ctor_set(x_56, 5, x_47);
lean_ctor_set(x_56, 6, x_48);
lean_ctor_set(x_56, 7, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*8, x_43);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 1, x_3);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 2, x_44);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 3, x_49);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 4, x_50);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 5, x_51);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 6, x_52);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 7, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 8, x_55);
x_57 = 0;
x_58 = 1;
x_59 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_57, x_58, x_56, x_5, x_6, x_7, x_8, x_9, x_10);
return x_59;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 8);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_PersistentHashMap_find_x3f___at_Lean_getDelayedMVarAssignment_x3f___spec__1(x_14, x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 8);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_PersistentHashMap_find_x3f___at_Lean_getDelayedMVarAssignment_x3f___spec__1(x_21, x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
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
lean_inc(x_2);
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
uint8_t x_15; 
lean_inc(x_2);
lean_inc(x_3);
x_15 = l_Lean_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_inc(x_2);
x_16 = l_Lean_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_3, x_2);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3(x_1, x_17, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
case 5:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_19, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_20);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_22, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_22, 0, x_30);
return x_21;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_33 = x_23;
} else {
 lean_dec_ref(x_23);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_21, 0, x_35);
return x_21;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_dec(x_21);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_38 = x_22;
} else {
 lean_dec_ref(x_22);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_23, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_40 = x_23;
} else {
 lean_dec_ref(x_23);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_23);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_dec(x_21);
x_45 = lean_ctor_get(x_22, 1);
lean_inc(x_45);
lean_dec(x_22);
x_2 = x_20;
x_3 = x_45;
x_10 = x_44;
goto _start;
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
lean_dec(x_2);
x_49 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_47, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
lean_dec(x_48);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_49, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_50, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_50, 0, x_58);
return x_49;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_dec(x_50);
x_60 = lean_ctor_get(x_51, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_61 = x_51;
} else {
 lean_dec_ref(x_51);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
lean_ctor_set(x_49, 0, x_63);
return x_49;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_49, 1);
lean_inc(x_64);
lean_dec(x_49);
x_65 = lean_ctor_get(x_50, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_66 = x_50;
} else {
 lean_dec_ref(x_50);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_51, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_68 = x_51;
} else {
 lean_dec_ref(x_51);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 1, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_67);
if (lean_is_scalar(x_66)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_66;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_64);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_51);
x_72 = lean_ctor_get(x_49, 1);
lean_inc(x_72);
lean_dec(x_49);
x_73 = lean_ctor_get(x_50, 1);
lean_inc(x_73);
lean_dec(x_50);
x_2 = x_48;
x_3 = x_73;
x_10 = x_72;
goto _start;
}
}
case 7:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_2, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_2, 2);
lean_inc(x_76);
lean_dec(x_2);
x_77 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_75, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
lean_dec(x_76);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_77, 0);
lean_dec(x_81);
x_82 = !lean_is_exclusive(x_78);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_78, 0);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
return x_77;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_79, 0);
lean_inc(x_85);
lean_dec(x_79);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_78, 0, x_86);
return x_77;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_78, 1);
lean_inc(x_87);
lean_dec(x_78);
x_88 = lean_ctor_get(x_79, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_89 = x_79;
} else {
 lean_dec_ref(x_79);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 1, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_87);
lean_ctor_set(x_77, 0, x_91);
return x_77;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_92 = lean_ctor_get(x_77, 1);
lean_inc(x_92);
lean_dec(x_77);
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
x_95 = lean_ctor_get(x_79, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_96 = x_79;
} else {
 lean_dec_ref(x_79);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 1, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_95);
if (lean_is_scalar(x_94)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_94;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_93);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_92);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_79);
x_100 = lean_ctor_get(x_77, 1);
lean_inc(x_100);
lean_dec(x_77);
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
lean_dec(x_78);
x_2 = x_76;
x_3 = x_101;
x_10 = x_100;
goto _start;
}
}
case 8:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_2, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_2, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_2, 3);
lean_inc(x_105);
lean_dec(x_2);
x_106 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_103, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
lean_dec(x_105);
lean_dec(x_104);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_106, 0);
lean_dec(x_110);
x_111 = !lean_is_exclusive(x_107);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_107, 0);
lean_dec(x_112);
x_113 = !lean_is_exclusive(x_108);
if (x_113 == 0)
{
return x_106;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_108, 0);
lean_inc(x_114);
lean_dec(x_108);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_107, 0, x_115);
return x_106;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_107, 1);
lean_inc(x_116);
lean_dec(x_107);
x_117 = lean_ctor_get(x_108, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_118 = x_108;
} else {
 lean_dec_ref(x_108);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 1, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_117);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_116);
lean_ctor_set(x_106, 0, x_120);
return x_106;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_121 = lean_ctor_get(x_106, 1);
lean_inc(x_121);
lean_dec(x_106);
x_122 = lean_ctor_get(x_107, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_123 = x_107;
} else {
 lean_dec_ref(x_107);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_108, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_125 = x_108;
} else {
 lean_dec_ref(x_108);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(0, 1, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_124);
if (lean_is_scalar(x_123)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_123;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_122);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_121);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_108);
x_129 = lean_ctor_get(x_106, 1);
lean_inc(x_129);
lean_dec(x_106);
x_130 = lean_ctor_get(x_107, 1);
lean_inc(x_130);
lean_dec(x_107);
x_131 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_104, x_130, x_4, x_5, x_6, x_7, x_8, x_9, x_129);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
lean_dec(x_105);
x_134 = !lean_is_exclusive(x_131);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_131, 0);
lean_dec(x_135);
x_136 = !lean_is_exclusive(x_132);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_132, 0);
lean_dec(x_137);
x_138 = !lean_is_exclusive(x_133);
if (x_138 == 0)
{
return x_131;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_133, 0);
lean_inc(x_139);
lean_dec(x_133);
x_140 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_132, 0, x_140);
return x_131;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_132, 1);
lean_inc(x_141);
lean_dec(x_132);
x_142 = lean_ctor_get(x_133, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_143 = x_133;
} else {
 lean_dec_ref(x_133);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 1, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_142);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_141);
lean_ctor_set(x_131, 0, x_145);
return x_131;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_146 = lean_ctor_get(x_131, 1);
lean_inc(x_146);
lean_dec(x_131);
x_147 = lean_ctor_get(x_132, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_148 = x_132;
} else {
 lean_dec_ref(x_132);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_133, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_150 = x_133;
} else {
 lean_dec_ref(x_133);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 1, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_149);
if (lean_is_scalar(x_148)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_148;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_147);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_146);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_133);
x_154 = lean_ctor_get(x_131, 1);
lean_inc(x_154);
lean_dec(x_131);
x_155 = lean_ctor_get(x_132, 1);
lean_inc(x_155);
lean_dec(x_132);
x_2 = x_105;
x_3 = x_155;
x_10 = x_154;
goto _start;
}
}
}
case 10:
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_2, 1);
lean_inc(x_157);
lean_dec(x_2);
x_2 = x_157;
x_3 = x_16;
goto _start;
}
case 11:
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_2, 2);
lean_inc(x_159);
lean_dec(x_2);
x_2 = x_159;
x_3 = x_16;
goto _start;
}
default: 
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_2);
x_161 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1;
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_16);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_10);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_2);
x_164 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1;
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_3);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_10);
return x_166;
}
}
}
}
static lean_object* _init_l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
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
x_14 = l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__1;
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
lean_inc(x_1);
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
uint8_t x_284; 
x_284 = 1;
x_20 = x_284;
goto block_283;
}
else
{
uint8_t x_285; 
x_285 = 0;
x_20 = x_285;
goto block_283;
}
block_283:
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
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
x_40 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
x_41 = l_Lean_replaceRef(x_2, x_34);
lean_dec(x_34);
lean_dec(x_2);
x_42 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_30);
lean_ctor_set(x_42, 2, x_31);
lean_ctor_set(x_42, 3, x_32);
lean_ctor_set(x_42, 4, x_33);
lean_ctor_set(x_42, 5, x_41);
lean_ctor_set(x_42, 6, x_35);
lean_ctor_set(x_42, 7, x_36);
lean_ctor_set(x_42, 8, x_37);
lean_ctor_set(x_42, 9, x_38);
lean_ctor_set(x_42, 10, x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*11, x_40);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_43 = l_Lean_Elab_Term_ensureHasType(x_18, x_26, x_28, x_28, x_4, x_5, x_6, x_7, x_42, x_9, x_27);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_44);
x_46 = l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(x_1, x_44, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
uint8_t x_49; 
lean_dec(x_44);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
lean_dec(x_50);
x_51 = 0;
x_52 = lean_box(x_51);
lean_ctor_set(x_46, 0, x_52);
return x_46;
}
else
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = 0;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
lean_dec(x_46);
x_58 = l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(x_1, x_44, x_4, x_5, x_6, x_7, x_8, x_9, x_57);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
x_61 = 1;
x_62 = lean_box(x_61);
lean_ctor_set(x_58, 0, x_62);
return x_58;
}
else
{
lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_dec(x_58);
x_64 = 1;
x_65 = lean_box(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_43);
if (x_67 == 0)
{
return x_43;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_43, 0);
x_69 = lean_ctor_get(x_43, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_43);
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
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_25);
if (x_71 == 0)
{
return x_25;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_25, 0);
x_73 = lean_ctor_get(x_25, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_25);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_168; lean_object* x_169; lean_object* x_249; 
x_75 = lean_ctor_get(x_19, 1);
lean_inc(x_75);
lean_dec(x_19);
x_76 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__2___rarg(x_9, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_18);
lean_inc(x_2);
x_249 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(x_2, x_18, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_78);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_box(0);
x_253 = lean_ctor_get(x_8, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_8, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_8, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_8, 3);
lean_inc(x_256);
x_257 = lean_ctor_get(x_8, 4);
lean_inc(x_257);
x_258 = lean_ctor_get(x_8, 5);
lean_inc(x_258);
x_259 = lean_ctor_get(x_8, 6);
lean_inc(x_259);
x_260 = lean_ctor_get(x_8, 7);
lean_inc(x_260);
x_261 = lean_ctor_get(x_8, 8);
lean_inc(x_261);
x_262 = lean_ctor_get(x_8, 9);
lean_inc(x_262);
x_263 = lean_ctor_get(x_8, 10);
lean_inc(x_263);
x_264 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
x_265 = l_Lean_replaceRef(x_2, x_258);
lean_dec(x_258);
lean_dec(x_2);
x_266 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_266, 0, x_253);
lean_ctor_set(x_266, 1, x_254);
lean_ctor_set(x_266, 2, x_255);
lean_ctor_set(x_266, 3, x_256);
lean_ctor_set(x_266, 4, x_257);
lean_ctor_set(x_266, 5, x_265);
lean_ctor_set(x_266, 6, x_259);
lean_ctor_set(x_266, 7, x_260);
lean_ctor_set(x_266, 8, x_261);
lean_ctor_set(x_266, 9, x_262);
lean_ctor_set(x_266, 10, x_263);
lean_ctor_set_uint8(x_266, sizeof(void*)*11, x_264);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_267 = l_Lean_Elab_Term_ensureHasType(x_18, x_250, x_252, x_252, x_4, x_5, x_6, x_7, x_266, x_9, x_251);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
lean_inc(x_268);
x_270 = l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(x_1, x_268, x_4, x_5, x_6, x_7, x_8, x_9, x_269);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_unbox(x_271);
lean_dec(x_271);
if (x_272 == 0)
{
lean_object* x_273; uint8_t x_274; 
lean_dec(x_268);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_dec(x_270);
x_274 = 0;
x_79 = x_274;
x_80 = x_273;
goto block_167;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_275 = lean_ctor_get(x_270, 1);
lean_inc(x_275);
lean_dec(x_270);
lean_inc(x_1);
x_276 = l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(x_1, x_268, x_4, x_5, x_6, x_7, x_8, x_9, x_275);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
lean_dec(x_276);
x_278 = 1;
x_79 = x_278;
x_80 = x_277;
goto block_167;
}
}
else
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_279 = lean_ctor_get(x_267, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_267, 1);
lean_inc(x_280);
lean_dec(x_267);
x_168 = x_279;
x_169 = x_280;
goto block_248;
}
}
else
{
lean_object* x_281; lean_object* x_282; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_281 = lean_ctor_get(x_249, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_249, 1);
lean_inc(x_282);
lean_dec(x_249);
x_168 = x_281;
x_169 = x_282;
goto block_248;
}
block_167:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_81 = lean_st_ref_take(x_9, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 6);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = !lean_is_exclusive(x_82);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_82, 6);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = lean_ctor_get(x_83, 0);
x_89 = lean_ctor_get(x_83, 1);
x_90 = lean_ctor_get(x_89, 2);
lean_inc(x_90);
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_nat_dec_lt(x_91, x_90);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_1);
lean_ctor_set(x_83, 1, x_77);
x_93 = lean_st_ref_set(x_9, x_82, x_84);
lean_dec(x_9);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
lean_dec(x_95);
x_96 = lean_box(x_79);
lean_ctor_set(x_93, 0, x_96);
return x_93;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_box(x_79);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_sub(x_90, x_100);
lean_dec(x_90);
x_102 = l_Lean_Elab_instInhabitedInfoTree;
x_103 = l_Lean_PersistentArray_get_x21___rarg(x_102, x_89, x_101);
lean_dec(x_101);
x_104 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_88, x_1, x_103);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 0, x_104);
x_105 = lean_st_ref_set(x_9, x_82, x_84);
lean_dec(x_9);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 0);
lean_dec(x_107);
x_108 = lean_box(x_79);
lean_ctor_set(x_105, 0, x_108);
return x_105;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_dec(x_105);
x_110 = lean_box(x_79);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
else
{
uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_112 = lean_ctor_get_uint8(x_83, sizeof(void*)*2);
x_113 = lean_ctor_get(x_83, 0);
x_114 = lean_ctor_get(x_83, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_83);
x_115 = lean_ctor_get(x_114, 2);
lean_inc(x_115);
x_116 = lean_unsigned_to_nat(0u);
x_117 = lean_nat_dec_lt(x_116, x_115);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_1);
x_118 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_77);
lean_ctor_set_uint8(x_118, sizeof(void*)*2, x_112);
lean_ctor_set(x_82, 6, x_118);
x_119 = lean_st_ref_set(x_9, x_82, x_84);
lean_dec(x_9);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
x_122 = lean_box(x_79);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_nat_sub(x_115, x_124);
lean_dec(x_115);
x_126 = l_Lean_Elab_instInhabitedInfoTree;
x_127 = l_Lean_PersistentArray_get_x21___rarg(x_126, x_114, x_125);
lean_dec(x_125);
x_128 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_113, x_1, x_127);
x_129 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_77);
lean_ctor_set_uint8(x_129, sizeof(void*)*2, x_112);
lean_ctor_set(x_82, 6, x_129);
x_130 = lean_st_ref_set(x_9, x_82, x_84);
lean_dec(x_9);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
x_133 = lean_box(x_79);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_131);
return x_134;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_135 = lean_ctor_get(x_82, 0);
x_136 = lean_ctor_get(x_82, 1);
x_137 = lean_ctor_get(x_82, 2);
x_138 = lean_ctor_get(x_82, 3);
x_139 = lean_ctor_get(x_82, 4);
x_140 = lean_ctor_get(x_82, 5);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_82);
x_141 = lean_ctor_get_uint8(x_83, sizeof(void*)*2);
x_142 = lean_ctor_get(x_83, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_83, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_144 = x_83;
} else {
 lean_dec_ref(x_83);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_143, 2);
lean_inc(x_145);
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_nat_dec_lt(x_146, x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_145);
lean_dec(x_143);
lean_dec(x_1);
if (lean_is_scalar(x_144)) {
 x_148 = lean_alloc_ctor(0, 2, 1);
} else {
 x_148 = x_144;
}
lean_ctor_set(x_148, 0, x_142);
lean_ctor_set(x_148, 1, x_77);
lean_ctor_set_uint8(x_148, sizeof(void*)*2, x_141);
x_149 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_149, 0, x_135);
lean_ctor_set(x_149, 1, x_136);
lean_ctor_set(x_149, 2, x_137);
lean_ctor_set(x_149, 3, x_138);
lean_ctor_set(x_149, 4, x_139);
lean_ctor_set(x_149, 5, x_140);
lean_ctor_set(x_149, 6, x_148);
x_150 = lean_st_ref_set(x_9, x_149, x_84);
lean_dec(x_9);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
x_153 = lean_box(x_79);
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
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_155 = lean_unsigned_to_nat(1u);
x_156 = lean_nat_sub(x_145, x_155);
lean_dec(x_145);
x_157 = l_Lean_Elab_instInhabitedInfoTree;
x_158 = l_Lean_PersistentArray_get_x21___rarg(x_157, x_143, x_156);
lean_dec(x_156);
x_159 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_142, x_1, x_158);
if (lean_is_scalar(x_144)) {
 x_160 = lean_alloc_ctor(0, 2, 1);
} else {
 x_160 = x_144;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_77);
lean_ctor_set_uint8(x_160, sizeof(void*)*2, x_141);
x_161 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_161, 0, x_135);
lean_ctor_set(x_161, 1, x_136);
lean_ctor_set(x_161, 2, x_137);
lean_ctor_set(x_161, 3, x_138);
lean_ctor_set(x_161, 4, x_139);
lean_ctor_set(x_161, 5, x_140);
lean_ctor_set(x_161, 6, x_160);
x_162 = lean_st_ref_set(x_9, x_161, x_84);
lean_dec(x_9);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_164 = x_162;
} else {
 lean_dec_ref(x_162);
 x_164 = lean_box(0);
}
x_165 = lean_box(x_79);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
return x_166;
}
}
}
block_248:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_170 = lean_st_ref_take(x_9, x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_171, 6);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
x_174 = !lean_is_exclusive(x_171);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_171, 6);
lean_dec(x_175);
x_176 = !lean_is_exclusive(x_172);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_177 = lean_ctor_get(x_172, 0);
x_178 = lean_ctor_get(x_172, 1);
x_179 = lean_ctor_get(x_178, 2);
lean_inc(x_179);
x_180 = lean_unsigned_to_nat(0u);
x_181 = lean_nat_dec_lt(x_180, x_179);
if (x_181 == 0)
{
lean_object* x_182; uint8_t x_183; 
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_1);
lean_ctor_set(x_172, 1, x_77);
x_182 = lean_st_ref_set(x_9, x_171, x_173);
lean_dec(x_9);
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_182, 0);
lean_dec(x_184);
lean_ctor_set_tag(x_182, 1);
lean_ctor_set(x_182, 0, x_168);
return x_182;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_dec(x_182);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_168);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_187 = lean_unsigned_to_nat(1u);
x_188 = lean_nat_sub(x_179, x_187);
lean_dec(x_179);
x_189 = l_Lean_Elab_instInhabitedInfoTree;
x_190 = l_Lean_PersistentArray_get_x21___rarg(x_189, x_178, x_188);
lean_dec(x_188);
x_191 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_177, x_1, x_190);
lean_ctor_set(x_172, 1, x_77);
lean_ctor_set(x_172, 0, x_191);
x_192 = lean_st_ref_set(x_9, x_171, x_173);
lean_dec(x_9);
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_192, 0);
lean_dec(x_194);
lean_ctor_set_tag(x_192, 1);
lean_ctor_set(x_192, 0, x_168);
return x_192;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
lean_dec(x_192);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_168);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
else
{
uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_197 = lean_ctor_get_uint8(x_172, sizeof(void*)*2);
x_198 = lean_ctor_get(x_172, 0);
x_199 = lean_ctor_get(x_172, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_172);
x_200 = lean_ctor_get(x_199, 2);
lean_inc(x_200);
x_201 = lean_unsigned_to_nat(0u);
x_202 = lean_nat_dec_lt(x_201, x_200);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_1);
x_203 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_77);
lean_ctor_set_uint8(x_203, sizeof(void*)*2, x_197);
lean_ctor_set(x_171, 6, x_203);
x_204 = lean_st_ref_set(x_9, x_171, x_173);
lean_dec(x_9);
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
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
 lean_ctor_set_tag(x_207, 1);
}
lean_ctor_set(x_207, 0, x_168);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_208 = lean_unsigned_to_nat(1u);
x_209 = lean_nat_sub(x_200, x_208);
lean_dec(x_200);
x_210 = l_Lean_Elab_instInhabitedInfoTree;
x_211 = l_Lean_PersistentArray_get_x21___rarg(x_210, x_199, x_209);
lean_dec(x_209);
x_212 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_198, x_1, x_211);
x_213 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_77);
lean_ctor_set_uint8(x_213, sizeof(void*)*2, x_197);
lean_ctor_set(x_171, 6, x_213);
x_214 = lean_st_ref_set(x_9, x_171, x_173);
lean_dec(x_9);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_216 = x_214;
} else {
 lean_dec_ref(x_214);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
 lean_ctor_set_tag(x_217, 1);
}
lean_ctor_set(x_217, 0, x_168);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_218 = lean_ctor_get(x_171, 0);
x_219 = lean_ctor_get(x_171, 1);
x_220 = lean_ctor_get(x_171, 2);
x_221 = lean_ctor_get(x_171, 3);
x_222 = lean_ctor_get(x_171, 4);
x_223 = lean_ctor_get(x_171, 5);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_171);
x_224 = lean_ctor_get_uint8(x_172, sizeof(void*)*2);
x_225 = lean_ctor_get(x_172, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_172, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_227 = x_172;
} else {
 lean_dec_ref(x_172);
 x_227 = lean_box(0);
}
x_228 = lean_ctor_get(x_226, 2);
lean_inc(x_228);
x_229 = lean_unsigned_to_nat(0u);
x_230 = lean_nat_dec_lt(x_229, x_228);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_1);
if (lean_is_scalar(x_227)) {
 x_231 = lean_alloc_ctor(0, 2, 1);
} else {
 x_231 = x_227;
}
lean_ctor_set(x_231, 0, x_225);
lean_ctor_set(x_231, 1, x_77);
lean_ctor_set_uint8(x_231, sizeof(void*)*2, x_224);
x_232 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_232, 0, x_218);
lean_ctor_set(x_232, 1, x_219);
lean_ctor_set(x_232, 2, x_220);
lean_ctor_set(x_232, 3, x_221);
lean_ctor_set(x_232, 4, x_222);
lean_ctor_set(x_232, 5, x_223);
lean_ctor_set(x_232, 6, x_231);
x_233 = lean_st_ref_set(x_9, x_232, x_173);
lean_dec(x_9);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_235 = x_233;
} else {
 lean_dec_ref(x_233);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_235;
 lean_ctor_set_tag(x_236, 1);
}
lean_ctor_set(x_236, 0, x_168);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_237 = lean_unsigned_to_nat(1u);
x_238 = lean_nat_sub(x_228, x_237);
lean_dec(x_228);
x_239 = l_Lean_Elab_instInhabitedInfoTree;
x_240 = l_Lean_PersistentArray_get_x21___rarg(x_239, x_226, x_238);
lean_dec(x_238);
x_241 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_225, x_1, x_240);
if (lean_is_scalar(x_227)) {
 x_242 = lean_alloc_ctor(0, 2, 1);
} else {
 x_242 = x_227;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_77);
lean_ctor_set_uint8(x_242, sizeof(void*)*2, x_224);
x_243 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_243, 0, x_218);
lean_ctor_set(x_243, 1, x_219);
lean_ctor_set(x_243, 2, x_220);
lean_ctor_set(x_243, 3, x_221);
lean_ctor_set(x_243, 4, x_222);
lean_ctor_set(x_243, 5, x_223);
lean_ctor_set(x_243, 6, x_242);
x_244 = lean_st_ref_set(x_9, x_243, x_173);
lean_dec(x_9);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_246 = x_244;
} else {
 lean_dec_ref(x_244);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
 lean_ctor_set_tag(x_247, 1);
}
lean_ctor_set(x_247, 0, x_168);
lean_ctor_set(x_247, 1, x_245);
return x_247;
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
lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = l_Lean_Elab_Term_saveState___rarg(x_6, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(x_3);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1___boxed), 10, 3);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_Elab_Term_withSavedContext___rarg(x_4, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_12 = x_26;
x_13 = x_24;
goto block_16;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
x_30 = l_Lean_Exception_isRuntime(x_28);
if (x_30 == 0)
{
if (lean_obj_tag(x_28) == 0)
{
lean_free_object(x_22);
if (x_3 == 0)
{
lean_object* x_31; 
lean_dec(x_18);
x_31 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1;
x_12 = x_33;
x_13 = x_32;
goto block_16;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
x_38 = 1;
x_39 = l_Lean_Elab_Term_SavedState_restore(x_18, x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
x_12 = x_41;
x_13 = x_40;
goto block_16;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_28, 0);
lean_inc(x_42);
x_43 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__3;
x_44 = lean_nat_dec_eq(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_22;
}
else
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_22);
lean_dec(x_28);
x_45 = 1;
x_46 = l_Lean_Elab_Term_SavedState_restore(x_18, x_45, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
x_12 = x_48;
x_13 = x_47;
goto block_16;
}
}
}
else
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_9, sizeof(void*)*11);
if (x_49 == 0)
{
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_22;
}
else
{
if (lean_obj_tag(x_28) == 0)
{
lean_free_object(x_22);
if (x_3 == 0)
{
lean_object* x_50; 
lean_dec(x_18);
x_50 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1;
x_12 = x_52;
x_13 = x_51;
goto block_16;
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_28);
x_57 = 1;
x_58 = l_Lean_Elab_Term_SavedState_restore(x_18, x_57, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
x_12 = x_60;
x_13 = x_59;
goto block_16;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_28, 0);
lean_inc(x_61);
x_62 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__3;
x_63 = lean_nat_dec_eq(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_22;
}
else
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_22);
lean_dec(x_28);
x_64 = 1;
x_65 = l_Lean_Elab_Term_SavedState_restore(x_18, x_64, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
x_12 = x_67;
x_13 = x_66;
goto block_16;
}
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_22, 0);
x_69 = lean_ctor_get(x_22, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_22);
x_70 = l_Lean_Exception_isRuntime(x_68);
if (x_70 == 0)
{
if (lean_obj_tag(x_68) == 0)
{
if (x_3 == 0)
{
lean_object* x_71; 
lean_dec(x_18);
x_71 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_68, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1;
x_12 = x_73;
x_13 = x_72;
goto block_16;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
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
else
{
uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_68);
x_78 = 1;
x_79 = l_Lean_Elab_Term_SavedState_restore(x_18, x_78, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
x_12 = x_81;
x_13 = x_80;
goto block_16;
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_68, 0);
lean_inc(x_82);
x_83 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__3;
x_84 = lean_nat_dec_eq(x_82, x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_68);
lean_ctor_set(x_85, 1, x_69);
return x_85;
}
else
{
uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_68);
x_86 = 1;
x_87 = l_Lean_Elab_Term_SavedState_restore(x_18, x_86, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
x_12 = x_89;
x_13 = x_88;
goto block_16;
}
}
}
else
{
uint8_t x_90; 
x_90 = lean_ctor_get_uint8(x_9, sizeof(void*)*11);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_68);
lean_ctor_set(x_91, 1, x_69);
return x_91;
}
else
{
if (lean_obj_tag(x_68) == 0)
{
if (x_3 == 0)
{
lean_object* x_92; 
lean_dec(x_18);
x_92 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_68, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1;
x_12 = x_94;
x_13 = x_93;
goto block_16;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
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
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_68);
x_99 = 1;
x_100 = l_Lean_Elab_Term_SavedState_restore(x_18, x_99, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
x_12 = x_102;
x_13 = x_101;
goto block_16;
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_68, 0);
lean_inc(x_103);
x_104 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__3;
x_105 = lean_nat_dec_eq(x_103, x_104);
lean_dec(x_103);
if (x_105 == 0)
{
lean_object* x_106; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_68);
lean_ctor_set(x_106, 1, x_69);
return x_106;
}
else
{
uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_68);
x_107 = 1;
x_108 = l_Lean_Elab_Term_SavedState_restore(x_18, x_107, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
x_12 = x_110;
x_13 = x_109;
goto block_16;
}
}
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_29 = lean_ctor_get_uint8(x_9, sizeof(void*)*11);
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
x_30 = l_Lean_replaceRef(x_2, x_23);
lean_dec(x_23);
lean_dec(x_2);
x_31 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_20);
lean_ctor_set(x_31, 3, x_21);
lean_ctor_set(x_31, 4, x_22);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_24);
lean_ctor_set(x_31, 7, x_25);
lean_ctor_set(x_31, 8, x_26);
lean_ctor_set(x_31, 9, x_27);
lean_ctor_set(x_31, 10, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*11, x_29);
x_32 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_3, x_13, x_5, x_6, x_7, x_8, x_31, x_10, x_11);
return x_32;
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
x_1 = lean_mk_string_from_bytes("Lean.Elab.SyntheticMVars", 24);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Elab.SyntheticMVars.0.Lean.Elab.Term.synthesizePendingInstMVar", 76);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(67u);
x_4 = lean_unsigned_to_nat(26u);
x_5 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_15; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_10 = x_19;
x_11 = x_17;
goto block_14;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
x_23 = l_Lean_Exception_isRuntime(x_21);
if (x_23 == 0)
{
lean_free_object(x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_24; 
x_24 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1;
x_10 = x_26;
x_11 = x_25;
goto block_14;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
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
lean_dec(x_21);
x_31 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__4;
x_32 = l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1(x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_10 = x_36;
x_11 = x_34;
goto block_14;
}
else
{
uint8_t x_37; 
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
}
else
{
uint8_t x_41; 
x_41 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
if (x_41 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
lean_free_object(x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_42; 
x_42 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1;
x_10 = x_44;
x_11 = x_43;
goto block_14;
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_42);
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
lean_dec(x_21);
x_49 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__4;
x_50 = l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1(x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_10 = x_54;
x_11 = x_52;
goto block_14;
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
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_15, 0);
x_60 = lean_ctor_get(x_15, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_15);
x_61 = l_Lean_Exception_isRuntime(x_59);
if (x_61 == 0)
{
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_62; 
x_62 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1;
x_10 = x_64;
x_11 = x_63;
goto block_14;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_67 = x_62;
} else {
 lean_dec_ref(x_62);
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
lean_object* x_69; lean_object* x_70; 
lean_dec(x_59);
x_69 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__4;
x_70 = l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1(x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
x_10 = x_74;
x_11 = x_72;
goto block_14;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_77 = x_70;
} else {
 lean_dec_ref(x_70);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8_t x_79; 
x_79 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_59);
lean_ctor_set(x_80, 1, x_60);
return x_80;
}
else
{
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_81; 
x_81 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1;
x_10 = x_83;
x_11 = x_82;
goto block_14;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
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
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_59);
x_88 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__4;
x_89 = l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1(x_88, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_10 = x_93;
x_11 = x_91;
goto block_14;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
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
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_31; 
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
x_31 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
lean_dec(x_12);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = 0;
x_36 = l_Lean_Elab_Term_SavedState_restore(x_10, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_34);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(x_35);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_box(x_35);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_31, 0);
lean_dec(x_44);
x_45 = 1;
x_46 = lean_box(x_45);
lean_ctor_set(x_31, 0, x_46);
return x_31;
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_31, 1);
lean_inc(x_47);
lean_dec(x_31);
x_48 = 1;
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_31, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_31, 1);
lean_inc(x_52);
lean_dec(x_31);
x_13 = x_51;
x_14 = x_52;
goto block_30;
}
block_30:
{
uint8_t x_15; 
x_15 = l_Lean_Exception_isRuntime(x_13);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_12);
x_16 = 0;
x_17 = l_Lean_Elab_Term_SavedState_restore(x_10, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*11);
if (x_22 == 0)
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
else
{
uint8_t x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_12);
x_24 = 0;
x_25 = l_Lean_Elab_Term_SavedState_restore(x_10, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 0, x_13);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
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
x_17 = l_Lean_Exception_isRuntime(x_16);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_7);
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
else
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
lean_dec(x_7);
if (x_20 == 0)
{
return x_10;
}
else
{
uint8_t x_21; lean_object* x_22; 
lean_dec(x_16);
x_21 = 0;
x_22 = lean_box(x_21);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = l_Lean_Exception_isRuntime(x_23);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_7);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
lean_dec(x_7);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_23);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_24);
return x_33;
}
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Meta_instInhabitedDefaultInstances;
x_8 = l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___closed__1;
x_9 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_7, x_8, x_6);
lean_dec(x_6);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
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
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_instInhabitedDefaultInstances;
x_15 = l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___closed__1;
x_16 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_14, x_15, x_13);
lean_dec(x_13);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Meta_instInhabitedDefaultInstances;
x_14 = l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___closed__1;
x_15 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_13, x_14, x_12);
lean_dec(x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_RBNode_find___at_Lean_Meta_addDefaultInstanceEntry___spec__3(x_16, x_1);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_instInhabitedDefaultInstances;
x_24 = l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___closed__1;
x_25 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_23, x_24, x_22);
lean_dec(x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_RBNode_find___at_Lean_Meta_addDefaultInstanceEntry___spec__3(x_26, x_1);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_5);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_nat_dec_eq(x_17, x_2);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_16);
lean_inc(x_3);
{
lean_object* _tmp_3 = x_15;
lean_object* _tmp_4 = x_3;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_20; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_20 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance(x_1, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
lean_inc(x_3);
{
lean_object* _tmp_3 = x_15;
lean_object* _tmp_4 = x_3;
lean_object* _tmp_11 = x_23;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 0);
lean_dec(x_26);
x_27 = l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__2;
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__2;
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
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_37 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__2(x_1, x_2, x_36, x_26, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__2;
x_42 = lean_box(0);
x_43 = lean_apply_8(x_41, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_46);
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_ctor_get(x_39, 0);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
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
}
}
else
{
uint8_t x_54; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_10);
if (x_58 == 0)
{
return x_10;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_10, 0);
x_60 = lean_ctor_get(x_10, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_10);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_4, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_4, x_19);
lean_dec(x_4);
x_21 = lean_nat_dec_lt(x_5, x_3);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_22 = l_Lean_instInhabitedBinderInfo;
x_23 = lean_box(x_22);
x_24 = l___private_Init_Util_0__outOfBounds___rarg(x_23);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
x_26 = 3;
x_27 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_20;
x_5 = x_28;
goto _start;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_array_get_size(x_1);
x_31 = lean_nat_dec_lt(x_5, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l_Lean_instInhabitedExpr;
x_33 = l___private_Init_Util_0__outOfBounds___rarg(x_32);
x_34 = l_Lean_Expr_mvarId_x21(x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_8);
x_36 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_20;
x_5 = x_36;
x_8 = x_35;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_array_fget(x_1, x_5);
x_39 = l_Lean_Expr_mvarId_x21(x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_8);
x_41 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_20;
x_5 = x_41;
x_8 = x_40;
goto _start;
}
}
}
else
{
lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; 
x_43 = lean_array_fget(x_2, x_5);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
x_45 = 3;
x_46 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_20;
x_5 = x_47;
goto _start;
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_array_get_size(x_1);
x_50 = lean_nat_dec_lt(x_5, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = l_Lean_instInhabitedExpr;
x_52 = l___private_Init_Util_0__outOfBounds___rarg(x_51);
x_53 = l_Lean_Expr_mvarId_x21(x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_8);
x_55 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_20;
x_5 = x_55;
x_8 = x_54;
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_array_fget(x_1, x_5);
x_58 = l_Lean_Expr_mvarId_x21(x_57);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_8);
x_60 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_20;
x_5 = x_60;
x_8 = x_59;
goto _start;
}
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_5);
lean_dec(x_4);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_8);
lean_ctor_set(x_62, 1, x_15);
return x_62;
}
}
else
{
lean_object* x_63; 
lean_dec(x_5);
lean_dec(x_4);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_8);
lean_ctor_set(x_63, 1, x_15);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_unsigned_to_nat(1u);
lean_inc(x_12);
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___spec__1(x_2, x_1, x_12, x_12, x_13, x_12, x_14, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
lean_dec(x_1);
lean_dec(x_2);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("isDefEq worked ", 15);
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
x_1 = lean_mk_string_from_bytes(" : ", 3);
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
x_1 = lean_mk_string_from_bytes(" =\?= ", 5);
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
x_1 = lean_mk_string_from_bytes("", 0);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_6);
x_14 = l_Lean_Expr_mvar___override(x_1);
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 4);
lean_inc(x_19);
x_20 = lean_ctor_get(x_9, 5);
lean_inc(x_20);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 1;
lean_ctor_set_uint8(x_15, 7, x_22);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_17);
lean_ctor_set(x_23, 3, x_18);
lean_ctor_set(x_23, 4, x_19);
lean_ctor_set(x_23, 5, x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_14);
x_24 = l_Lean_Meta_isExprDefEqGuarded(x_14, x_2, x_23, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = 0;
x_30 = lean_box(x_29);
lean_ctor_set(x_24, 0, x_30);
return x_24;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_dec(x_24);
lean_inc(x_3);
x_36 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_box(0);
x_41 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1(x_4, x_5, x_40, x_7, x_8, x_9, x_10, x_11, x_12, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_14);
x_43 = lean_infer_type(x_14, x_9, x_10, x_11, x_12, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_46 = lean_infer_type(x_2, x_9, x_10, x_11, x_12, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_MessageData_ofExpr(x_14);
x_50 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__2;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_MessageData_ofExpr(x_44);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_MessageData_ofExpr(x_2);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_52);
x_61 = l_Lean_MessageData_ofExpr(x_47);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_3, x_64, x_7, x_8, x_9, x_10, x_11, x_12, x_48);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1(x_4, x_5, x_66, x_7, x_8, x_9, x_10, x_11, x_12, x_67);
return x_68;
}
else
{
uint8_t x_69; 
lean_dec(x_44);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_46);
if (x_69 == 0)
{
return x_46;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_46, 0);
x_71 = lean_ctor_get(x_46, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_46);
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
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_43);
if (x_73 == 0)
{
return x_43;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_43, 0);
x_75 = lean_ctor_get(x_43, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_43);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_24);
if (x_77 == 0)
{
return x_24;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_24, 0);
x_79 = lean_ctor_get(x_24, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_24);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_81 = lean_ctor_get_uint8(x_15, 0);
x_82 = lean_ctor_get_uint8(x_15, 1);
x_83 = lean_ctor_get_uint8(x_15, 2);
x_84 = lean_ctor_get_uint8(x_15, 3);
x_85 = lean_ctor_get_uint8(x_15, 4);
x_86 = lean_ctor_get_uint8(x_15, 5);
x_87 = lean_ctor_get_uint8(x_15, 6);
x_88 = lean_ctor_get_uint8(x_15, 8);
x_89 = lean_ctor_get_uint8(x_15, 9);
x_90 = lean_ctor_get_uint8(x_15, 10);
x_91 = lean_ctor_get_uint8(x_15, 11);
lean_dec(x_15);
x_92 = 1;
x_93 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_93, 0, x_81);
lean_ctor_set_uint8(x_93, 1, x_82);
lean_ctor_set_uint8(x_93, 2, x_83);
lean_ctor_set_uint8(x_93, 3, x_84);
lean_ctor_set_uint8(x_93, 4, x_85);
lean_ctor_set_uint8(x_93, 5, x_86);
lean_ctor_set_uint8(x_93, 6, x_87);
lean_ctor_set_uint8(x_93, 7, x_92);
lean_ctor_set_uint8(x_93, 8, x_88);
lean_ctor_set_uint8(x_93, 9, x_89);
lean_ctor_set_uint8(x_93, 10, x_90);
lean_ctor_set_uint8(x_93, 11, x_91);
x_94 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_16);
lean_ctor_set(x_94, 2, x_17);
lean_ctor_set(x_94, 3, x_18);
lean_ctor_set(x_94, 4, x_19);
lean_ctor_set(x_94, 5, x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_14);
x_95 = l_Lean_Meta_isExprDefEqGuarded(x_14, x_2, x_94, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_99 = x_95;
} else {
 lean_dec_ref(x_95);
 x_99 = lean_box(0);
}
x_100 = 0;
x_101 = lean_box(x_100);
if (lean_is_scalar(x_99)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_99;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_98);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_ctor_get(x_95, 1);
lean_inc(x_103);
lean_dec(x_95);
lean_inc(x_3);
x_104 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_box(0);
x_109 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1(x_4, x_5, x_108, x_7, x_8, x_9, x_10, x_11, x_12, x_107);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_104, 1);
lean_inc(x_110);
lean_dec(x_104);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_14);
x_111 = lean_infer_type(x_14, x_9, x_10, x_11, x_12, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_114 = lean_infer_type(x_2, x_9, x_10, x_11, x_12, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Lean_MessageData_ofExpr(x_14);
x_118 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__2;
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
x_120 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4;
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_MessageData_ofExpr(x_112);
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6;
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_MessageData_ofExpr(x_2);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_120);
x_129 = l_Lean_MessageData_ofExpr(x_115);
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_3, x_132, x_7, x_8, x_9, x_10, x_11, x_12, x_116);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1(x_4, x_5, x_134, x_7, x_8, x_9, x_10, x_11, x_12, x_135);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_112);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = lean_ctor_get(x_114, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_114, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_139 = x_114;
} else {
 lean_dec_ref(x_114);
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
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_141 = lean_ctor_get(x_111, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_111, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_143 = x_111;
} else {
 lean_dec_ref(x_111);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_145 = lean_ctor_get(x_95, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_95, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_147 = x_95;
} else {
 lean_dec_ref(x_95);
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
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("defaultInstance", 15);
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
x_1 = lean_mk_string_from_bytes(", ", 2);
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
lean_inc(x_23);
x_25 = l_Lean_mkAppN(x_11, x_23);
x_26 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__3;
x_27 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_box(0);
x_32 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2(x_2, x_25, x_26, x_24, x_23, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
lean_inc(x_2);
x_34 = l_Lean_Expr_mvar___override(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_34);
x_35 = lean_infer_type(x_34, x_5, x_6, x_7, x_8, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_25);
x_38 = lean_infer_type(x_25, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_expr_dbg_to_string(x_34);
x_42 = l_Lean_stringToMessageData(x_41);
lean_dec(x_41);
x_43 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__5;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_MessageData_ofExpr(x_34);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_MessageData_ofExpr(x_36);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_inc(x_25);
x_55 = l_Lean_MessageData_ofExpr(x_25);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_49);
x_58 = l_Lean_MessageData_ofExpr(x_39);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_43);
x_61 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_26, x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2(x_2, x_25, x_26, x_24, x_23, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_36);
lean_dec(x_34);
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
x_65 = !lean_is_exclusive(x_38);
if (x_65 == 0)
{
return x_38;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_38, 0);
x_67 = lean_ctor_get(x_38, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_38);
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
lean_dec(x_34);
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
x_69 = !lean_is_exclusive(x_35);
if (x_69 == 0)
{
return x_35;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_35, 0);
x_71 = lean_ctor_get(x_35, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_35);
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
uint8_t x_73; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_19);
if (x_73 == 0)
{
return x_19;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_19, 0);
x_75 = lean_ctor_get(x_19, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_19);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_13);
if (x_77 == 0)
{
return x_13;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_13, 0);
x_79 = lean_ctor_get(x_13, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_13);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_10);
if (x_81 == 0)
{
return x_10;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_10, 0);
x_83 = lean_ctor_get(x_10, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_10);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
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
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
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
x_36 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
x_37 = l_Lean_replaceRef(x_24, x_30);
lean_dec(x_24);
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
x_38 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_26);
lean_ctor_set(x_38, 2, x_27);
lean_ctor_set(x_38, 3, x_28);
lean_ctor_set(x_38, 4, x_29);
lean_ctor_set(x_38, 5, x_37);
lean_ctor_set(x_38, 6, x_31);
lean_ctor_set(x_38, 7, x_32);
lean_ctor_set(x_38, 8, x_33);
lean_ctor_set(x_38, 9, x_34);
lean_ctor_set(x_38, 10, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*11, x_36);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_15);
x_39 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio(x_15, x_1, x_4, x_5, x_6, x_7, x_38, x_9, x_23);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_16;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_9 = x_42;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_10 = _tmp_9;
}
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_2);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_st_ref_take(x_5, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_46, 2);
lean_dec(x_49);
x_50 = l_List_reverse___rarg(x_16);
x_51 = l_List_appendTR___rarg(x_50, x_3);
lean_ctor_set(x_46, 2, x_51);
x_52 = lean_st_ref_set(x_5, x_46, x_47);
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
x_55 = 1;
x_56 = lean_box(x_55);
lean_ctor_set(x_52, 0, x_56);
return x_52;
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec(x_52);
x_58 = 1;
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_61 = lean_ctor_get(x_46, 0);
x_62 = lean_ctor_get(x_46, 1);
x_63 = lean_ctor_get(x_46, 3);
x_64 = lean_ctor_get(x_46, 4);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_46);
x_65 = l_List_reverse___rarg(x_16);
x_66 = l_List_appendTR___rarg(x_65, x_3);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_62);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_63);
lean_ctor_set(x_67, 4, x_64);
x_68 = lean_st_ref_set(x_5, x_67, x_47);
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
x_71 = 1;
x_72 = lean_box(x_71);
if (lean_is_scalar(x_70)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_70;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_69);
return x_73;
}
}
}
else
{
uint8_t x_74; 
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
x_74 = !lean_is_exclusive(x_39);
if (x_74 == 0)
{
return x_39;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_39, 0);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_39);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_22);
lean_dec(x_21);
x_78 = lean_ctor_get(x_17, 1);
lean_inc(x_78);
lean_dec(x_17);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_16;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_9 = x_78;
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
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_2, 0);
x_81 = lean_ctor_get(x_2, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_2);
x_82 = l_Lean_Elab_Term_getSyntheticMVarDecl_x3f(x_80, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_3);
x_2 = x_81;
x_3 = x_85;
x_10 = x_84;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec(x_82);
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_ctor_get(x_8, 0);
x_92 = lean_ctor_get(x_8, 1);
x_93 = lean_ctor_get(x_8, 2);
x_94 = lean_ctor_get(x_8, 3);
x_95 = lean_ctor_get(x_8, 4);
x_96 = lean_ctor_get(x_8, 5);
x_97 = lean_ctor_get(x_8, 6);
x_98 = lean_ctor_get(x_8, 7);
x_99 = lean_ctor_get(x_8, 8);
x_100 = lean_ctor_get(x_8, 9);
x_101 = lean_ctor_get(x_8, 10);
x_102 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
x_103 = l_Lean_replaceRef(x_90, x_96);
lean_dec(x_90);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
x_104 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_104, 0, x_91);
lean_ctor_set(x_104, 1, x_92);
lean_ctor_set(x_104, 2, x_93);
lean_ctor_set(x_104, 3, x_94);
lean_ctor_set(x_104, 4, x_95);
lean_ctor_set(x_104, 5, x_103);
lean_ctor_set(x_104, 6, x_97);
lean_ctor_set(x_104, 7, x_98);
lean_ctor_set(x_104, 8, x_99);
lean_ctor_set(x_104, 9, x_100);
lean_ctor_set(x_104, 10, x_101);
lean_ctor_set_uint8(x_104, sizeof(void*)*11, x_102);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_80);
x_105 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio(x_80, x_1, x_4, x_5, x_6, x_7, x_104, x_9, x_89);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_80);
lean_ctor_set(x_109, 1, x_3);
x_2 = x_81;
x_3 = x_109;
x_10 = x_108;
goto _start;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_80);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
lean_dec(x_105);
x_112 = lean_st_ref_take(x_5, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 3);
lean_inc(x_117);
x_118 = lean_ctor_get(x_113, 4);
lean_inc(x_118);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 x_119 = x_113;
} else {
 lean_dec_ref(x_113);
 x_119 = lean_box(0);
}
x_120 = l_List_reverse___rarg(x_81);
x_121 = l_List_appendTR___rarg(x_120, x_3);
if (lean_is_scalar(x_119)) {
 x_122 = lean_alloc_ctor(0, 5, 0);
} else {
 x_122 = x_119;
}
lean_ctor_set(x_122, 0, x_115);
lean_ctor_set(x_122, 1, x_116);
lean_ctor_set(x_122, 2, x_121);
lean_ctor_set(x_122, 3, x_117);
lean_ctor_set(x_122, 4, x_118);
x_123 = lean_st_ref_set(x_5, x_122, x_114);
lean_dec(x_5);
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
x_126 = 1;
x_127 = lean_box(x_126);
if (lean_is_scalar(x_125)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_125;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_124);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_129 = lean_ctor_get(x_105, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_105, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_131 = x_105;
} else {
 lean_dec_ref(x_105);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_88);
lean_dec(x_87);
x_133 = lean_ctor_get(x_82, 1);
lean_inc(x_133);
lean_dec(x_82);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_80);
lean_ctor_set(x_134, 1, x_3);
x_2 = x_81;
x_3 = x_134;
x_10 = x_133;
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
x_1 = lean_mk_string_from_bytes("typeclass instance problem is stuck, it is often due to metavariables", 69);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_Elab_Term_getMVarDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_7, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 5);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_12);
x_18 = lean_ctor_get(x_10, 2);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_indentExpr(x_18);
x_20 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__2;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_2);
x_25 = lean_box(0);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_ctor_get(x_26, 5);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_10, 2);
lean_inc(x_30);
lean_dec(x_10);
x_31 = l_Lean_indentExpr(x_30);
x_32 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__2;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_27);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_10);
lean_dec(x_2);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_27);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to create type class instance for", 40);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_getMVarDecl(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_indentExpr(x_19);
x_21 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_3, x_4, x_14, x_1, x_5, x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
return x_26;
}
else
{
uint8_t x_27; 
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
static lean_object* _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.Term.reportStuckSyntheticMVar", 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1;
x_2 = l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__1;
x_3 = lean_unsigned_to_nat(223u);
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
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_10);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___boxed), 8, 1);
lean_closure_set(x_27, 0, x_1);
x_28 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = lean_box(0);
lean_ctor_set(x_10, 0, x_29);
return x_10;
}
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_10);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_23, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_23, 3);
lean_inc(x_33);
lean_dec(x_23);
lean_inc(x_1);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2), 12, 5);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_1);
lean_closure_set(x_34, 2, x_30);
lean_closure_set(x_34, 3, x_31);
lean_closure_set(x_34, 4, x_33);
x_35 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_35;
}
default: 
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_23);
lean_free_object(x_10);
lean_dec(x_1);
x_36 = l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__2;
x_37 = l_panic___at_Lean_Elab_Term_reportStuckSyntheticMVar___spec__1(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_7, 0);
x_39 = lean_ctor_get(x_7, 1);
x_40 = lean_ctor_get(x_7, 2);
x_41 = lean_ctor_get(x_7, 3);
x_42 = lean_ctor_get(x_7, 4);
x_43 = lean_ctor_get(x_7, 5);
x_44 = lean_ctor_get(x_7, 6);
x_45 = lean_ctor_get(x_7, 7);
x_46 = lean_ctor_get(x_7, 8);
x_47 = lean_ctor_get(x_7, 9);
x_48 = lean_ctor_get(x_7, 10);
x_49 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_7);
x_50 = l_Lean_replaceRef(x_22, x_43);
lean_dec(x_43);
lean_dec(x_22);
x_51 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_51, 0, x_38);
lean_ctor_set(x_51, 1, x_39);
lean_ctor_set(x_51, 2, x_40);
lean_ctor_set(x_51, 3, x_41);
lean_ctor_set(x_51, 4, x_42);
lean_ctor_set(x_51, 5, x_50);
lean_ctor_set(x_51, 6, x_44);
lean_ctor_set(x_51, 7, x_45);
lean_ctor_set(x_51, 8, x_46);
lean_ctor_set(x_51, 9, x_47);
lean_ctor_set(x_51, 10, x_48);
lean_ctor_set_uint8(x_51, sizeof(void*)*11, x_49);
switch (lean_obj_tag(x_23)) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_free_object(x_10);
lean_inc(x_1);
x_52 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___boxed), 8, 1);
lean_closure_set(x_52, 0, x_1);
x_53 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_52, x_3, x_4, x_5, x_6, x_51, x_8, x_19);
return x_53;
}
else
{
lean_object* x_54; 
lean_dec(x_51);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = lean_box(0);
lean_ctor_set(x_10, 0, x_54);
return x_10;
}
}
case 1:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_free_object(x_10);
x_55 = lean_ctor_get(x_23, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_23, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_23, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_23, 3);
lean_inc(x_58);
lean_dec(x_23);
lean_inc(x_1);
x_59 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2), 12, 5);
lean_closure_set(x_59, 0, x_57);
lean_closure_set(x_59, 1, x_1);
lean_closure_set(x_59, 2, x_55);
lean_closure_set(x_59, 3, x_56);
lean_closure_set(x_59, 4, x_58);
x_60 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_59, x_3, x_4, x_5, x_6, x_51, x_8, x_19);
return x_60;
}
default: 
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_23);
lean_free_object(x_10);
lean_dec(x_1);
x_61 = l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__2;
x_62 = l_panic___at_Lean_Elab_Term_reportStuckSyntheticMVar___spec__1(x_61, x_3, x_4, x_5, x_6, x_51, x_8, x_19);
return x_62;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_63 = lean_ctor_get(x_10, 1);
lean_inc(x_63);
lean_dec(x_10);
x_64 = lean_ctor_get(x_11, 0);
lean_inc(x_64);
lean_dec(x_11);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_7, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_7, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_7, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_7, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_7, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_7, 5);
lean_inc(x_72);
x_73 = lean_ctor_get(x_7, 6);
lean_inc(x_73);
x_74 = lean_ctor_get(x_7, 7);
lean_inc(x_74);
x_75 = lean_ctor_get(x_7, 8);
lean_inc(x_75);
x_76 = lean_ctor_get(x_7, 9);
lean_inc(x_76);
x_77 = lean_ctor_get(x_7, 10);
lean_inc(x_77);
x_78 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
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
 x_79 = x_7;
} else {
 lean_dec_ref(x_7);
 x_79 = lean_box(0);
}
x_80 = l_Lean_replaceRef(x_65, x_72);
lean_dec(x_72);
lean_dec(x_65);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 11, 1);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_67);
lean_ctor_set(x_81, 1, x_68);
lean_ctor_set(x_81, 2, x_69);
lean_ctor_set(x_81, 3, x_70);
lean_ctor_set(x_81, 4, x_71);
lean_ctor_set(x_81, 5, x_80);
lean_ctor_set(x_81, 6, x_73);
lean_ctor_set(x_81, 7, x_74);
lean_ctor_set(x_81, 8, x_75);
lean_ctor_set(x_81, 9, x_76);
lean_ctor_set(x_81, 10, x_77);
lean_ctor_set_uint8(x_81, sizeof(void*)*11, x_78);
switch (lean_obj_tag(x_66)) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_inc(x_1);
x_82 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___boxed), 8, 1);
lean_closure_set(x_82, 0, x_1);
x_83 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_82, x_3, x_4, x_5, x_6, x_81, x_8, x_63);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_81);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_63);
return x_85;
}
}
case 1:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_66, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_66, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_66, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_66, 3);
lean_inc(x_89);
lean_dec(x_66);
lean_inc(x_1);
x_90 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2), 12, 5);
lean_closure_set(x_90, 0, x_88);
lean_closure_set(x_90, 1, x_1);
lean_closure_set(x_90, 2, x_86);
lean_closure_set(x_90, 3, x_87);
lean_closure_set(x_90, 4, x_89);
x_91 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_90, x_3, x_4, x_5, x_6, x_81, x_8, x_63);
return x_91;
}
default: 
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_66);
lean_dec(x_1);
x_92 = l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__2;
x_93 = l_panic___at_Lean_Elab_Term_reportStuckSyntheticMVar___spec__1(x_92, x_3, x_4, x_5, x_6, x_81, x_8, x_63);
return x_93;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Elab_Term_reportStuckSyntheticMVar(x_12, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_2 = x_13;
x_3 = x_16;
x_10 = x_15;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_10, 2);
x_14 = lean_box(0);
lean_ctor_set(x_10, 2, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1(x_1, x_13, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
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
uint8_t x_23; 
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
x_29 = lean_ctor_get(x_10, 2);
x_30 = lean_ctor_get(x_10, 3);
x_31 = lean_ctor_get(x_10, 4);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_31);
x_34 = lean_st_ref_set(x_3, x_33, x_11);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1(x_1, x_29, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_43 = x_37;
} else {
 lean_dec_ref(x_37);
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
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
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
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = l_Lean_Elab_Term_getSyntheticMVarDecl_x3f(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
{
lean_object* _tmp_1 = x_13;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_9 = x_16;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_10 = _tmp_9;
}
goto _start;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 1);
x_21 = lean_ctor_get(x_14, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 0;
x_24 = l_Lean_Syntax_getPos_x3f(x_22, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_dec(x_22);
lean_free_object(x_14);
lean_inc(x_1);
{
lean_object* _tmp_1 = x_13;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_9 = x_20;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_10 = _tmp_9;
}
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_ctor_set(x_24, 0, x_22);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_14, 0, x_29);
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_22);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_14, 0, x_32);
return x_14;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_dec(x_14);
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
lean_dec(x_18);
x_35 = 0;
x_36 = l_Lean_Syntax_getPos_x3f(x_34, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_dec(x_34);
lean_inc(x_1);
{
lean_object* _tmp_1 = x_13;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_9 = x_33;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_10 = _tmp_9;
}
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_1);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_34);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_33);
return x_42;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__1;
x_13 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___spec__1(x_12, x_11, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___closed__1;
x_18 = lean_box(0);
x_19 = lean_apply_8(x_17, x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_16);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
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
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = l_Lean_Level_hash(x_5);
lean_dec(x_5);
x_8 = l_Lean_Level_hash(x_6);
lean_dec(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_hashset_mk_idx(x_4, x_9);
x_11 = lean_array_uget(x_3, x_10);
lean_dec(x_3);
x_12 = l_List_elem___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__3(x_2, x_11);
lean_dec(x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_hashset_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 1, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_17 = lean_apply_1(x_1, x_14);
x_18 = lean_unbox_uint64(x_17);
lean_dec(x_17);
x_19 = lean_hashset_mk_idx(x_16, x_18);
x_20 = lean_array_uget(x_2, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_uset(x_2, x_19, x_21);
x_2 = x_22;
x_3 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__8(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = l_Lean_Level_hash(x_7);
lean_dec(x_7);
x_10 = l_Lean_Level_hash(x_8);
lean_dec(x_8);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = lean_hashset_mk_idx(x_6, x_11);
x_13 = lean_array_uget(x_1, x_12);
lean_ctor_set(x_2, 1, x_13);
x_14 = lean_array_uset(x_1, x_12, x_2);
x_1 = x_14;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_18 = lean_array_get_size(x_1);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
x_21 = l_Lean_Level_hash(x_19);
lean_dec(x_19);
x_22 = l_Lean_Level_hash(x_20);
lean_dec(x_20);
x_23 = lean_uint64_mix_hash(x_21, x_22);
x_24 = lean_hashset_mk_idx(x_18, x_23);
x_25 = lean_array_uget(x_1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_array_uset(x_1, x_24, x_26);
x_1 = x_27;
x_2 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__8(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashSetImp_moveEntries___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_replace___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_level_eq(x_8, x_10);
lean_dec(x_8);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
x_13 = l_List_replace___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9(x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_13);
return x_1;
}
else
{
uint8_t x_14; 
x_14 = lean_level_eq(x_9, x_11);
lean_dec(x_9);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_List_replace___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9(x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_15);
return x_1;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_level_eq(x_18, x_20);
lean_dec(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
x_23 = l_List_replace___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9(x_17, x_2, x_3);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_level_eq(x_19, x_21);
lean_dec(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_List_replace___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9(x_17, x_2, x_3);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_17);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = l_Lean_Level_hash(x_7);
lean_dec(x_7);
x_10 = l_Lean_Level_hash(x_8);
lean_dec(x_8);
x_11 = lean_uint64_mix_hash(x_9, x_10);
lean_inc(x_6);
x_12 = lean_hashset_mk_idx(x_6, x_11);
x_13 = lean_array_uget(x_5, x_12);
x_14 = l_List_elem___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__3(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_array_uset(x_5, x_12, x_17);
x_19 = lean_nat_dec_le(x_16, x_6);
lean_dec(x_6);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_1);
x_20 = l_Lean_HashSetImp_expand___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__5(x_16, x_18);
return x_20;
}
else
{
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_inc(x_2);
x_21 = l_List_replace___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9(x_13, x_2, x_2);
lean_dec(x_2);
x_22 = lean_array_uset(x_5, x_12, x_21);
lean_ctor_set(x_1, 1, x_22);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; size_t x_31; lean_object* x_32; uint8_t x_33; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = lean_array_get_size(x_24);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
x_28 = l_Lean_Level_hash(x_26);
lean_dec(x_26);
x_29 = l_Lean_Level_hash(x_27);
lean_dec(x_27);
x_30 = lean_uint64_mix_hash(x_28, x_29);
lean_inc(x_25);
x_31 = lean_hashset_mk_idx(x_25, x_30);
x_32 = lean_array_uget(x_24, x_31);
x_33 = l_List_elem___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__3(x_2, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_23, x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_array_uset(x_24, x_31, x_36);
x_38 = lean_nat_dec_le(x_35, x_25);
lean_dec(x_25);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = l_Lean_HashSetImp_expand___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__5(x_35, x_37);
return x_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_25);
lean_inc(x_2);
x_41 = l_List_replace___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9(x_32, x_2, x_2);
lean_dec(x_2);
x_42 = lean_array_uset(x_24, x_31, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_23);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_7, x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_uget(x_5, x_7);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_8, 1);
x_21 = lean_ctor_get(x_8, 0);
lean_dec(x_21);
lean_inc(x_12);
lean_inc(x_9);
lean_inc(x_20);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11(x_1, x_2, x_3, x_18, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_20);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_dec(x_8);
lean_inc(x_12);
lean_inc(x_9);
lean_inc(x_35);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_36 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11(x_1, x_2, x_3, x_18, x_35, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_18);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; 
lean_dec(x_35);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
lean_inc(x_4);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_44);
x_46 = 1;
x_47 = lean_usize_add(x_7, x_46);
x_7 = x_47;
x_8 = x_45;
x_15 = x_43;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
lean_inc(x_14);
lean_inc(x_2);
x_15 = l_Lean_HashSetImp_contains___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__2(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_push(x_5, x_1);
x_17 = l_Lean_HashSetImp_insert___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__4(x_2, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_5);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_6, x_5);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_25; 
x_17 = lean_array_uget(x_4, x_6);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_26 = lean_ctor_get(x_7, 1);
x_27 = lean_ctor_get(x_7, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_17, 2);
lean_inc(x_31);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Level_normLtAux(x_31, x_32, x_30, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_box(0);
x_35 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13___lambda__1(x_17, x_28, x_30, x_31, x_29, x_34, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_39);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_36, 0, x_7);
x_18 = x_36;
x_19 = x_37;
goto block_24;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec(x_36);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_40);
lean_ctor_set(x_7, 0, x_3);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_7);
x_18 = x_41;
x_19 = x_37;
goto block_24;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_box(0);
x_43 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13___lambda__1(x_17, x_28, x_31, x_30, x_29, x_42, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_47);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_44, 0, x_7);
x_18 = x_44;
x_19 = x_45;
goto block_24;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_48);
lean_ctor_set(x_7, 0, x_3);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_7);
x_18 = x_49;
x_19 = x_45;
goto block_24;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_dec(x_7);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_17, 2);
lean_inc(x_54);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_Level_normLtAux(x_54, x_55, x_53, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_box(0);
x_58 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13___lambda__1(x_17, x_51, x_53, x_54, x_52, x_57, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
lean_inc(x_3);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_61);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
x_18 = x_64;
x_19 = x_60;
goto block_24;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_box(0);
x_66 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13___lambda__1(x_17, x_51, x_54, x_53, x_52, x_65, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
lean_inc(x_3);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_3);
lean_ctor_set(x_71, 1, x_69);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
x_18 = x_72;
x_19 = x_68;
goto block_24;
}
}
block_24:
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_6, x_21);
x_6 = x_22;
x_7 = x_20;
x_14 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_array_get_size(x_13);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
lean_inc(x_9);
lean_inc(x_6);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12(x_1, x_2, x_3, x_14, x_13, x_17, x_18, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
x_25 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___lambda__1(x_23, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_9);
lean_dec(x_6);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_6);
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
lean_dec(x_3);
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
x_35 = lean_array_get_size(x_32);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13(x_1, x_2, x_33, x_32, x_36, x_37, x_34, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
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
x_44 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___lambda__1(x_42, x_43, x_6, x_7, x_8, x_9, x_10, x_11, x_41);
lean_dec(x_9);
lean_dec(x_6);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_39);
lean_dec(x_9);
lean_dec(x_6);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_6, x_5);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_25; 
x_17 = lean_array_uget(x_4, x_6);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_26 = lean_ctor_get(x_7, 1);
x_27 = lean_ctor_get(x_7, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_17, 2);
lean_inc(x_31);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Level_normLtAux(x_31, x_32, x_30, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_box(0);
x_35 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13___lambda__1(x_17, x_28, x_30, x_31, x_29, x_34, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_39);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_36, 0, x_7);
x_18 = x_36;
x_19 = x_37;
goto block_24;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec(x_36);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_40);
lean_ctor_set(x_7, 0, x_3);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_7);
x_18 = x_41;
x_19 = x_37;
goto block_24;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_box(0);
x_43 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13___lambda__1(x_17, x_28, x_31, x_30, x_29, x_42, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_47);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_44, 0, x_7);
x_18 = x_44;
x_19 = x_45;
goto block_24;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_48);
lean_ctor_set(x_7, 0, x_3);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_7);
x_18 = x_49;
x_19 = x_45;
goto block_24;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_dec(x_7);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_17, 2);
lean_inc(x_54);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_Level_normLtAux(x_54, x_55, x_53, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_box(0);
x_58 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13___lambda__1(x_17, x_51, x_53, x_54, x_52, x_57, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
lean_inc(x_3);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_61);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
x_18 = x_64;
x_19 = x_60;
goto block_24;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_box(0);
x_66 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13___lambda__1(x_17, x_51, x_54, x_53, x_52, x_65, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
lean_inc(x_3);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_3);
lean_ctor_set(x_71, 1, x_69);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
x_18 = x_72;
x_19 = x_68;
goto block_24;
}
}
block_24:
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_6, x_21);
x_6 = x_22;
x_7 = x_20;
x_14 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11(x_1, x_2, x_4, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_5);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_array_get_size(x_23);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = 0;
x_29 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__14(x_1, x_2, x_24, x_23, x_27, x_28, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
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
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stuck at solving universe constraint", 36);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_37; 
lean_dec(x_7);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_3, x_18);
lean_dec(x_3);
x_37 = lean_nat_dec_lt(x_4, x_2);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_Meta_instInhabitedPostponedEntry;
x_39 = l___private_Init_Util_0__outOfBounds___rarg(x_38);
x_20 = x_39;
goto block_36;
}
else
{
lean_object* x_40; 
x_40 = lean_array_fget(x_1, x_4);
x_20 = x_40;
goto block_36;
}
block_36:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_20);
x_22 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore(x_21, x_20, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = 2;
x_27 = l_Lean_logAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__8(x_25, x_23, x_26, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_30 = lean_box(0);
x_3 = x_19;
x_4 = x_29;
x_7 = x_30;
x_14 = x_28;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_7);
lean_ctor_set(x_41, 1, x_14);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_7);
lean_ctor_set(x_42, 1, x_14);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
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
x_25 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
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
x_26 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_27 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_16);
lean_ctor_set(x_27, 3, x_17);
lean_ctor_set(x_27, 4, x_18);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set(x_27, 6, x_20);
lean_ctor_set(x_27, 7, x_21);
lean_ctor_set(x_27, 8, x_22);
lean_ctor_set(x_27, 9, x_23);
lean_ctor_set(x_27, 10, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*11, x_25);
x_28 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_2, x_3, x_4, x_5, x_6, x_27, x_8, x_9);
lean_dec(x_27);
return x_28;
}
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_instBEqLevel;
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
x_1 = l_Lean_Level_instHashableLevel;
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
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = l_Lean_Meta_getPostponed___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(8u);
x_12 = l_Lean_mkHashSetImp___rarg(x_11);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1;
x_16 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2;
lean_inc(x_4);
lean_inc(x_1);
x_17 = l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10(x_15, x_16, x_9, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_get_size(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_21);
x_24 = l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15(x_20, x_21, x_21, x_22, x_21, x_22, x_23, x_1, x_2, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_38; uint8_t x_39; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_lt(x_38, x_21);
lean_dec(x_21);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_20);
x_40 = l_Lean_Meta_instInhabitedPostponedEntry;
x_41 = l___private_Init_Util_0__outOfBounds___rarg(x_40);
x_26 = x_41;
goto block_37;
}
else
{
lean_object* x_42; 
x_42 = lean_array_fget(x_20, x_38);
lean_dec(x_20);
x_26 = x_42;
goto block_37;
}
block_37:
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_26);
x_28 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore(x_27, x_26, x_3, x_4, x_5, x_6, x_25);
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
x_32 = l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__16(x_31, x_29, x_1, x_2, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_2);
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
}
else
{
uint8_t x_43; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_24);
if (x_43 == 0)
{
return x_24;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_24, 0);
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_24);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSet___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_elem___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashSetImp_contains___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__2(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replace___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__13(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__14(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
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
lean_dec(x_2);
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
lean_dec(x_2);
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
x_26 = lean_ctor_get(x_10, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_27 = l_Lean_RBNode_erase___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__1(x_1, x_23);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_25);
lean_ctor_set(x_28, 4, x_26);
x_29 = lean_st_ref_set(x_3, x_28, x_11);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
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
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__2;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
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
x_26 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
x_27 = l_Lean_replaceRef(x_12, x_20);
lean_dec(x_20);
lean_dec(x_12);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_27);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_ctor_set(x_8, 5, x_27);
x_28 = lean_nat_dec_eq(x_18, x_19);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_8);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_18, x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_16);
lean_ctor_set(x_31, 2, x_17);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_19);
lean_ctor_set(x_31, 5, x_27);
lean_ctor_set(x_31, 6, x_21);
lean_ctor_set(x_31, 7, x_22);
lean_ctor_set(x_31, 8, x_23);
lean_ctor_set(x_31, 9, x_24);
lean_ctor_set(x_31, 10, x_25);
lean_ctor_set_uint8(x_31, sizeof(void*)*11, x_26);
x_32 = lean_st_ref_get(x_5, x_13);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_ctor_get(x_34, 2);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_List_isEmpty___rarg(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_32);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_box(x_38);
x_41 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_41, 0, x_39);
lean_closure_set(x_41, 1, x_40);
lean_inc(x_9);
lean_inc(x_31);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_42 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_38, x_38, x_4, x_5, x_6, x_7, x_31, x_9, x_35);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
if (x_1 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = 1;
x_47 = lean_box(x_46);
x_48 = lean_box(x_38);
x_49 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_49, 0, x_47);
lean_closure_set(x_49, 1, x_48);
lean_inc(x_9);
lean_inc(x_31);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_50 = l_Lean_Elab_Term_withoutPostponing___rarg(x_49, x_4, x_5, x_6, x_7, x_31, x_9, x_45);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_54 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(x_4, x_5, x_6, x_7, x_31, x_9, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
lean_inc(x_9);
lean_inc(x_31);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_58 = l_Lean_Elab_Term_withoutPostponing___rarg(x_41, x_4, x_5, x_6, x_7, x_31, x_9, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
lean_inc(x_9);
lean_inc(x_31);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_62 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_38, x_46, x_4, x_5, x_6, x_7, x_31, x_9, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_2, x_4, x_5, x_6, x_7, x_31, x_9, x_65);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_box(0);
x_3 = x_68;
x_8 = x_31;
x_10 = x_67;
goto _start;
}
}
else
{
uint8_t x_70; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_58, 1);
lean_inc(x_74);
lean_dec(x_58);
x_75 = lean_box(0);
x_3 = x_75;
x_8 = x_31;
x_10 = x_74;
goto _start;
}
}
else
{
uint8_t x_77; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_58);
if (x_77 == 0)
{
return x_58;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_58, 0);
x_79 = lean_ctor_get(x_58, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_58);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_41);
x_81 = lean_ctor_get(x_54, 1);
lean_inc(x_81);
lean_dec(x_54);
x_82 = lean_box(0);
x_3 = x_82;
x_8 = x_31;
x_10 = x_81;
goto _start;
}
}
else
{
uint8_t x_84; 
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_84 = !lean_is_exclusive(x_54);
if (x_84 == 0)
{
return x_54;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_54, 0);
x_86 = lean_ctor_get(x_54, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_54);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_41);
x_88 = lean_ctor_get(x_50, 1);
lean_inc(x_88);
lean_dec(x_50);
x_89 = lean_box(0);
x_3 = x_89;
x_8 = x_31;
x_10 = x_88;
goto _start;
}
}
else
{
uint8_t x_91; 
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_91 = !lean_is_exclusive(x_50);
if (x_91 == 0)
{
return x_50;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_50, 0);
x_93 = lean_ctor_get(x_50, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_50);
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
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_95 = !lean_is_exclusive(x_42);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_42, 0);
lean_dec(x_96);
x_97 = lean_box(0);
lean_ctor_set(x_42, 0, x_97);
return x_42;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_42, 1);
lean_inc(x_98);
lean_dec(x_42);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_41);
x_101 = lean_ctor_get(x_42, 1);
lean_inc(x_101);
lean_dec(x_42);
x_102 = lean_box(0);
x_3 = x_102;
x_8 = x_31;
x_10 = x_101;
goto _start;
}
}
else
{
uint8_t x_104; 
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_104 = !lean_is_exclusive(x_42);
if (x_104 == 0)
{
return x_42;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_42, 0);
x_106 = lean_ctor_get(x_42, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_42);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_108 = lean_box(0);
lean_ctor_set(x_32, 0, x_108);
return x_32;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_32, 0);
x_110 = lean_ctor_get(x_32, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_32);
x_111 = lean_ctor_get(x_109, 2);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l_List_isEmpty___rarg(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = 0;
x_114 = lean_box(x_113);
x_115 = lean_box(x_113);
x_116 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_116, 0, x_114);
lean_closure_set(x_116, 1, x_115);
lean_inc(x_9);
lean_inc(x_31);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_117 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_113, x_113, x_4, x_5, x_6, x_7, x_31, x_9, x_110);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_unbox(x_118);
lean_dec(x_118);
if (x_119 == 0)
{
if (x_1 == 0)
{
lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = 1;
x_122 = lean_box(x_121);
x_123 = lean_box(x_113);
x_124 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_124, 0, x_122);
lean_closure_set(x_124, 1, x_123);
lean_inc(x_9);
lean_inc(x_31);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_125 = l_Lean_Elab_Term_withoutPostponing___rarg(x_124, x_4, x_5, x_6, x_7, x_31, x_9, x_120);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_129 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(x_4, x_5, x_6, x_7, x_31, x_9, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
lean_inc(x_9);
lean_inc(x_31);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_133 = l_Lean_Elab_Term_withoutPostponing___rarg(x_116, x_4, x_5, x_6, x_7, x_31, x_9, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_unbox(x_134);
lean_dec(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
lean_inc(x_9);
lean_inc(x_31);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_137 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_113, x_121, x_4, x_5, x_6, x_7, x_31, x_9, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_141 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_2, x_4, x_5, x_6, x_7, x_31, x_9, x_140);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_137, 1);
lean_inc(x_142);
lean_dec(x_137);
x_143 = lean_box(0);
x_3 = x_143;
x_8 = x_31;
x_10 = x_142;
goto _start;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_145 = lean_ctor_get(x_137, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_137, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_147 = x_137;
} else {
 lean_dec_ref(x_137);
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
x_149 = lean_ctor_get(x_133, 1);
lean_inc(x_149);
lean_dec(x_133);
x_150 = lean_box(0);
x_3 = x_150;
x_8 = x_31;
x_10 = x_149;
goto _start;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_152 = lean_ctor_get(x_133, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_133, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_154 = x_133;
} else {
 lean_dec_ref(x_133);
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
lean_dec(x_116);
x_156 = lean_ctor_get(x_129, 1);
lean_inc(x_156);
lean_dec(x_129);
x_157 = lean_box(0);
x_3 = x_157;
x_8 = x_31;
x_10 = x_156;
goto _start;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_116);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_159 = lean_ctor_get(x_129, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_129, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_161 = x_129;
} else {
 lean_dec_ref(x_129);
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
lean_dec(x_116);
x_163 = lean_ctor_get(x_125, 1);
lean_inc(x_163);
lean_dec(x_125);
x_164 = lean_box(0);
x_3 = x_164;
x_8 = x_31;
x_10 = x_163;
goto _start;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_116);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_166 = lean_ctor_get(x_125, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_125, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_168 = x_125;
} else {
 lean_dec_ref(x_125);
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
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_116);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_170 = lean_ctor_get(x_117, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_171 = x_117;
} else {
 lean_dec_ref(x_117);
 x_171 = lean_box(0);
}
x_172 = lean_box(0);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_170);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_116);
x_174 = lean_ctor_get(x_117, 1);
lean_inc(x_174);
lean_dec(x_117);
x_175 = lean_box(0);
x_3 = x_175;
x_8 = x_31;
x_10 = x_174;
goto _start;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_116);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_177 = lean_ctor_get(x_117, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_117, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_179 = x_117;
} else {
 lean_dec_ref(x_117);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_181 = lean_box(0);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_110);
return x_182;
}
}
}
else
{
lean_object* x_183; 
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
x_183 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1(x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_184 = lean_ctor_get(x_8, 0);
x_185 = lean_ctor_get(x_8, 1);
x_186 = lean_ctor_get(x_8, 2);
x_187 = lean_ctor_get(x_8, 3);
x_188 = lean_ctor_get(x_8, 4);
x_189 = lean_ctor_get(x_8, 5);
x_190 = lean_ctor_get(x_8, 6);
x_191 = lean_ctor_get(x_8, 7);
x_192 = lean_ctor_get(x_8, 8);
x_193 = lean_ctor_get(x_8, 9);
x_194 = lean_ctor_get(x_8, 10);
x_195 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_8);
x_196 = l_Lean_replaceRef(x_12, x_189);
lean_dec(x_189);
lean_dec(x_12);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_196);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
x_197 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_197, 0, x_184);
lean_ctor_set(x_197, 1, x_185);
lean_ctor_set(x_197, 2, x_186);
lean_ctor_set(x_197, 3, x_187);
lean_ctor_set(x_197, 4, x_188);
lean_ctor_set(x_197, 5, x_196);
lean_ctor_set(x_197, 6, x_190);
lean_ctor_set(x_197, 7, x_191);
lean_ctor_set(x_197, 8, x_192);
lean_ctor_set(x_197, 9, x_193);
lean_ctor_set(x_197, 10, x_194);
lean_ctor_set_uint8(x_197, sizeof(void*)*11, x_195);
x_198 = lean_nat_dec_eq(x_187, x_188);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
lean_dec(x_197);
x_199 = lean_unsigned_to_nat(1u);
x_200 = lean_nat_add(x_187, x_199);
lean_dec(x_187);
x_201 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_201, 0, x_184);
lean_ctor_set(x_201, 1, x_185);
lean_ctor_set(x_201, 2, x_186);
lean_ctor_set(x_201, 3, x_200);
lean_ctor_set(x_201, 4, x_188);
lean_ctor_set(x_201, 5, x_196);
lean_ctor_set(x_201, 6, x_190);
lean_ctor_set(x_201, 7, x_191);
lean_ctor_set(x_201, 8, x_192);
lean_ctor_set(x_201, 9, x_193);
lean_ctor_set(x_201, 10, x_194);
lean_ctor_set_uint8(x_201, sizeof(void*)*11, x_195);
x_202 = lean_st_ref_get(x_5, x_13);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_205 = x_202;
} else {
 lean_dec_ref(x_202);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_203, 2);
lean_inc(x_206);
lean_dec(x_203);
x_207 = l_List_isEmpty___rarg(x_206);
lean_dec(x_206);
if (x_207 == 0)
{
uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_205);
x_208 = 0;
x_209 = lean_box(x_208);
x_210 = lean_box(x_208);
x_211 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_211, 0, x_209);
lean_closure_set(x_211, 1, x_210);
lean_inc(x_9);
lean_inc(x_201);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_212 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_208, x_208, x_4, x_5, x_6, x_7, x_201, x_9, x_204);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; uint8_t x_214; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_unbox(x_213);
lean_dec(x_213);
if (x_214 == 0)
{
if (x_1 == 0)
{
lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_215 = lean_ctor_get(x_212, 1);
lean_inc(x_215);
lean_dec(x_212);
x_216 = 1;
x_217 = lean_box(x_216);
x_218 = lean_box(x_208);
x_219 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_219, 0, x_217);
lean_closure_set(x_219, 1, x_218);
lean_inc(x_9);
lean_inc(x_201);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_220 = l_Lean_Elab_Term_withoutPostponing___rarg(x_219, x_4, x_5, x_6, x_7, x_201, x_9, x_215);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; uint8_t x_222; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_unbox(x_221);
lean_dec(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
lean_dec(x_220);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_224 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(x_4, x_5, x_6, x_7, x_201, x_9, x_223);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; uint8_t x_226; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_unbox(x_225);
lean_dec(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_224, 1);
lean_inc(x_227);
lean_dec(x_224);
lean_inc(x_9);
lean_inc(x_201);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_228 = l_Lean_Elab_Term_withoutPostponing___rarg(x_211, x_4, x_5, x_6, x_7, x_201, x_9, x_227);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; uint8_t x_230; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_unbox(x_229);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
lean_dec(x_228);
lean_inc(x_9);
lean_inc(x_201);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_232 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_208, x_216, x_4, x_5, x_6, x_7, x_201, x_9, x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; uint8_t x_234; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_unbox(x_233);
lean_dec(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_232, 1);
lean_inc(x_235);
lean_dec(x_232);
x_236 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_2, x_4, x_5, x_6, x_7, x_201, x_9, x_235);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_232, 1);
lean_inc(x_237);
lean_dec(x_232);
x_238 = lean_box(0);
x_3 = x_238;
x_8 = x_201;
x_10 = x_237;
goto _start;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_201);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_240 = lean_ctor_get(x_232, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_232, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_242 = x_232;
} else {
 lean_dec_ref(x_232);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_228, 1);
lean_inc(x_244);
lean_dec(x_228);
x_245 = lean_box(0);
x_3 = x_245;
x_8 = x_201;
x_10 = x_244;
goto _start;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_201);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_247 = lean_ctor_get(x_228, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_228, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_249 = x_228;
} else {
 lean_dec_ref(x_228);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
else
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_211);
x_251 = lean_ctor_get(x_224, 1);
lean_inc(x_251);
lean_dec(x_224);
x_252 = lean_box(0);
x_3 = x_252;
x_8 = x_201;
x_10 = x_251;
goto _start;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_211);
lean_dec(x_201);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_254 = lean_ctor_get(x_224, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_224, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_256 = x_224;
} else {
 lean_dec_ref(x_224);
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
lean_dec(x_211);
x_258 = lean_ctor_get(x_220, 1);
lean_inc(x_258);
lean_dec(x_220);
x_259 = lean_box(0);
x_3 = x_259;
x_8 = x_201;
x_10 = x_258;
goto _start;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_211);
lean_dec(x_201);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_261 = lean_ctor_get(x_220, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_220, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_263 = x_220;
} else {
 lean_dec_ref(x_220);
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
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_211);
lean_dec(x_201);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_265 = lean_ctor_get(x_212, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_266 = x_212;
} else {
 lean_dec_ref(x_212);
 x_266 = lean_box(0);
}
x_267 = lean_box(0);
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_265);
return x_268;
}
}
else
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_211);
x_269 = lean_ctor_get(x_212, 1);
lean_inc(x_269);
lean_dec(x_212);
x_270 = lean_box(0);
x_3 = x_270;
x_8 = x_201;
x_10 = x_269;
goto _start;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_211);
lean_dec(x_201);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_272 = lean_ctor_get(x_212, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_212, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_274 = x_212;
} else {
 lean_dec_ref(x_212);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
else
{
lean_object* x_276; lean_object* x_277; 
lean_dec(x_201);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_276 = lean_box(0);
if (lean_is_scalar(x_205)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_205;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_204);
return x_277;
}
}
else
{
lean_object* x_278; 
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
x_278 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1(x_196, x_4, x_5, x_6, x_7, x_197, x_9, x_13);
lean_dec(x_9);
lean_dec(x_197);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_278;
}
}
}
else
{
uint8_t x_279; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_279 = !lean_is_exclusive(x_11);
if (x_279 == 0)
{
return x_11;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_11, 0);
x_281 = lean_ctor_get(x_11, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_11);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
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
x_1 = lean_mk_string_from_bytes("not ready yet", 13);
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
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("succeeded", 9);
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
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_3);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
x_1 = lean_mk_string_from_bytes("postpone", 8);
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
x_1 = lean_mk_string_from_bytes("resuming ", 9);
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_40 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2(x_38, x_39, x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
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
x_1 = lean_mk_string_from_bytes("resuming synthetic metavariables, mayPostpone: ", 47);
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
x_1 = lean_mk_string_from_bytes(", postponeOnError: ", 19);
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
x_1 = lean_mk_string_from_bytes("false", 5);
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
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
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
x_1 = lean_mk_string_from_bytes("true", 4);
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
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
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
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
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
x_1 = lean_mk_string_from_bytes("resuming", 8);
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
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_57 = lean_ctor_get(x_34, 0);
x_58 = lean_ctor_get(x_34, 1);
x_59 = lean_ctor_get(x_34, 2);
x_60 = lean_ctor_get(x_34, 3);
x_61 = lean_ctor_get(x_34, 4);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_34);
lean_inc(x_31);
x_62 = l_List_appendTR___rarg(x_59, x_31);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_62);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
x_64 = lean_st_ref_set(x_4, x_63, x_35);
lean_dec(x_4);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = l_List_lengthTRAux___rarg(x_31, x_19);
lean_dec(x_31);
x_68 = lean_nat_dec_eq(x_20, x_67);
lean_dec(x_67);
lean_dec(x_20);
if (x_68 == 0)
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_69 = 1;
x_70 = lean_box(x_69);
if (lean_is_scalar(x_66)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_66;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_65);
return x_71;
}
else
{
uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_72 = 0;
x_73 = lean_box(x_72);
if (lean_is_scalar(x_66)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_66;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_65);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_20);
lean_dec(x_4);
x_75 = !lean_is_exclusive(x_30);
if (x_75 == 0)
{
return x_30;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_30, 0);
x_77 = lean_ctor_get(x_30, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_30);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_22, 0);
x_80 = lean_ctor_get(x_22, 1);
x_81 = lean_ctor_get(x_22, 3);
x_82 = lean_ctor_get(x_22, 4);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_22);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set(x_84, 2, x_83);
lean_ctor_set(x_84, 3, x_81);
lean_ctor_set(x_84, 4, x_82);
x_85 = lean_st_ref_set(x_4, x_84, x_23);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_List_reverse___rarg(x_18);
lean_inc(x_4);
x_88 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1(x_1, x_2, x_87, x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_st_ref_take(x_4, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 2);
lean_inc(x_96);
x_97 = lean_ctor_get(x_92, 3);
lean_inc(x_97);
x_98 = lean_ctor_get(x_92, 4);
lean_inc(x_98);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 lean_ctor_release(x_92, 3);
 lean_ctor_release(x_92, 4);
 x_99 = x_92;
} else {
 lean_dec_ref(x_92);
 x_99 = lean_box(0);
}
lean_inc(x_89);
x_100 = l_List_appendTR___rarg(x_96, x_89);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 5, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_94);
lean_ctor_set(x_101, 1, x_95);
lean_ctor_set(x_101, 2, x_100);
lean_ctor_set(x_101, 3, x_97);
lean_ctor_set(x_101, 4, x_98);
x_102 = lean_st_ref_set(x_4, x_101, x_93);
lean_dec(x_4);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = l_List_lengthTRAux___rarg(x_89, x_19);
lean_dec(x_89);
x_106 = lean_nat_dec_eq(x_20, x_105);
lean_dec(x_105);
lean_dec(x_20);
if (x_106 == 0)
{
uint8_t x_107; lean_object* x_108; lean_object* x_109; 
x_107 = 1;
x_108 = lean_box(x_107);
if (lean_is_scalar(x_104)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_104;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_103);
return x_109;
}
else
{
uint8_t x_110; lean_object* x_111; lean_object* x_112; 
x_110 = 0;
x_111 = lean_box(x_110);
if (lean_is_scalar(x_104)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_104;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_103);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_20);
lean_dec(x_4);
x_113 = lean_ctor_get(x_88, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_88, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_115 = x_88;
} else {
 lean_dec_ref(x_88);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 5);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_18 = 1;
lean_ctor_set_uint8(x_11, 9, x_18);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_13);
lean_ctor_set(x_19, 3, x_14);
lean_ctor_set(x_19, 4, x_15);
lean_ctor_set(x_19, 5, x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_19);
lean_inc(x_1);
x_20 = lean_infer_type(x_1, x_19, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_23 = l_Lean_Meta_isExprDefEq(x_21, x_2, x_19, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__1(x_1, x_2, x_3, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_5);
lean_dec(x_4);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
lean_inc(x_1);
x_30 = l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_box(0);
x_35 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__1(x_1, x_2, x_3, x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
lean_dec(x_5);
lean_dec(x_4);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = 1;
x_41 = lean_box(x_40);
lean_ctor_set(x_37, 0, x_41);
return x_37;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = 1;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
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
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_54 = lean_ctor_get_uint8(x_11, 0);
x_55 = lean_ctor_get_uint8(x_11, 1);
x_56 = lean_ctor_get_uint8(x_11, 2);
x_57 = lean_ctor_get_uint8(x_11, 3);
x_58 = lean_ctor_get_uint8(x_11, 4);
x_59 = lean_ctor_get_uint8(x_11, 5);
x_60 = lean_ctor_get_uint8(x_11, 6);
x_61 = lean_ctor_get_uint8(x_11, 7);
x_62 = lean_ctor_get_uint8(x_11, 8);
x_63 = lean_ctor_get_uint8(x_11, 10);
x_64 = lean_ctor_get_uint8(x_11, 11);
lean_dec(x_11);
x_65 = 1;
x_66 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_66, 0, x_54);
lean_ctor_set_uint8(x_66, 1, x_55);
lean_ctor_set_uint8(x_66, 2, x_56);
lean_ctor_set_uint8(x_66, 3, x_57);
lean_ctor_set_uint8(x_66, 4, x_58);
lean_ctor_set_uint8(x_66, 5, x_59);
lean_ctor_set_uint8(x_66, 6, x_60);
lean_ctor_set_uint8(x_66, 7, x_61);
lean_ctor_set_uint8(x_66, 8, x_62);
lean_ctor_set_uint8(x_66, 9, x_65);
lean_ctor_set_uint8(x_66, 10, x_63);
lean_ctor_set_uint8(x_66, 11, x_64);
x_67 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_12);
lean_ctor_set(x_67, 2, x_13);
lean_ctor_set(x_67, 3, x_14);
lean_ctor_set(x_67, 4, x_15);
lean_ctor_set(x_67, 5, x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_67);
lean_inc(x_1);
x_68 = lean_infer_type(x_1, x_67, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_71 = l_Lean_Meta_isExprDefEq(x_69, x_2, x_67, x_7, x_8, x_9, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_box(0);
x_76 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__1(x_1, x_2, x_3, x_75, x_4, x_5, x_6, x_7, x_8, x_9, x_74);
lean_dec(x_5);
lean_dec(x_4);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_dec(x_71);
lean_inc(x_1);
x_78 = l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_box(0);
x_83 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__1(x_1, x_2, x_3, x_82, x_4, x_5, x_6, x_7, x_8, x_9, x_81);
lean_dec(x_5);
lean_dec(x_4);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_2);
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
lean_dec(x_78);
x_85 = l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_84);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = 1;
x_89 = lean_box(x_88);
if (lean_is_scalar(x_87)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_87;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_86);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = lean_ctor_get(x_71, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_71, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_93 = x_71;
} else {
 lean_dec_ref(x_71);
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
lean_dec(x_67);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_ctor_get(x_68, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_68, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_97 = x_68;
} else {
 lean_dec_ref(x_68);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_runTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = 1;
x_14 = lean_box(x_13);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
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
x_3 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_Term_addTermInfo___spec__1___rarg___boxed), 8, 1);
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
lean_object* x_28; 
lean_dec(x_23);
x_28 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_28;
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 2);
lean_inc(x_30);
lean_dec(x_24);
lean_inc(x_1);
x_31 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2), 10, 3);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_29);
lean_closure_set(x_31, 2, x_1);
x_32 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_32;
}
case 2:
{
lean_dec(x_23);
if (x_3 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___closed__1;
x_35 = l_Lean_Elab_Term_withSavedContext___rarg(x_33, x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_dec(x_24);
x_38 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__3), 9, 2);
lean_closure_set(x_38, 0, x_1);
lean_closure_set(x_38, 1, x_36);
x_39 = l_Lean_Elab_Term_withSavedContext___rarg(x_37, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_39;
}
}
default: 
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_24, 0);
lean_inc(x_40);
lean_dec(x_24);
x_41 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(x_40, x_23, x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
x_44 = lean_ctor_get(x_8, 2);
x_45 = lean_ctor_get(x_8, 3);
x_46 = lean_ctor_get(x_8, 4);
x_47 = lean_ctor_get(x_8, 5);
x_48 = lean_ctor_get(x_8, 6);
x_49 = lean_ctor_get(x_8, 7);
x_50 = lean_ctor_get(x_8, 8);
x_51 = lean_ctor_get(x_8, 9);
x_52 = lean_ctor_get(x_8, 10);
x_53 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
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
lean_dec(x_8);
x_54 = l_Lean_replaceRef(x_23, x_47);
lean_dec(x_47);
x_55 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_55, 0, x_42);
lean_ctor_set(x_55, 1, x_43);
lean_ctor_set(x_55, 2, x_44);
lean_ctor_set(x_55, 3, x_45);
lean_ctor_set(x_55, 4, x_46);
lean_ctor_set(x_55, 5, x_54);
lean_ctor_set(x_55, 6, x_48);
lean_ctor_set(x_55, 7, x_49);
lean_ctor_set(x_55, 8, x_50);
lean_ctor_set(x_55, 9, x_51);
lean_ctor_set(x_55, 10, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*11, x_53);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_56; 
lean_dec(x_23);
x_56 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar(x_1, x_4, x_5, x_6, x_7, x_55, x_9, x_21);
return x_56;
}
case 1:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_23);
x_57 = lean_ctor_get(x_24, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_24, 2);
lean_inc(x_58);
lean_dec(x_24);
lean_inc(x_1);
x_59 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2), 10, 3);
lean_closure_set(x_59, 0, x_58);
lean_closure_set(x_59, 1, x_57);
lean_closure_set(x_59, 2, x_1);
x_60 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_59, x_4, x_5, x_6, x_7, x_55, x_9, x_21);
return x_60;
}
case 2:
{
lean_dec(x_23);
if (x_3 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_1);
x_61 = lean_ctor_get(x_24, 1);
lean_inc(x_61);
lean_dec(x_24);
x_62 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___closed__1;
x_63 = l_Lean_Elab_Term_withSavedContext___rarg(x_61, x_62, x_4, x_5, x_6, x_7, x_55, x_9, x_21);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_24, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_24, 1);
lean_inc(x_65);
lean_dec(x_24);
x_66 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__3), 9, 2);
lean_closure_set(x_66, 0, x_1);
lean_closure_set(x_66, 1, x_64);
x_67 = l_Lean_Elab_Term_withSavedContext___rarg(x_65, x_66, x_4, x_5, x_6, x_7, x_55, x_9, x_21);
return x_67;
}
}
default: 
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_24, 0);
lean_inc(x_68);
lean_dec(x_24);
x_69 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(x_68, x_23, x_1, x_2, x_4, x_5, x_6, x_7, x_55, x_9, x_21);
return x_69;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_13 = lean_array_uget(x_1, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__6(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_15;
x_11 = x_16;
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 3);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_17, sizeof(void*)*4);
x_22 = lean_ctor_get_uint8(x_17, sizeof(void*)*4 + 1);
lean_dec(x_17);
x_23 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_LocalContext_mkLocalDecl(x_4, x_18, x_19, x_24, x_21, x_22);
x_27 = 1;
x_28 = lean_usize_add(x_2, x_27);
x_2 = x_28;
x_4 = x_26;
x_11 = x_25;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; 
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_17, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_17, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_17, 4);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_17, sizeof(void*)*5);
x_35 = lean_ctor_get_uint8(x_17, sizeof(void*)*5 + 1);
lean_dec(x_17);
x_36 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_LocalContext_mkLetDecl(x_4, x_30, x_31, x_37, x_40, x_34, x_35);
x_43 = 1;
x_44 = lean_usize_add(x_2, x_43);
x_2 = x_44;
x_4 = x_42;
x_11 = x_41;
goto _start;
}
}
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_11);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_11, x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__7(x_10, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_array_get_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_21, x_21);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_9);
return x_26;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8(x_20, x_27, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_20);
return x_29;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArrayNode(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; uint8_t x_24; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_usize_shift_right(x_2, x_3);
x_14 = lean_usize_to_nat(x_13);
x_15 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__5___closed__1;
x_16 = lean_array_get(x_15, x_12, x_14);
x_17 = 1;
x_18 = lean_usize_shift_left(x_17, x_3);
x_19 = lean_usize_sub(x_18, x_17);
x_20 = lean_usize_land(x_2, x_19);
x_21 = 5;
x_22 = lean_usize_sub(x_3, x_21);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__5(x_16, x_20, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_14, x_27);
lean_dec(x_14);
x_29 = lean_array_get_size(x_12);
x_30 = lean_nat_dec_lt(x_28, x_29);
if (x_30 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_23;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_29, x_29);
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_23;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
lean_free_object(x_23);
x_32 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_33 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__7(x_12, x_32, x_33, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_14, x_37);
lean_dec(x_14);
x_39 = lean_array_get_size(x_12);
x_40 = lean_nat_dec_lt(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_39, x_39);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; 
x_44 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_45 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_46 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__7(x_12, x_44, x_45, x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_1, 0);
x_48 = lean_usize_to_nat(x_2);
x_49 = lean_array_get_size(x_47);
x_50 = lean_nat_dec_lt(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_11);
return x_51;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_49, x_49);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_11);
return x_53;
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; 
x_54 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_55 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_56 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8(x_47, x_54, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_Elab_Term_runTactic___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_3, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
x_14 = lean_nat_dec_le(x_13, x_3);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_17 = lean_ctor_get_usize(x_1, 4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__5(x_15, x_16, x_17, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = lean_nat_dec_lt(x_11, x_23);
if (x_24 == 0)
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_23, x_23);
if (x_25 == 0)
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
lean_free_object(x_18);
x_26 = 0;
x_27 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_28 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8(x_22, x_26, x_27, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_22);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_array_get_size(x_31);
x_33 = lean_nat_dec_lt(x_11, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_32, x_32);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
x_37 = 0;
x_38 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_39 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8(x_31, x_37, x_38, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_31);
return x_39;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_nat_sub(x_3, x_13);
lean_dec(x_13);
lean_dec(x_3);
x_42 = lean_array_get_size(x_40);
x_43 = lean_nat_dec_lt(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_10);
return x_44;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_le(x_42, x_42);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_10);
return x_46;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_48 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_49 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8(x_40, x_47, x_48, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_40);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_3);
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_51 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__6(x_50, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_array_get_size(x_55);
x_57 = lean_nat_dec_lt(x_11, x_56);
if (x_57 == 0)
{
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_51;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_56, x_56);
if (x_58 == 0)
{
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_51;
}
else
{
size_t x_59; size_t x_60; lean_object* x_61; 
lean_free_object(x_51);
x_59 = 0;
x_60 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_61 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8(x_55, x_59, x_60, x_53, x_4, x_5, x_6, x_7, x_8, x_9, x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_55);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_51, 0);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_51);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
lean_dec(x_1);
x_65 = lean_array_get_size(x_64);
x_66 = lean_nat_dec_lt(x_11, x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
else
{
uint8_t x_68; 
x_68 = lean_nat_dec_le(x_65, x_65);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
else
{
size_t x_70; size_t x_71; lean_object* x_72; 
x_70 = 0;
x_71 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_72 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8(x_64, x_70, x_71, x_62, x_4, x_5, x_6, x_7, x_8, x_9, x_63);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_64);
return x_72;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_Elab_Term_runTactic___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_PersistentArray_foldlM___at_Lean_Elab_Term_runTactic___spec__4(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__5;
x_3 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__4;
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
static lean_object* _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__3;
x_2 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__7;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_LocalContext_foldlM___at_Lean_Elab_Term_runTactic___spec__3(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
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
lean_inc(x_1);
x_13 = l_Lean_MetavarContext_getDecl(x_12, x_1);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_take(x_5, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_25, 4);
lean_ctor_set(x_13, 2, x_21);
lean_ctor_set(x_13, 1, x_18);
x_31 = l_Lean_PersistentHashMap_insert___at_Lean_instantiateMVarDeclMVars___spec__1(x_30, x_1, x_13);
lean_ctor_set(x_25, 4, x_31);
x_32 = lean_st_ref_set(x_5, x_24, x_26);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get(x_25, 1);
x_41 = lean_ctor_get(x_25, 2);
x_42 = lean_ctor_get(x_25, 3);
x_43 = lean_ctor_get(x_25, 4);
x_44 = lean_ctor_get(x_25, 5);
x_45 = lean_ctor_get(x_25, 6);
x_46 = lean_ctor_get(x_25, 7);
x_47 = lean_ctor_get(x_25, 8);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
lean_ctor_set(x_13, 2, x_21);
lean_ctor_set(x_13, 1, x_18);
x_48 = l_Lean_PersistentHashMap_insert___at_Lean_instantiateMVarDeclMVars___spec__1(x_43, x_1, x_13);
x_49 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_41);
lean_ctor_set(x_49, 3, x_42);
lean_ctor_set(x_49, 4, x_48);
lean_ctor_set(x_49, 5, x_44);
lean_ctor_set(x_49, 6, x_45);
lean_ctor_set(x_49, 7, x_46);
lean_ctor_set(x_49, 8, x_47);
lean_ctor_set(x_24, 0, x_49);
x_50 = lean_st_ref_set(x_5, x_24, x_26);
lean_dec(x_5);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
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
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_55 = lean_ctor_get(x_24, 1);
x_56 = lean_ctor_get(x_24, 2);
x_57 = lean_ctor_get(x_24, 3);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_24);
x_58 = lean_ctor_get(x_25, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_25, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_25, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_25, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_25, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_25, 5);
lean_inc(x_63);
x_64 = lean_ctor_get(x_25, 6);
lean_inc(x_64);
x_65 = lean_ctor_get(x_25, 7);
lean_inc(x_65);
x_66 = lean_ctor_get(x_25, 8);
lean_inc(x_66);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 lean_ctor_release(x_25, 5);
 lean_ctor_release(x_25, 6);
 lean_ctor_release(x_25, 7);
 lean_ctor_release(x_25, 8);
 x_67 = x_25;
} else {
 lean_dec_ref(x_25);
 x_67 = lean_box(0);
}
lean_ctor_set(x_13, 2, x_21);
lean_ctor_set(x_13, 1, x_18);
x_68 = l_Lean_PersistentHashMap_insert___at_Lean_instantiateMVarDeclMVars___spec__1(x_62, x_1, x_13);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 9, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_59);
lean_ctor_set(x_69, 2, x_60);
lean_ctor_set(x_69, 3, x_61);
lean_ctor_set(x_69, 4, x_68);
lean_ctor_set(x_69, 5, x_63);
lean_ctor_set(x_69, 6, x_64);
lean_ctor_set(x_69, 7, x_65);
lean_ctor_set(x_69, 8, x_66);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_55);
lean_ctor_set(x_70, 2, x_56);
lean_ctor_set(x_70, 3, x_57);
x_71 = lean_st_ref_set(x_5, x_70, x_26);
lean_dec(x_5);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
x_74 = lean_box(0);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_76 = lean_ctor_get(x_13, 0);
x_77 = lean_ctor_get(x_13, 1);
x_78 = lean_ctor_get(x_13, 2);
x_79 = lean_ctor_get(x_13, 3);
x_80 = lean_ctor_get(x_13, 4);
x_81 = lean_ctor_get_uint8(x_13, sizeof(void*)*7);
x_82 = lean_ctor_get(x_13, 5);
x_83 = lean_ctor_get(x_13, 6);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_84 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2(x_77, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_78, x_2, x_3, x_4, x_5, x_6, x_7, x_86);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_st_ref_take(x_5, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_91, 3);
lean_inc(x_96);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 lean_ctor_release(x_91, 3);
 x_97 = x_91;
} else {
 lean_dec_ref(x_91);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_92, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_92, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_92, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_92, 4);
lean_inc(x_102);
x_103 = lean_ctor_get(x_92, 5);
lean_inc(x_103);
x_104 = lean_ctor_get(x_92, 6);
lean_inc(x_104);
x_105 = lean_ctor_get(x_92, 7);
lean_inc(x_105);
x_106 = lean_ctor_get(x_92, 8);
lean_inc(x_106);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 lean_ctor_release(x_92, 3);
 lean_ctor_release(x_92, 4);
 lean_ctor_release(x_92, 5);
 lean_ctor_release(x_92, 6);
 lean_ctor_release(x_92, 7);
 lean_ctor_release(x_92, 8);
 x_107 = x_92;
} else {
 lean_dec_ref(x_92);
 x_107 = lean_box(0);
}
x_108 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_108, 0, x_76);
lean_ctor_set(x_108, 1, x_85);
lean_ctor_set(x_108, 2, x_88);
lean_ctor_set(x_108, 3, x_79);
lean_ctor_set(x_108, 4, x_80);
lean_ctor_set(x_108, 5, x_82);
lean_ctor_set(x_108, 6, x_83);
lean_ctor_set_uint8(x_108, sizeof(void*)*7, x_81);
x_109 = l_Lean_PersistentHashMap_insert___at_Lean_instantiateMVarDeclMVars___spec__1(x_102, x_1, x_108);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 9, 0);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_98);
lean_ctor_set(x_110, 1, x_99);
lean_ctor_set(x_110, 2, x_100);
lean_ctor_set(x_110, 3, x_101);
lean_ctor_set(x_110, 4, x_109);
lean_ctor_set(x_110, 5, x_103);
lean_ctor_set(x_110, 6, x_104);
lean_ctor_set(x_110, 7, x_105);
lean_ctor_set(x_110, 8, x_106);
if (lean_is_scalar(x_97)) {
 x_111 = lean_alloc_ctor(0, 4, 0);
} else {
 x_111 = x_97;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_94);
lean_ctor_set(x_111, 2, x_95);
lean_ctor_set(x_111, 3, x_96);
x_112 = lean_st_ref_set(x_5, x_111, x_93);
lean_dec(x_5);
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
x_115 = lean_box(0);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Term_runTactic___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_55 = lean_ctor_get(x_34, 0);
x_56 = lean_ctor_get(x_34, 1);
x_57 = lean_ctor_get(x_34, 2);
x_58 = lean_ctor_get(x_34, 3);
x_59 = lean_ctor_get(x_34, 4);
x_60 = lean_ctor_get(x_34, 5);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_34);
x_61 = lean_ctor_get_uint8(x_35, sizeof(void*)*2);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_63 = x_35;
} else {
 lean_dec_ref(x_35);
 x_63 = lean_box(0);
}
x_64 = l_Lean_PersistentArray_push___rarg(x_20, x_31);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 1);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_61);
x_66 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_56);
lean_ctor_set(x_66, 2, x_57);
lean_ctor_set(x_66, 3, x_58);
lean_ctor_set(x_66, 4, x_59);
lean_ctor_set(x_66, 5, x_60);
lean_ctor_set(x_66, 6, x_65);
x_67 = lean_st_ref_set(x_10, x_66, x_36);
lean_dec(x_10);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_23);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_10);
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
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_22, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_22, 1);
lean_inc(x_76);
lean_dec(x_22);
x_77 = lean_st_ref_get(x_10, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 6);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
lean_inc(x_10);
x_82 = lean_apply_10(x_2, x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_79);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_st_ref_take(x_10, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 6);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_86, 6);
lean_dec(x_90);
x_91 = !lean_is_exclusive(x_87);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_87, 1);
lean_dec(x_92);
x_93 = l_Lean_PersistentArray_push___rarg(x_20, x_83);
lean_ctor_set(x_87, 1, x_93);
x_94 = lean_st_ref_set(x_10, x_86, x_88);
lean_dec(x_10);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
lean_ctor_set_tag(x_94, 1);
lean_ctor_set(x_94, 0, x_75);
return x_94;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_75);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_99 = lean_ctor_get_uint8(x_87, sizeof(void*)*2);
x_100 = lean_ctor_get(x_87, 0);
lean_inc(x_100);
lean_dec(x_87);
x_101 = l_Lean_PersistentArray_push___rarg(x_20, x_83);
x_102 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_99);
lean_ctor_set(x_86, 6, x_102);
x_103 = lean_st_ref_set(x_10, x_86, x_88);
lean_dec(x_10);
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
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
 lean_ctor_set_tag(x_106, 1);
}
lean_ctor_set(x_106, 0, x_75);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_107 = lean_ctor_get(x_86, 0);
x_108 = lean_ctor_get(x_86, 1);
x_109 = lean_ctor_get(x_86, 2);
x_110 = lean_ctor_get(x_86, 3);
x_111 = lean_ctor_get(x_86, 4);
x_112 = lean_ctor_get(x_86, 5);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_86);
x_113 = lean_ctor_get_uint8(x_87, sizeof(void*)*2);
x_114 = lean_ctor_get(x_87, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_115 = x_87;
} else {
 lean_dec_ref(x_87);
 x_115 = lean_box(0);
}
x_116 = l_Lean_PersistentArray_push___rarg(x_20, x_83);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 1);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*2, x_113);
x_118 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_118, 0, x_107);
lean_ctor_set(x_118, 1, x_108);
lean_ctor_set(x_118, 2, x_109);
lean_ctor_set(x_118, 3, x_110);
lean_ctor_set(x_118, 4, x_111);
lean_ctor_set(x_118, 5, x_112);
lean_ctor_set(x_118, 6, x_117);
x_119 = lean_st_ref_set(x_10, x_118, x_88);
lean_dec(x_10);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
 lean_ctor_set_tag(x_122, 1);
}
lean_ctor_set(x_122, 0, x_75);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
uint8_t x_123; 
lean_dec(x_75);
lean_dec(x_20);
lean_dec(x_10);
x_123 = !lean_is_exclusive(x_82);
if (x_123 == 0)
{
return x_82;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_82, 0);
x_125 = lean_ctor_get(x_82, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_82);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runTactic___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
x_15 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_MVarId_admit(x_14, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_box(0);
x_3 = x_19;
x_4 = x_20;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_16 = l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Term_runTactic___spec__9(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_18, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_59; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_11 = l_Lean_instantiateMVarDeclMVars___at_Lean_Elab_Term_runTactic___spec__1(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_13 = x_11;
} else {
 lean_dec_ref(x_11);
 x_13 = lean_box(0);
}
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_2, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic), 10, 1);
lean_closure_set(x_16, 0, x_3);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg), 11, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lambda__2), 11, 2);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_17);
x_79 = lean_st_ref_get(x_9, x_12);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 6);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_ctor_get_uint8(x_81, sizeof(void*)*2);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_84 = l_Lean_Elab_Tactic_run(x_1, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_83);
x_59 = x_84;
goto block_78;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_dec(x_79);
x_86 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__2___rarg(x_9, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_89 = l_Lean_Elab_Tactic_run(x_1, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_st_ref_take(x_9, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 6);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = !lean_is_exclusive(x_93);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_93, 6);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_94);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_94, 0);
x_100 = lean_ctor_get(x_94, 1);
x_101 = lean_ctor_get(x_100, 2);
lean_inc(x_101);
x_102 = lean_nat_dec_lt(x_14, x_101);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
lean_dec(x_101);
lean_dec(x_100);
lean_ctor_set(x_94, 1, x_87);
x_103 = lean_st_ref_set(x_9, x_93, x_95);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_103, 0);
lean_dec(x_105);
lean_ctor_set(x_103, 0, x_90);
x_59 = x_103;
goto block_78;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_90);
lean_ctor_set(x_107, 1, x_106);
x_59 = x_107;
goto block_78;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_108 = lean_unsigned_to_nat(1u);
x_109 = lean_nat_sub(x_101, x_108);
lean_dec(x_101);
x_110 = l_Lean_Elab_instInhabitedInfoTree;
x_111 = l_Lean_PersistentArray_get_x21___rarg(x_110, x_100, x_109);
lean_dec(x_109);
lean_inc(x_1);
x_112 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_99, x_1, x_111);
lean_ctor_set(x_94, 1, x_87);
lean_ctor_set(x_94, 0, x_112);
x_113 = lean_st_ref_set(x_9, x_93, x_95);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_113, 0);
lean_dec(x_115);
lean_ctor_set(x_113, 0, x_90);
x_59 = x_113;
goto block_78;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_90);
lean_ctor_set(x_117, 1, x_116);
x_59 = x_117;
goto block_78;
}
}
}
else
{
uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_118 = lean_ctor_get_uint8(x_94, sizeof(void*)*2);
x_119 = lean_ctor_get(x_94, 0);
x_120 = lean_ctor_get(x_94, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_94);
x_121 = lean_ctor_get(x_120, 2);
lean_inc(x_121);
x_122 = lean_nat_dec_lt(x_14, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_121);
lean_dec(x_120);
x_123 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_87);
lean_ctor_set_uint8(x_123, sizeof(void*)*2, x_118);
lean_ctor_set(x_93, 6, x_123);
x_124 = lean_st_ref_set(x_9, x_93, x_95);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_90);
lean_ctor_set(x_127, 1, x_125);
x_59 = x_127;
goto block_78;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_nat_sub(x_121, x_128);
lean_dec(x_121);
x_130 = l_Lean_Elab_instInhabitedInfoTree;
x_131 = l_Lean_PersistentArray_get_x21___rarg(x_130, x_120, x_129);
lean_dec(x_129);
lean_inc(x_1);
x_132 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_119, x_1, x_131);
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_87);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_118);
lean_ctor_set(x_93, 6, x_133);
x_134 = lean_st_ref_set(x_9, x_93, x_95);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_90);
lean_ctor_set(x_137, 1, x_135);
x_59 = x_137;
goto block_78;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_138 = lean_ctor_get(x_93, 0);
x_139 = lean_ctor_get(x_93, 1);
x_140 = lean_ctor_get(x_93, 2);
x_141 = lean_ctor_get(x_93, 3);
x_142 = lean_ctor_get(x_93, 4);
x_143 = lean_ctor_get(x_93, 5);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_93);
x_144 = lean_ctor_get_uint8(x_94, sizeof(void*)*2);
x_145 = lean_ctor_get(x_94, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_94, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_147 = x_94;
} else {
 lean_dec_ref(x_94);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_146, 2);
lean_inc(x_148);
x_149 = lean_nat_dec_lt(x_14, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_148);
lean_dec(x_146);
if (lean_is_scalar(x_147)) {
 x_150 = lean_alloc_ctor(0, 2, 1);
} else {
 x_150 = x_147;
}
lean_ctor_set(x_150, 0, x_145);
lean_ctor_set(x_150, 1, x_87);
lean_ctor_set_uint8(x_150, sizeof(void*)*2, x_144);
x_151 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_151, 0, x_138);
lean_ctor_set(x_151, 1, x_139);
lean_ctor_set(x_151, 2, x_140);
lean_ctor_set(x_151, 3, x_141);
lean_ctor_set(x_151, 4, x_142);
lean_ctor_set(x_151, 5, x_143);
lean_ctor_set(x_151, 6, x_150);
x_152 = lean_st_ref_set(x_9, x_151, x_95);
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
lean_ctor_set(x_155, 0, x_90);
lean_ctor_set(x_155, 1, x_153);
x_59 = x_155;
goto block_78;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_156 = lean_unsigned_to_nat(1u);
x_157 = lean_nat_sub(x_148, x_156);
lean_dec(x_148);
x_158 = l_Lean_Elab_instInhabitedInfoTree;
x_159 = l_Lean_PersistentArray_get_x21___rarg(x_158, x_146, x_157);
lean_dec(x_157);
lean_inc(x_1);
x_160 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_145, x_1, x_159);
if (lean_is_scalar(x_147)) {
 x_161 = lean_alloc_ctor(0, 2, 1);
} else {
 x_161 = x_147;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_87);
lean_ctor_set_uint8(x_161, sizeof(void*)*2, x_144);
x_162 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_162, 0, x_138);
lean_ctor_set(x_162, 1, x_139);
lean_ctor_set(x_162, 2, x_140);
lean_ctor_set(x_162, 3, x_141);
lean_ctor_set(x_162, 4, x_142);
lean_ctor_set(x_162, 5, x_143);
lean_ctor_set(x_162, 6, x_161);
x_163 = lean_st_ref_set(x_9, x_162, x_95);
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
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_90);
lean_ctor_set(x_166, 1, x_164);
x_59 = x_166;
goto block_78;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_167 = lean_ctor_get(x_89, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_89, 1);
lean_inc(x_168);
lean_dec(x_89);
x_169 = lean_st_ref_take(x_9, x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_170, 6);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = !lean_is_exclusive(x_170);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_ctor_get(x_170, 6);
lean_dec(x_174);
x_175 = !lean_is_exclusive(x_171);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_176 = lean_ctor_get(x_171, 0);
x_177 = lean_ctor_get(x_171, 1);
x_178 = lean_ctor_get(x_177, 2);
lean_inc(x_178);
x_179 = lean_nat_dec_lt(x_14, x_178);
if (x_179 == 0)
{
lean_object* x_180; uint8_t x_181; 
lean_dec(x_178);
lean_dec(x_177);
lean_ctor_set(x_171, 1, x_87);
x_180 = lean_st_ref_set(x_9, x_170, x_172);
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_180, 0);
lean_dec(x_182);
lean_ctor_set_tag(x_180, 1);
lean_ctor_set(x_180, 0, x_167);
x_59 = x_180;
goto block_78;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_167);
lean_ctor_set(x_184, 1, x_183);
x_59 = x_184;
goto block_78;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_185 = lean_unsigned_to_nat(1u);
x_186 = lean_nat_sub(x_178, x_185);
lean_dec(x_178);
x_187 = l_Lean_Elab_instInhabitedInfoTree;
x_188 = l_Lean_PersistentArray_get_x21___rarg(x_187, x_177, x_186);
lean_dec(x_186);
lean_inc(x_1);
x_189 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_176, x_1, x_188);
lean_ctor_set(x_171, 1, x_87);
lean_ctor_set(x_171, 0, x_189);
x_190 = lean_st_ref_set(x_9, x_170, x_172);
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_190, 0);
lean_dec(x_192);
lean_ctor_set_tag(x_190, 1);
lean_ctor_set(x_190, 0, x_167);
x_59 = x_190;
goto block_78;
}
else
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_dec(x_190);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_167);
lean_ctor_set(x_194, 1, x_193);
x_59 = x_194;
goto block_78;
}
}
}
else
{
uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_195 = lean_ctor_get_uint8(x_171, sizeof(void*)*2);
x_196 = lean_ctor_get(x_171, 0);
x_197 = lean_ctor_get(x_171, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_171);
x_198 = lean_ctor_get(x_197, 2);
lean_inc(x_198);
x_199 = lean_nat_dec_lt(x_14, x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_198);
lean_dec(x_197);
x_200 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_200, 0, x_196);
lean_ctor_set(x_200, 1, x_87);
lean_ctor_set_uint8(x_200, sizeof(void*)*2, x_195);
lean_ctor_set(x_170, 6, x_200);
x_201 = lean_st_ref_set(x_9, x_170, x_172);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
 lean_ctor_set_tag(x_204, 1);
}
lean_ctor_set(x_204, 0, x_167);
lean_ctor_set(x_204, 1, x_202);
x_59 = x_204;
goto block_78;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_205 = lean_unsigned_to_nat(1u);
x_206 = lean_nat_sub(x_198, x_205);
lean_dec(x_198);
x_207 = l_Lean_Elab_instInhabitedInfoTree;
x_208 = l_Lean_PersistentArray_get_x21___rarg(x_207, x_197, x_206);
lean_dec(x_206);
lean_inc(x_1);
x_209 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_196, x_1, x_208);
x_210 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_87);
lean_ctor_set_uint8(x_210, sizeof(void*)*2, x_195);
lean_ctor_set(x_170, 6, x_210);
x_211 = lean_st_ref_set(x_9, x_170, x_172);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_213 = x_211;
} else {
 lean_dec_ref(x_211);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
 lean_ctor_set_tag(x_214, 1);
}
lean_ctor_set(x_214, 0, x_167);
lean_ctor_set(x_214, 1, x_212);
x_59 = x_214;
goto block_78;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_215 = lean_ctor_get(x_170, 0);
x_216 = lean_ctor_get(x_170, 1);
x_217 = lean_ctor_get(x_170, 2);
x_218 = lean_ctor_get(x_170, 3);
x_219 = lean_ctor_get(x_170, 4);
x_220 = lean_ctor_get(x_170, 5);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_170);
x_221 = lean_ctor_get_uint8(x_171, sizeof(void*)*2);
x_222 = lean_ctor_get(x_171, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_171, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_224 = x_171;
} else {
 lean_dec_ref(x_171);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_223, 2);
lean_inc(x_225);
x_226 = lean_nat_dec_lt(x_14, x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_225);
lean_dec(x_223);
if (lean_is_scalar(x_224)) {
 x_227 = lean_alloc_ctor(0, 2, 1);
} else {
 x_227 = x_224;
}
lean_ctor_set(x_227, 0, x_222);
lean_ctor_set(x_227, 1, x_87);
lean_ctor_set_uint8(x_227, sizeof(void*)*2, x_221);
x_228 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_228, 0, x_215);
lean_ctor_set(x_228, 1, x_216);
lean_ctor_set(x_228, 2, x_217);
lean_ctor_set(x_228, 3, x_218);
lean_ctor_set(x_228, 4, x_219);
lean_ctor_set(x_228, 5, x_220);
lean_ctor_set(x_228, 6, x_227);
x_229 = lean_st_ref_set(x_9, x_228, x_172);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_231 = x_229;
} else {
 lean_dec_ref(x_229);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_231;
 lean_ctor_set_tag(x_232, 1);
}
lean_ctor_set(x_232, 0, x_167);
lean_ctor_set(x_232, 1, x_230);
x_59 = x_232;
goto block_78;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_233 = lean_unsigned_to_nat(1u);
x_234 = lean_nat_sub(x_225, x_233);
lean_dec(x_225);
x_235 = l_Lean_Elab_instInhabitedInfoTree;
x_236 = l_Lean_PersistentArray_get_x21___rarg(x_235, x_223, x_234);
lean_dec(x_234);
lean_inc(x_1);
x_237 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_222, x_1, x_236);
if (lean_is_scalar(x_224)) {
 x_238 = lean_alloc_ctor(0, 2, 1);
} else {
 x_238 = x_224;
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_87);
lean_ctor_set_uint8(x_238, sizeof(void*)*2, x_221);
x_239 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_239, 0, x_215);
lean_ctor_set(x_239, 1, x_216);
lean_ctor_set(x_239, 2, x_217);
lean_ctor_set(x_239, 3, x_218);
lean_ctor_set(x_239, 4, x_219);
lean_ctor_set(x_239, 5, x_220);
lean_ctor_set(x_239, 6, x_238);
x_240 = lean_st_ref_set(x_9, x_239, x_172);
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
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
 lean_ctor_set_tag(x_243, 1);
}
lean_ctor_set(x_243, 0, x_167);
lean_ctor_set(x_243, 1, x_241);
x_59 = x_243;
goto block_78;
}
}
}
}
block_58:
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_13)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_13;
 lean_ctor_set_tag(x_23, 1);
}
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_13);
x_24 = l_Lean_Expr_mvar___override(x_1);
x_25 = l_Lean_Meta_getMVars(x_24, x_6, x_7, x_8, x_9, x_20);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_array_get_size(x_26);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = 0;
x_31 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_32 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runTactic___spec__10(x_26, x_29, x_30, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
lean_dec(x_26);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
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
x_39 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_13)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_13;
 lean_ctor_set_tag(x_40, 1);
}
lean_ctor_set(x_40, 0, x_19);
lean_ctor_set(x_40, 1, x_20);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_13)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_13;
 lean_ctor_set_tag(x_42, 1);
}
lean_ctor_set(x_42, 0, x_19);
lean_ctor_set(x_42, 1, x_20);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_13);
x_43 = l_Lean_Expr_mvar___override(x_1);
x_44 = l_Lean_Meta_getMVars(x_43, x_6, x_7, x_8, x_9, x_20);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_array_get_size(x_45);
x_48 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_49 = 0;
x_50 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runTactic___spec__10(x_45, x_48, x_49, x_50, x_4, x_5, x_6, x_7, x_8, x_9, x_46);
lean_dec(x_45);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
}
block_78:
{
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
x_63 = l_List_isEmpty___rarg(x_61);
if (x_63 == 0)
{
lean_object* x_64; 
lean_free_object(x_59);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_64 = l_Lean_Elab_Term_reportUnsolvedGoals(x_61, x_6, x_7, x_8, x_9, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_19 = x_65;
x_20 = x_66;
goto block_58;
}
}
else
{
lean_object* x_67; 
lean_dec(x_61);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_67 = lean_box(0);
lean_ctor_set(x_59, 0, x_67);
return x_59;
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_59, 0);
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_59);
x_70 = l_List_isEmpty___rarg(x_68);
if (x_70 == 0)
{
lean_object* x_71; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_71 = l_Lean_Elab_Term_reportUnsolvedGoals(x_68, x_6, x_7, x_8, x_9, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_19 = x_72;
x_20 = x_73;
goto block_58;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_68);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_69);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_59, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_59, 1);
lean_inc(x_77);
lean_dec(x_59);
x_19 = x_76;
x_20 = x_77;
goto block_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_2, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lambda__3), 10, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_11);
x_13 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
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
if (x_1 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_processPostponedUniverseContraints(x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__7(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__5(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runTactic___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runTactic___spec__10(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
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
x_9 = 0;
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
x_18 = 1;
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
x_8 = 1;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_5, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_51; lean_object* x_52; lean_object* x_76; 
x_19 = lean_ctor_get(x_16, 2);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_16, 2, x_20);
x_21 = lean_st_ref_set(x_5, x_16, x_17);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_76 = lean_apply_7(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_80 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_2, x_79, x_4, x_5, x_6, x_7, x_8, x_9, x_78);
if (lean_obj_tag(x_80) == 0)
{
if (x_2 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_box(0);
x_83 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1(x_77, x_82, x_4, x_5, x_6, x_7, x_8, x_9, x_81);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_23 = x_84;
x_24 = x_85;
goto block_50;
}
else
{
if (x_3 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_dec(x_80);
x_87 = lean_box(0);
x_88 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1(x_77, x_87, x_4, x_5, x_6, x_7, x_8, x_9, x_86);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_23 = x_89;
x_24 = x_90;
goto block_50;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_80, 1);
lean_inc(x_91);
lean_dec(x_80);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_92 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultLoop(x_4, x_5, x_6, x_7, x_8, x_9, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1(x_77, x_93, x_4, x_5, x_6, x_7, x_8, x_9, x_94);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_93);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_23 = x_96;
x_24 = x_97;
goto block_50;
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_77);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_98 = lean_ctor_get(x_92, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
lean_dec(x_92);
x_51 = x_98;
x_52 = x_99;
goto block_75;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_77);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_100 = lean_ctor_get(x_80, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_80, 1);
lean_inc(x_101);
lean_dec(x_80);
x_51 = x_100;
x_52 = x_101;
goto block_75;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_102 = lean_ctor_get(x_76, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_76, 1);
lean_inc(x_103);
lean_dec(x_76);
x_51 = x_102;
x_52 = x_103;
goto block_75;
}
block_50:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_st_ref_take(x_5, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_26, 2);
x_30 = l_List_appendTR___rarg(x_29, x_14);
lean_ctor_set(x_26, 2, x_30);
x_31 = lean_st_ref_set(x_5, x_26, x_27);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
lean_dec(x_23);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec(x_23);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
x_40 = lean_ctor_get(x_26, 2);
x_41 = lean_ctor_get(x_26, 3);
x_42 = lean_ctor_get(x_26, 4);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_26);
x_43 = l_List_appendTR___rarg(x_40, x_14);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_41);
lean_ctor_set(x_44, 4, x_42);
x_45 = lean_st_ref_set(x_5, x_44, x_27);
lean_dec(x_5);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_23, 0);
lean_inc(x_48);
lean_dec(x_23);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
block_75:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_st_ref_take(x_5, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_54, 2);
x_58 = l_List_appendTR___rarg(x_57, x_14);
lean_ctor_set(x_54, 2, x_58);
x_59 = lean_st_ref_set(x_5, x_54, x_55);
lean_dec(x_5);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set_tag(x_59, 1);
lean_ctor_set(x_59, 0, x_51);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_51);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_64 = lean_ctor_get(x_54, 0);
x_65 = lean_ctor_get(x_54, 1);
x_66 = lean_ctor_get(x_54, 2);
x_67 = lean_ctor_get(x_54, 3);
x_68 = lean_ctor_get(x_54, 4);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_54);
x_69 = l_List_appendTR___rarg(x_66, x_14);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_65);
lean_ctor_set(x_70, 2, x_69);
lean_ctor_set(x_70, 3, x_67);
lean_ctor_set(x_70, 4, x_68);
x_71 = lean_st_ref_set(x_5, x_70, x_55);
lean_dec(x_5);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
 lean_ctor_set_tag(x_74, 1);
}
lean_ctor_set(x_74, 0, x_51);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_131; lean_object* x_132; lean_object* x_149; 
x_104 = lean_ctor_get(x_16, 0);
x_105 = lean_ctor_get(x_16, 1);
x_106 = lean_ctor_get(x_16, 3);
x_107 = lean_ctor_get(x_16, 4);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_16);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_106);
lean_ctor_set(x_109, 4, x_107);
x_110 = lean_st_ref_set(x_5, x_109, x_17);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_149 = lean_apply_7(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_111);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_153 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_2, x_152, x_4, x_5, x_6, x_7, x_8, x_9, x_151);
if (lean_obj_tag(x_153) == 0)
{
if (x_2 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_155 = lean_box(0);
x_156 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1(x_150, x_155, x_4, x_5, x_6, x_7, x_8, x_9, x_154);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_112 = x_157;
x_113 = x_158;
goto block_130;
}
else
{
if (x_3 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = lean_ctor_get(x_153, 1);
lean_inc(x_159);
lean_dec(x_153);
x_160 = lean_box(0);
x_161 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1(x_150, x_160, x_4, x_5, x_6, x_7, x_8, x_9, x_159);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_112 = x_162;
x_113 = x_163;
goto block_130;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_153, 1);
lean_inc(x_164);
lean_dec(x_153);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_165 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultLoop(x_4, x_5, x_6, x_7, x_8, x_9, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1(x_150, x_166, x_4, x_5, x_6, x_7, x_8, x_9, x_167);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_166);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_112 = x_169;
x_113 = x_170;
goto block_130;
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_150);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_171 = lean_ctor_get(x_165, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_165, 1);
lean_inc(x_172);
lean_dec(x_165);
x_131 = x_171;
x_132 = x_172;
goto block_148;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_150);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_173 = lean_ctor_get(x_153, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_153, 1);
lean_inc(x_174);
lean_dec(x_153);
x_131 = x_173;
x_132 = x_174;
goto block_148;
}
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_175 = lean_ctor_get(x_149, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_149, 1);
lean_inc(x_176);
lean_dec(x_149);
x_131 = x_175;
x_132 = x_176;
goto block_148;
}
block_130:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_114 = lean_st_ref_take(x_5, x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_115, 4);
lean_inc(x_121);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 lean_ctor_release(x_115, 2);
 lean_ctor_release(x_115, 3);
 lean_ctor_release(x_115, 4);
 x_122 = x_115;
} else {
 lean_dec_ref(x_115);
 x_122 = lean_box(0);
}
x_123 = l_List_appendTR___rarg(x_119, x_14);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 5, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_117);
lean_ctor_set(x_124, 1, x_118);
lean_ctor_set(x_124, 2, x_123);
lean_ctor_set(x_124, 3, x_120);
lean_ctor_set(x_124, 4, x_121);
x_125 = lean_st_ref_set(x_5, x_124, x_116);
lean_dec(x_5);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_112, 0);
lean_inc(x_128);
lean_dec(x_112);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
return x_129;
}
block_148:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_133 = lean_st_ref_take(x_5, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_134, 3);
lean_inc(x_139);
x_140 = lean_ctor_get(x_134, 4);
lean_inc(x_140);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 lean_ctor_release(x_134, 2);
 lean_ctor_release(x_134, 3);
 lean_ctor_release(x_134, 4);
 x_141 = x_134;
} else {
 lean_dec_ref(x_134);
 x_141 = lean_box(0);
}
x_142 = l_List_appendTR___rarg(x_138, x_14);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 5, 0);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_136);
lean_ctor_set(x_143, 1, x_137);
lean_ctor_set(x_143, 2, x_142);
lean_ctor_set(x_143, 3, x_139);
lean_ctor_set(x_143, 4, x_140);
x_144 = lean_st_ref_set(x_5, x_143, x_135);
lean_dec(x_5);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
 lean_ctor_set_tag(x_147, 1);
}
lean_ctor_set(x_147, 0, x_131);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___boxed), 10, 0);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___rarg___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_3, x_1, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withSynthesize___rarg___lambda__1___boxed), 10, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_apply_3(x_1, lean_box(0), x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withSynthesize___rarg___boxed), 4, 0);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Elab_Term_withSynthesize___rarg(x_1, x_2, x_3, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = 0;
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_withSynthesizeLight___rarg___closed__1;
x_5 = lean_apply_3(x_1, lean_box(0), x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withSynthesizeLight___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_withSynthesizeLight___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
x_17 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_13, x_17, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
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
x_37 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
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
x_38 = l_Lean_replaceRef(x_1, x_31);
lean_dec(x_31);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_39, 0, x_26);
lean_ctor_set(x_39, 1, x_27);
lean_ctor_set(x_39, 2, x_28);
lean_ctor_set(x_39, 3, x_29);
lean_ctor_set(x_39, 4, x_30);
lean_ctor_set(x_39, 5, x_38);
lean_ctor_set(x_39, 6, x_32);
lean_ctor_set(x_39, 7, x_33);
lean_ctor_set(x_39, 8, x_34);
lean_ctor_set(x_39, 9, x_35);
lean_ctor_set(x_39, 10, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*11, x_37);
x_40 = 0;
lean_inc(x_8);
lean_inc(x_39);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_41 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_13, x_40, x_10, x_3, x_4, x_5, x_6, x_39, x_8, x_9);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_42, x_3, x_4, x_5, x_6, x_39, x_8, x_43);
lean_dec(x_8);
lean_dec(x_39);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_Elab_Term_runTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
x_22 = l_Lean_getDelayedMVarRoot___at_Lean_Elab_Term_isLetRecAuxMVar___spec__1(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Term_getSyntheticMVarDecl_x3f(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1;
x_15 = x_28;
x_16 = x_27;
goto block_21;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 2)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___lambda__1), 9, 2);
lean_closure_set(x_34, 0, x_23);
lean_closure_set(x_34, 1, x_32);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_35 = l_Lean_Elab_Term_withSavedContext___rarg(x_33, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1;
x_15 = x_37;
x_16 = x_36;
goto block_21;
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_30);
lean_dec(x_23);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_dec(x_25);
x_43 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1;
x_15 = x_43;
x_16 = x_42;
goto block_21;
}
}
block_21:
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_4 = x_17;
x_11 = x_16;
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
x_12 = lean_array_get_size(x_10);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = lean_box(0);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1(x_10, x_13, x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("resume", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__4;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__5;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__7;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__9;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__11;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__12;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("SyntheticMVars", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__13;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__15;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__17;
x_2 = lean_unsigned_to_nat(7658u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__2;
x_3 = 0;
x_4 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__18;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_OccursCheck(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
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
l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__15___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__2);
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
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___closed__1);
l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__5___closed__1 = _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__5___closed__1();
lean_mark_persistent(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__5___closed__1);
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
l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__7 = _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__7();
lean_mark_persistent(l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__7);
l_Lean_Elab_Term_withSynthesizeLight___rarg___closed__1 = _init_l_Lean_Elab_Term_withSynthesizeLight___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_withSynthesizeLight___rarg___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__1 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__1();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__1);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__2 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__2();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__2);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__3 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__3();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__3);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__4 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__4();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__4);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__5 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__5();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__5);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__6 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__6();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__6);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__7 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__7();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__7);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__8 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__8();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__8);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__9 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__9();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__9);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__10 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__10();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__10);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__11 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__11();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__11);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__12 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__12();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__12);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__13 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__13();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__13);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__14 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__14();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__14);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__15 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__15();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__15);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__16 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__16();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__16);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__17 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__17();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__17);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__18 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__18();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658____closed__18);
if (builtin) {res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7658_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
