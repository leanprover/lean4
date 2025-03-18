// Lean compiler output
// Module: Lean.Elab.Tactic.Try
// Imports: Init.Try Init.Grind.Tactics Lean.Meta.Tactic.ExposeNames Lean.Meta.Tactic.Try Lean.Meta.Tactic.TryThis Lean.Elab.Tactic.Config Lean.Elab.Tactic.SimpTrace Lean.Elab.Tactic.LibrarySearch Lean.Elab.Tactic.Grind
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalAndSuggest___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___closed__1;
lean_object* l_Lean_Elab_Tactic_setGrindParams(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___lambda__1___boxed(lean_object**);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeGrind_x3f___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_withNonTerminal___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__6;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabTryConfig___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__7;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__12;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalTryTrace___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_observing___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__1(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__7;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__3;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__2(lean_object*, lean_object*, size_t, size_t);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__5;
lean_object* l_Lean_Meta_LibrarySearch_solveByElim(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_LibrarySearch_librarySearch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSuggestion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__2;
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__1;
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__3;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___boxed(lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__11;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeSimp_x3f(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__3;
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__3;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__3;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_setSimpParams(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__3;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__3;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FunInd_SeenCalls_uniques(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__1;
lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__8;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeSimp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4___closed__1;
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__17;
lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__5___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion___closed__2;
static lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__3;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__4;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq___spec__1(lean_object*, size_t, size_t);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__9;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeGrind_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__4(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__4;
static lean_object* l_Lean_Elab_Tactic_Try_evalTryTrace___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__3___boxed(lean_object**);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_withNonTerminal(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalTryTrace___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__9;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__5(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___spec__1___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__2;
static lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___boxed__const__1;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___closed__1;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__13;
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getSimpParams(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_focus___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabTryConfig___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2___boxed(lean_object**);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_suggest_tactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions___spec__1(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__3;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___closed__1;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4;
lean_object* lean_array_to_list(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__4;
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__4;
lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic___closed__1;
lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_merge_x3f(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__4;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeGrind_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__3;
lean_object* l_Lean_Expr_constName_x21(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__5;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionsCore(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__3;
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___lambda__1(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__3___closed__2;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__1;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions(lean_object*);
uint8_t l_Lean_Elab_Tactic_isSimpOnly(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalAndSuggest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_Try_Collector_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___closed__1;
lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__6;
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__10;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__2;
LEAN_EXPORT uint8_t l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__12;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__2___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__6;
lean_object* l_Lean_Elab_Tactic_elabGrindConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__6;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__5___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__4;
LEAN_EXPORT uint8_t l_Array_contains___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__7;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___lambda__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__5;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__1;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__9;
lean_object* l_Array_mkArray3___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalTryTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__18(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__8___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__8;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__6;
lean_object* l_Lean_Elab_Tactic_mkGrindOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__8(lean_object*, size_t, size_t);
lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_checkTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__3___closed__1;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__7(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeSimp_x3f___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__10;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___spec__1(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toIdent___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__1___closed__1;
lean_object* l_Array_mkArray1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_Try_evalSuggestExact___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__5;
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___boxed(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__1;
static double l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10___closed__1;
lean_object* l_Array_back_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalTryTrace___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__1(lean_object*, size_t, size_t);
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___closed__2;
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__3;
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
lean_object* l_Lean_Elab_Tactic_evalGrindCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__2(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Elab_Tactic_getGrindParams(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledForCore(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__2;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__5;
size_t lean_array_size(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12___closed__1;
static lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalAndSuggest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalAndSuggest___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__2;
uint8_t l_Lean_Elab_Tactic_isGrindOnly(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___closed__1;
LEAN_EXPORT lean_object* l_List_beq___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__16;
static lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___lambda__2___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__7;
lean_object* l_Lean_Meta_evalExpr_x27___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion___closed__1;
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_Try_evalSuggestExact___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_observing(lean_object*);
lean_object* l_Array_mkArray2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_focus(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__6(size_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___closed__2;
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__11;
LEAN_EXPORT lean_object* lean_eval_suggest_tactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__2___closed__1;
lean_object* l_Lean_Meta_withExposedNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__3;
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
uint8_t l_Array_contains___at_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___spec__4(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__3(lean_object*, lean_object*, size_t, size_t);
static lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__4___boxed(lean_object**);
static lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__7___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__2;
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Config", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__2;
x_3 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__4;
x_10 = 0;
x_11 = l_Lean_Meta_evalExpr_x27___rarg(x_9, x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabTryConfig___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 1);
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
static lean_object* _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error evaluating configuration\n", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nException: ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6_(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_22 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__2;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Exception_toMessageData(x_16);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at_Lean_Elab_Tactic_elabTryConfig___spec__1(x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
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
x_41 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__2;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__4;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Exception_toMessageData(x_35);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Lean_Elab_Tactic_elabTryConfig___spec__1(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
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
static lean_object* _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabTryConfig___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasSorry(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_13 = l_Lean_Elab_Tactic_elabTryConfig___lambda__2___closed__2;
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
static lean_object* _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__3___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = 0;
x_3 = lean_unsigned_to_nat(8u);
x_4 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 2, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 3, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 4, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 5, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1 + 6, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__4;
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
x_18 = l_Lean_Elab_Tactic_elabTryConfig___lambda__2(x_14, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
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
x_19 = l_Lean_Elab_Tactic_elabTryConfig___lambda__3___closed__1;
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
x_24 = l_Lean_Elab_Tactic_elabTryConfig___lambda__2(x_20, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
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
x_25 = l_Lean_Elab_Tactic_elabTryConfig___lambda__3___closed__1;
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
static lean_object* _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__4;
x_2 = l_Lean_MessageData_ofName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__2;
x_2 = l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__3;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__4;
x_2 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_15 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__4;
x_16 = l_Lean_Environment_contains(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
x_17 = l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__5;
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
x_24 = l_Lean_Elab_Tactic_elabTryConfig___lambda__3(x_1, x_2, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_19 = l_Lean_Elab_Tactic_elabTryConfig___lambda__4(x_11, x_13, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_37 = l_Lean_Elab_Tactic_elabTryConfig___lambda__4(x_11, x_13, x_36, x_4, x_5, x_6, x_7, x_35, x_9, x_10);
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
x_38 = l_Lean_Elab_Tactic_elabTryConfig___lambda__3___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_10);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabTryConfig___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Tactic_elabTryConfig___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabTryConfig___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_elabTryConfig___lambda__3(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_elabTryConfig___lambda__4(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTryConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabTryConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_2);
x_7 = l_Lean_FVarId_getDecl(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_LocalDecl_userName(x_9);
x_11 = l_Lean_Name_hasMacroScopes(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_LocalContext_findFromUserName_x3f(x_12, x_10);
lean_dec(x_10);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; lean_object* x_15; 
lean_dec(x_9);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_18 = l_Lean_LocalDecl_fvarId(x_9);
lean_dec(x_9);
x_19 = lean_name_eq(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_box(x_19);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
}
else
{
uint8_t x_21; lean_object* x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_21 = 0;
x_22 = lean_box(x_21);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = l_Lean_LocalDecl_userName(x_23);
x_26 = l_Lean_Name_hasMacroScopes(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_dec(x_2);
x_28 = l_Lean_LocalContext_findFromUserName_x3f(x_27, x_25);
lean_dec(x_25);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
x_33 = l_Lean_LocalDecl_fvarId(x_32);
lean_dec(x_32);
x_34 = l_Lean_LocalDecl_fvarId(x_23);
lean_dec(x_23);
x_35 = lean_name_eq(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_24);
return x_37;
}
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_2);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_24);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
return x_7;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_7, 0);
x_43 = lean_ctor_get(x_7, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_7);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_2, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_1, x_2);
lean_inc(x_4);
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isAccessible(x_10, x_4, x_5, x_6, x_7, x_8);
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
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_2 = x_24;
x_8 = x_22;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_4);
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
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_4);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_8);
return x_32;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__3;
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__5;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_collectFVars(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_9, x_12);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_2);
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
lean_free_object(x_13);
x_23 = 0;
x_24 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_25 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___spec__1(x_17, x_23, x_24, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = 1;
x_31 = lean_box(x_30);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 0);
lean_dec(x_37);
x_38 = 0;
x_39 = lean_box(x_38);
lean_ctor_set(x_25, 0, x_39);
return x_25;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
x_41 = 0;
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_25);
if (x_44 == 0)
{
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_25, 0);
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_25);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_13, 0);
x_49 = lean_ctor_get(x_13, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_13);
x_50 = lean_ctor_get(x_48, 2);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_array_get_size(x_50);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_dec_lt(x_52, x_51);
if (x_53 == 0)
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_2);
x_54 = 1;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_49);
return x_56;
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_59 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___spec__1(x_50, x_57, x_58, x_2, x_3, x_4, x_5, x_49);
lean_dec(x_50);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_63 = x_59;
} else {
 lean_dec_ref(x_59);
 x_63 = lean_box(0);
}
x_64 = 1;
x_65 = lean_box(x_64);
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_63;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_68 = x_59;
} else {
 lean_dec_ref(x_59);
 x_68 = lean_box(0);
}
x_69 = 0;
x_70 = lean_box(x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_59, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_59, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_74 = x_59;
} else {
 lean_dec_ref(x_59);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___spec__1(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_checkTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = l_Lean_Elab_Tactic_saveState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 0;
x_16 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Elab_Tactic_evalTactic(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_Try_evalSuggestExact___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_unsigned_to_nat(6u);
x_10 = l_Lean_Meta_LibrarySearch_solveByElim(x_8, x_1, x_2, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Elab_Tactic_Try_checkTactic(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Tactic_setGoals(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_3);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
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
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exposeNames", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__12;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expose_names", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(";", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__16;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = l_Lean_PrettyPrinter_delab(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_5, 5);
lean_inc(x_11);
lean_dec(x_5);
x_12 = 0;
x_13 = l_Lean_SourceInfo_fromRef(x_11, x_12);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_6, x_10);
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5;
lean_inc(x_13);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__14;
lean_inc(x_13);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__13;
lean_inc(x_13);
x_22 = l_Lean_Syntax_node1(x_13, x_21, x_20);
x_23 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15;
lean_inc(x_13);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__16;
lean_inc(x_13);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__17;
lean_inc(x_13);
x_28 = l_Lean_Syntax_node2(x_13, x_27, x_26, x_9);
x_29 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_13);
x_30 = l_Lean_Syntax_node3(x_13, x_29, x_22, x_24, x_28);
x_31 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_13);
x_32 = l_Lean_Syntax_node1(x_13, x_31, x_30);
x_33 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_13);
x_34 = l_Lean_Syntax_node1(x_13, x_33, x_32);
x_35 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18;
lean_inc(x_13);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4;
x_38 = l_Lean_Syntax_node3(x_13, x_37, x_18, x_34, x_36);
lean_ctor_set(x_14, 0, x_38);
return x_14;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_dec(x_14);
x_40 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5;
lean_inc(x_13);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_13);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__14;
lean_inc(x_13);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_13);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__13;
lean_inc(x_13);
x_45 = l_Lean_Syntax_node1(x_13, x_44, x_43);
x_46 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15;
lean_inc(x_13);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_13);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__16;
lean_inc(x_13);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__17;
lean_inc(x_13);
x_51 = l_Lean_Syntax_node2(x_13, x_50, x_49, x_9);
x_52 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_13);
x_53 = l_Lean_Syntax_node3(x_13, x_52, x_45, x_47, x_51);
x_54 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_13);
x_55 = l_Lean_Syntax_node1(x_13, x_54, x_53);
x_56 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_13);
x_57 = l_Lean_Syntax_node1(x_13, x_56, x_55);
x_58 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18;
lean_inc(x_13);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_13);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4;
x_61 = l_Lean_Syntax_node3(x_13, x_60, x_41, x_57, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_39);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_6);
lean_dec(x_5);
x_63 = !lean_is_exclusive(x_8);
if (x_63 == 0)
{
return x_8;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_8, 0);
x_65 = lean_ctor_get(x_8, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_8);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`exact\?` failed", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(10u);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_16 = l_Lean_Meta_LibrarySearch_librarySearch(x_1, x_2, x_3, x_15, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Expr_mvar___override(x_1);
x_20 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_headBeta(x_21);
lean_inc(x_10);
lean_inc(x_23);
x_24 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible(x_23, x_10, x_11, x_12, x_13, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4), 7, 2);
lean_closure_set(x_29, 0, x_23);
lean_closure_set(x_29, 1, x_28);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_30 = l_Lean_Meta_withExposedNames___rarg(x_29, x_10, x_11, x_12, x_13, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__3(x_4, x_5, x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_32);
return x_33;
}
else
{
uint8_t x_34; 
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
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
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
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_dec(x_24);
x_39 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_40 = l_Lean_PrettyPrinter_delab(x_23, x_39, x_10, x_11, x_12, x_13, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_12, 5);
lean_inc(x_43);
x_44 = 0;
x_45 = l_Lean_SourceInfo_fromRef(x_43, x_44);
lean_dec(x_43);
x_46 = lean_st_ref_get(x_13, x_42);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_46, 1);
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__16;
lean_inc(x_45);
lean_ctor_set_tag(x_46, 2);
lean_ctor_set(x_46, 1, x_50);
lean_ctor_set(x_46, 0, x_45);
x_51 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__17;
x_52 = l_Lean_Syntax_node2(x_45, x_51, x_46, x_41);
x_53 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__3(x_4, x_5, x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_48);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_dec(x_46);
x_55 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__16;
lean_inc(x_45);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__17;
x_58 = l_Lean_Syntax_node2(x_45, x_57, x_56, x_41);
x_59 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__3(x_4, x_5, x_58, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_54);
return x_59;
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
}
else
{
uint8_t x_64; 
lean_dec(x_23);
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
x_64 = !lean_is_exclusive(x_24);
if (x_64 == 0)
{
return x_24;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_24, 0);
x_66 = lean_ctor_get(x_24, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_24);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_68 = lean_ctor_get(x_16, 1);
lean_inc(x_68);
lean_dec(x_16);
x_69 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__5___closed__2;
x_70 = l_Lean_throwError___at_Lean_Elab_Tactic_Try_evalSuggestExact___spec__1(x_69, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_68);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_70;
}
}
else
{
uint8_t x_71; 
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
x_71 = !lean_is_exclusive(x_16);
if (x_71 == 0)
{
return x_16;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_16, 0);
x_73 = lean_ctor_get(x_16, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_16);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no goals", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__2___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Elab_Tactic_saveState___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Tactic_getGoals___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__2;
x_17 = l_Lean_throwError___at_Lean_Elab_Tactic_Try_evalSuggestExact___spec__1(x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__3;
x_22 = l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__4;
lean_inc(x_19);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__5), 14, 5);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_21);
lean_closure_set(x_23, 2, x_22);
lean_closure_set(x_23, 3, x_11);
lean_closure_set(x_23, 4, x_20);
x_24 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_19, x_23, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_Try_evalSuggestExact___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_Try_evalSuggestExact___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tryResult", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic___closed__2;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_array_mk(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
lean_dec(x_1);
x_9 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSuggestion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic(x_2);
x_4 = l_Array_append___rarg(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("try_suggestions", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`mkTrySuggestions` failed", 25, 25);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___rarg(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_8, 5);
x_16 = 0;
x_17 = l_Lean_SourceInfo_fromRef(x_15, x_16);
x_18 = lean_st_ref_get(x_9, x_10);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__1;
lean_inc(x_17);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
x_24 = l_Array_append___rarg(x_23, x_1);
x_25 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_17);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_24);
x_27 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic___closed__2;
x_28 = l_Lean_Syntax_node2(x_17, x_27, x_22, x_26);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__1;
lean_inc(x_17);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
x_33 = l_Array_append___rarg(x_32, x_1);
x_34 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_17);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_33);
x_36 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic___closed__2;
x_37 = l_Lean_Syntax_node2(x_17, x_36, x_31, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_box(0);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_array_get(x_39, x_1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_10);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__4;
x_44 = l_Lean_throwError___at_Lean_Elab_Tactic_Try_evalSuggestExact___spec__1(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("done", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("skip", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__2;
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
if (x_8 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4;
lean_inc(x_6);
x_12 = l_Lean_Syntax_isOfKind(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_4, x_6);
x_2 = x_10;
x_4 = x_13;
goto _start;
}
else
{
lean_dec(x_6);
x_2 = x_10;
goto _start;
}
}
else
{
lean_dec(x_6);
x_2 = x_10;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeqBracketed", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f___closed__2;
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_6);
x_10 = l_Lean_Syntax_isOfKind(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Syntax_getArg(x_6, x_5);
lean_dec(x_6);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_14 = l_Lean_Syntax_TSepArray_getElems___rarg(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_6, x_16);
lean_dec(x_6);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = l_Lean_Syntax_TSepArray_getElems___rarg(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cdot", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cdotTk", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__2;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__4;
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_push(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4;
lean_inc(x_2);
x_4 = l_Lean_Syntax_isOfKind(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__2;
lean_inc(x_2);
x_6 = l_Lean_Syntax_isOfKind(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_array_push(x_1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
x_10 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__4;
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_push(x_1, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = lean_array_push(x_1, x_2);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f(x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_array_push(x_1, x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_dec_lt(x_8, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_2);
x_23 = l_Array_append___rarg(x_1, x_20);
lean_dec(x_20);
return x_23;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq___spec__1(x_20, x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_2);
x_27 = l_Array_append___rarg(x_1, x_20);
lean_dec(x_20);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_20);
x_28 = lean_array_push(x_1, x_2);
return x_28;
}
}
}
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = l_Lean_Syntax_getArg(x_2, x_29);
x_31 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_30);
x_32 = l_Lean_Syntax_isOfKind(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
x_33 = lean_array_push(x_1, x_2);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f(x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_array_push(x_1, x_2);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Array_append___rarg(x_1, x_36);
lean_dec(x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("patternIgnore", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("token", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("· ", 3, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__3;
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("·", 2, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone(x_1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_7, x_10);
lean_dec(x_7);
if (x_11 == 0)
{
if (x_2 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_3, 5);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_12, x_13);
x_15 = lean_st_ref_get(x_4, x_5);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5;
lean_inc(x_14);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15;
x_21 = l_Lean_Syntax_SepArray_ofElems(x_20, x_6);
lean_dec(x_6);
x_22 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
x_23 = l_Array_append___rarg(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_14);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_23);
x_26 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_14);
x_27 = l_Lean_Syntax_node1(x_14, x_26, x_25);
x_28 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_14);
x_29 = l_Lean_Syntax_node1(x_14, x_28, x_27);
x_30 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18;
lean_inc(x_14);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4;
x_33 = l_Lean_Syntax_node3(x_14, x_32, x_19, x_29, x_31);
lean_ctor_set(x_15, 0, x_33);
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_dec(x_15);
x_35 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5;
lean_inc(x_14);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_14);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15;
x_38 = l_Lean_Syntax_SepArray_ofElems(x_37, x_6);
lean_dec(x_6);
x_39 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
x_40 = l_Array_append___rarg(x_39, x_38);
lean_dec(x_38);
x_41 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_14);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_14);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_40);
x_43 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_14);
x_44 = l_Lean_Syntax_node1(x_14, x_43, x_42);
x_45 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_14);
x_46 = l_Lean_Syntax_node1(x_14, x_45, x_44);
x_47 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18;
lean_inc(x_14);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_14);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4;
x_50 = l_Lean_Syntax_node3(x_14, x_49, x_36, x_46, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_34);
return x_51;
}
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_3, 5);
x_53 = 0;
x_54 = l_Lean_SourceInfo_fromRef(x_52, x_53);
x_55 = lean_st_ref_get(x_4, x_5);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
x_58 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__6;
lean_inc(x_54);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__5;
lean_inc(x_54);
x_61 = l_Lean_Syntax_node1(x_54, x_60, x_59);
x_62 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__2;
lean_inc(x_54);
x_63 = l_Lean_Syntax_node1(x_54, x_62, x_61);
x_64 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__4;
lean_inc(x_54);
x_65 = l_Lean_Syntax_node1(x_54, x_64, x_63);
x_66 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15;
x_67 = l_Lean_Syntax_SepArray_ofElems(x_66, x_6);
lean_dec(x_6);
x_68 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
x_69 = l_Array_append___rarg(x_68, x_67);
lean_dec(x_67);
x_70 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_54);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_54);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_69);
x_72 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_54);
x_73 = l_Lean_Syntax_node1(x_54, x_72, x_71);
x_74 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_54);
x_75 = l_Lean_Syntax_node1(x_54, x_74, x_73);
x_76 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__2;
x_77 = l_Lean_Syntax_node2(x_54, x_76, x_65, x_75);
lean_ctor_set(x_55, 0, x_77);
return x_55;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_78 = lean_ctor_get(x_55, 1);
lean_inc(x_78);
lean_dec(x_55);
x_79 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__6;
lean_inc(x_54);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_54);
lean_ctor_set(x_80, 1, x_79);
x_81 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__5;
lean_inc(x_54);
x_82 = l_Lean_Syntax_node1(x_54, x_81, x_80);
x_83 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__2;
lean_inc(x_54);
x_84 = l_Lean_Syntax_node1(x_54, x_83, x_82);
x_85 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__4;
lean_inc(x_54);
x_86 = l_Lean_Syntax_node1(x_54, x_85, x_84);
x_87 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15;
x_88 = l_Lean_Syntax_SepArray_ofElems(x_87, x_6);
lean_dec(x_6);
x_89 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
x_90 = l_Array_append___rarg(x_89, x_88);
lean_dec(x_88);
x_91 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_54);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_54);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_92, 2, x_90);
x_93 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_54);
x_94 = l_Lean_Syntax_node1(x_54, x_93, x_92);
x_95 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_54);
x_96 = l_Lean_Syntax_node1(x_54, x_95, x_94);
x_97 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__2;
x_98 = l_Lean_Syntax_node2(x_54, x_97, x_86, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_78);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_box(0);
x_101 = lean_array_get(x_100, x_6, x_8);
lean_dec(x_6);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_5);
return x_102;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
if (x_2 == 0)
{
lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_103 = lean_ctor_get(x_3, 5);
x_104 = 0;
x_105 = l_Lean_SourceInfo_fromRef(x_103, x_104);
x_106 = lean_st_ref_get(x_4, x_5);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_106, 0);
lean_dec(x_108);
x_109 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3;
lean_inc(x_105);
x_110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4;
x_112 = l_Lean_Syntax_node1(x_105, x_111, x_110);
lean_ctor_set(x_106, 0, x_112);
return x_106;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_106, 1);
lean_inc(x_113);
lean_dec(x_106);
x_114 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3;
lean_inc(x_105);
x_115 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_115, 0, x_105);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4;
x_117 = l_Lean_Syntax_node1(x_105, x_116, x_115);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_113);
return x_118;
}
}
else
{
lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_3, 5);
x_120 = 0;
x_121 = l_Lean_SourceInfo_fromRef(x_119, x_120);
x_122 = lean_st_ref_get(x_4, x_5);
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_122, 0);
lean_dec(x_124);
x_125 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__1;
lean_inc(x_121);
x_126 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_126, 0, x_121);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__2;
x_128 = l_Lean_Syntax_node1(x_121, x_127, x_126);
lean_ctor_set(x_122, 0, x_128);
return x_122;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_129 = lean_ctor_get(x_122, 1);
lean_inc(x_129);
lean_dec(x_122);
x_130 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__1;
lean_inc(x_121);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_121);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__2;
x_133 = l_Lean_Syntax_node1(x_121, x_132, x_131);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_129);
return x_134;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSorry", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__2;
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__2;
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
if (x_8 == 0)
{
lean_object* x_11; 
x_11 = lean_array_push(x_4, x_6);
x_2 = x_10;
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_6);
x_2 = x_10;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l_Lean_Syntax_structEq(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__2(x_2, x_1, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_uget(x_3, x_5);
lean_inc(x_8);
x_9 = l_Array_contains___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__1(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_array_push(x_6, x_8);
x_11 = 1;
x_12 = lean_usize_add(x_5, x_11);
x_5 = x_12;
x_6 = x_10;
goto _start;
}
else
{
size_t x_14; size_t x_15; 
lean_dec(x_8);
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_5 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_box(0);
x_3 = lean_array_size(x_1);
x_4 = 0;
x_5 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_6 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__3(x_1, x_2, x_1, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__1(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__3(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionsCore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic(x_1);
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSorry(x_2);
lean_dec(x_2);
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l_Array_contains___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__1(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = 1;
return x_8;
}
else
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l_Array_contains___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__1(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = 1;
return x_8;
}
else
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_array_uget(x_4, x_6);
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_12 = l_Array_toSubarray___rarg(x_1, x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_17 = lean_array_push(x_7, x_9);
x_18 = 1;
x_19 = lean_usize_add(x_6, x_18);
x_6 = x_19;
x_7 = x_17;
goto _start;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_array_get_size(x_13);
x_22 = lean_nat_dec_le(x_15, x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_15);
x_23 = lean_nat_dec_lt(x_14, x_21);
if (x_23 == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
x_24 = lean_array_push(x_7, x_9);
x_25 = 1;
x_26 = lean_usize_add(x_6, x_25);
x_6 = x_26;
x_7 = x_24;
goto _start;
}
else
{
size_t x_28; size_t x_29; uint8_t x_30; 
x_28 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_29 = lean_usize_of_nat(x_21);
lean_dec(x_21);
lean_inc(x_9);
x_30 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__1(x_9, x_13, x_28, x_29);
lean_dec(x_13);
if (x_30 == 0)
{
lean_object* x_31; size_t x_32; size_t x_33; 
x_31 = lean_array_push(x_7, x_9);
x_32 = 1;
x_33 = lean_usize_add(x_6, x_32);
x_6 = x_33;
x_7 = x_31;
goto _start;
}
else
{
size_t x_35; size_t x_36; 
lean_dec(x_9);
x_35 = 1;
x_36 = lean_usize_add(x_6, x_35);
x_6 = x_36;
goto _start;
}
}
}
else
{
size_t x_38; size_t x_39; uint8_t x_40; 
lean_dec(x_21);
x_38 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_39 = lean_usize_of_nat(x_15);
lean_dec(x_15);
lean_inc(x_9);
x_40 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__2(x_9, x_13, x_38, x_39);
lean_dec(x_13);
if (x_40 == 0)
{
lean_object* x_41; size_t x_42; size_t x_43; 
x_41 = lean_array_push(x_7, x_9);
x_42 = 1;
x_43 = lean_usize_add(x_6, x_42);
x_6 = x_43;
x_7 = x_41;
goto _start;
}
else
{
size_t x_45; size_t x_46; 
lean_dec(x_9);
x_45 = 1;
x_46 = lean_usize_add(x_6, x_45);
x_6 = x_46;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Array_isEmpty___rarg(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_box(0);
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get(x_4, x_1, x_5);
x_7 = lean_array_size(x_6);
x_8 = 0;
x_9 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_10 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__3(x_1, x_3, x_6, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll___spec__3(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_7);
x_8 = l_Array_contains___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_removeDuplicates___spec__1(x_1, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (x_8 == 0)
{
lean_object* x_11; 
x_11 = lean_array_push(x_5, x_7);
x_3 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_10;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_array_get_size(x_6);
x_10 = lean_nat_dec_lt(x_7, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_6);
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_14 = lean_array_uset(x_8, x_3, x_13);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_9, x_9);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_6);
x_17 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_18 = lean_array_uset(x_8, x_3, x_17);
x_3 = x_12;
x_4 = x_18;
goto _start;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_22 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_23 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___spec__1(x_1, x_6, x_20, x_21, x_22);
lean_dec(x_6);
x_24 = lean_array_uset(x_8, x_3, x_23);
x_3 = x_12;
x_4 = x_24;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_array_size(x_1);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___spec__2(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Syntax_getKind(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = 1;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__1(x_1, x_6, x_11, x_12);
lean_dec(x_6);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
else
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
goto _start;
}
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = 1;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__1(x_1, x_6, x_11, x_12);
lean_dec(x_6);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
else
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
goto _start;
}
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_array_uget(x_4, x_6);
x_10 = l_Lean_Syntax_getKind(x_9);
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_13 = l_Array_toSubarray___rarg(x_1, x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; size_t x_19; size_t x_20; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_18 = lean_array_push(x_7, x_10);
x_19 = 1;
x_20 = lean_usize_add(x_6, x_19);
x_6 = x_20;
x_7 = x_18;
goto _start;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_array_get_size(x_14);
x_23 = lean_nat_dec_le(x_16, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_16);
x_24 = lean_nat_dec_lt(x_15, x_22);
if (x_24 == 0)
{
lean_object* x_25; size_t x_26; size_t x_27; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
x_25 = lean_array_push(x_7, x_10);
x_26 = 1;
x_27 = lean_usize_add(x_6, x_26);
x_6 = x_27;
x_7 = x_25;
goto _start;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; 
x_29 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_30 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_31 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__2(x_10, x_14, x_29, x_30);
lean_dec(x_14);
if (x_31 == 0)
{
lean_object* x_32; size_t x_33; size_t x_34; 
x_32 = lean_array_push(x_7, x_10);
x_33 = 1;
x_34 = lean_usize_add(x_6, x_33);
x_6 = x_34;
x_7 = x_32;
goto _start;
}
else
{
size_t x_36; size_t x_37; 
lean_dec(x_10);
x_36 = 1;
x_37 = lean_usize_add(x_6, x_36);
x_6 = x_37;
goto _start;
}
}
}
else
{
size_t x_39; size_t x_40; uint8_t x_41; 
lean_dec(x_22);
x_39 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_40 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_41 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__3(x_10, x_14, x_39, x_40);
lean_dec(x_14);
if (x_41 == 0)
{
lean_object* x_42; size_t x_43; size_t x_44; 
x_42 = lean_array_push(x_7, x_10);
x_43 = 1;
x_44 = lean_usize_add(x_6, x_43);
x_6 = x_44;
x_7 = x_42;
goto _start;
}
else
{
size_t x_46; size_t x_47; 
lean_dec(x_10);
x_46 = 1;
x_47 = lean_usize_add(x_6, x_46);
x_6 = x_47;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Array_isEmpty___rarg(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_box(0);
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get(x_4, x_1, x_5);
x_7 = lean_array_size(x_6);
x_8 = 0;
x_9 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_10 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__4(x_1, x_3, x_6, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__3(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll___spec__4(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
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
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_name_eq(x_6, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_getGoals___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_15 = l_Lean_Elab_Tactic_evalTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_Tactic_getGoals___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_List_beq___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic___spec__1(x_13, x_19);
lean_dec(x_19);
lean_dec(x_13);
if (x_21 == 0)
{
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_free_object(x_17);
lean_dec(x_1);
x_22 = lean_ctor_get(x_8, 5);
lean_inc(x_22);
lean_dec(x_8);
x_23 = 0;
x_24 = l_Lean_SourceInfo_fromRef(x_22, x_23);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_9, x_20);
lean_dec(x_9);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3;
lean_inc(x_24);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_28);
lean_ctor_set(x_11, 0, x_24);
x_29 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4;
x_30 = l_Lean_Syntax_node1(x_24, x_29, x_11);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3;
lean_inc(x_24);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_32);
lean_ctor_set(x_11, 0, x_24);
x_33 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4;
x_34 = l_Lean_Syntax_node1(x_24, x_33, x_11);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_17, 0);
x_37 = lean_ctor_get(x_17, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_17);
x_38 = l_List_beq___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic___spec__1(x_13, x_36);
lean_dec(x_36);
lean_dec(x_13);
if (x_38 == 0)
{
lean_object* x_39; 
lean_free_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_1);
x_40 = lean_ctor_get(x_8, 5);
lean_inc(x_40);
lean_dec(x_8);
x_41 = 0;
x_42 = l_Lean_SourceInfo_fromRef(x_40, x_41);
lean_dec(x_40);
x_43 = lean_st_ref_get(x_9, x_37);
lean_dec(x_9);
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
x_46 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3;
lean_inc(x_42);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_46);
lean_ctor_set(x_11, 0, x_42);
x_47 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4;
x_48 = l_Lean_Syntax_node1(x_42, x_47, x_11);
if (lean_is_scalar(x_45)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_45;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_free_object(x_11);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_11, 0);
x_55 = lean_ctor_get(x_11, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_56 = l_Lean_Elab_Tactic_evalTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Lean_Elab_Tactic_getGoals___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_57);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = l_List_beq___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic___spec__1(x_54, x_59);
lean_dec(x_59);
lean_dec(x_54);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_9);
lean_dec(x_8);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
else
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_61);
lean_dec(x_1);
x_64 = lean_ctor_get(x_8, 5);
lean_inc(x_64);
lean_dec(x_8);
x_65 = 0;
x_66 = l_Lean_SourceInfo_fromRef(x_64, x_65);
lean_dec(x_64);
x_67 = lean_st_ref_get(x_9, x_60);
lean_dec(x_9);
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
x_70 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3;
lean_inc(x_66);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4;
x_73 = l_Lean_Syntax_node1(x_66, x_72, x_71);
if (lean_is_scalar(x_69)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_69;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_68);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_75 = lean_ctor_get(x_56, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_56, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_77 = x_56;
} else {
 lean_dec_ref(x_56);
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
}
LEAN_EXPORT lean_object* l_List_beq___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg), 1, 0);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("on_failure", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("only", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_12, 5);
x_16 = 0;
x_17 = l_Lean_SourceInfo_fromRef(x_15, x_16);
x_18 = lean_st_ref_get(x_13, x_14);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_20 = x_18;
} else {
 lean_dec_ref(x_18);
 x_20 = lean_box(0);
}
x_21 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__1;
lean_inc(x_17);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_67; 
x_67 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
x_23 = x_67;
goto block_66;
}
else
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_3, 0);
x_69 = 1;
x_70 = l_Lean_SourceInfo_fromRef(x_68, x_69);
x_71 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__7;
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Array_mkArray1___rarg(x_72);
x_23 = x_73;
goto block_66;
}
block_66:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
x_25 = l_Array_append___rarg(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_17);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_25);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__3;
lean_inc(x_17);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_28);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__2;
lean_inc(x_29);
x_31 = l_Lean_Syntax_node5(x_17, x_30, x_22, x_2, x_27, x_29, x_29);
if (lean_is_scalar(x_20)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_20;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_19);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_5, 0);
lean_inc(x_33);
lean_dec(x_5);
x_34 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__4;
lean_inc(x_17);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Array_mkArray2___rarg(x_35, x_33);
x_37 = l_Array_append___rarg(x_24, x_36);
lean_dec(x_36);
lean_inc(x_17);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_17);
lean_ctor_set(x_38, 1, x_26);
lean_ctor_set(x_38, 2, x_37);
x_39 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__2;
x_40 = l_Lean_Syntax_node5(x_17, x_39, x_22, x_2, x_27, x_29, x_38);
if (lean_is_scalar(x_20)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_20;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_19);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__5;
lean_inc(x_17);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_17);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Array_append___rarg(x_24, x_42);
lean_inc(x_17);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_17);
lean_ctor_set(x_46, 1, x_26);
lean_ctor_set(x_46, 2, x_45);
x_47 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__6;
lean_inc(x_17);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_17);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Array_mkArray3___rarg(x_44, x_46, x_48);
x_50 = l_Array_append___rarg(x_24, x_49);
lean_dec(x_49);
lean_inc(x_17);
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_17);
lean_ctor_set(x_51, 1, x_26);
lean_ctor_set(x_51, 2, x_50);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__3;
lean_inc(x_17);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_17);
lean_ctor_set(x_53, 1, x_26);
lean_ctor_set(x_53, 2, x_52);
x_54 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__2;
x_55 = l_Lean_Syntax_node5(x_17, x_54, x_22, x_2, x_27, x_51, x_53);
if (lean_is_scalar(x_20)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_20;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_19);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_5, 0);
lean_inc(x_57);
lean_dec(x_5);
x_58 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__4;
lean_inc(x_17);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_17);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Array_mkArray2___rarg(x_59, x_57);
x_61 = l_Array_append___rarg(x_24, x_60);
lean_dec(x_60);
lean_inc(x_17);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_17);
lean_ctor_set(x_62, 1, x_26);
lean_ctor_set(x_62, 2, x_61);
x_63 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__2;
x_64 = l_Lean_Syntax_node5(x_17, x_63, x_22, x_2, x_27, x_51, x_62);
if (lean_is_scalar(x_20)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_20;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_19);
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(4u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_isNone(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(2u);
lean_inc(x_16);
x_19 = l_Lean_Syntax_matchesNull(x_16, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_2);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg(x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_16, x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_box(0);
x_25 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1(x_5, x_2, x_3, x_24, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1(x_5, x_2, x_3, x_27, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Syntax_isNone(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_inc(x_15);
x_17 = l_Lean_Syntax_matchesNull(x_15, x_14);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_2);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg(x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_15, x_19);
lean_dec(x_15);
x_21 = l_Lean_Syntax_getArgs(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_box(0);
x_24 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__2(x_1, x_2, x_4, x_23, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__2(x_1, x_2, x_4, x_26, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_27;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindTrace", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__2;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_1);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg(x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = l_Lean_Syntax_isNone(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_inc(x_20);
x_22 = l_Lean_Syntax_matchesNull(x_20, x_14);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_1);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg(x_10);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Syntax_getArg(x_20, x_24);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_box(0);
x_28 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__3(x_1, x_15, x_27, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_26);
lean_dec(x_1);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_20);
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__3(x_1, x_15, x_30, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_unsigned_to_nat(4u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_getOptional_x3f(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_12, 5);
x_19 = 0;
x_20 = l_Lean_SourceInfo_fromRef(x_18, x_19);
x_21 = lean_st_ref_get(x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_75; 
x_75 = lean_box(0);
x_22 = x_75;
goto block_74;
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_17);
if (x_76 == 0)
{
x_22 = x_17;
goto block_74;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_17, 0);
lean_inc(x_77);
lean_dec(x_17);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_22 = x_78;
goto block_74;
}
}
block_74:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__1;
lean_inc(x_20);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
x_28 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
lean_inc(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
if (lean_obj_tag(x_3) == 0)
{
x_30 = x_28;
goto block_67;
}
else
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_3, 0);
x_69 = 1;
x_70 = l_Lean_SourceInfo_fromRef(x_68, x_69);
x_71 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__7;
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Array_mkArray1___rarg(x_72);
x_30 = x_73;
goto block_67;
}
block_67:
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Array_append___rarg(x_28, x_30);
lean_dec(x_30);
lean_inc(x_20);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_31);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__3;
lean_inc(x_20);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_33);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__2;
lean_inc(x_34);
x_36 = l_Lean_Syntax_node6(x_20, x_35, x_26, x_2, x_29, x_32, x_34, x_34);
if (lean_is_scalar(x_24)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_24;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_22, 0);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_array_push(x_28, x_38);
x_40 = l_Array_append___rarg(x_28, x_39);
lean_dec(x_39);
lean_inc(x_20);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_20);
lean_ctor_set(x_41, 1, x_27);
lean_ctor_set(x_41, 2, x_40);
x_42 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__2;
x_43 = l_Lean_Syntax_node6(x_20, x_42, x_26, x_2, x_29, x_32, x_34, x_41);
if (lean_is_scalar(x_24)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_24;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_23);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_5, 0);
x_46 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__5;
lean_inc(x_20);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_20);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Array_append___rarg(x_28, x_45);
lean_inc(x_20);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_20);
lean_ctor_set(x_49, 1, x_27);
lean_ctor_set(x_49, 2, x_48);
x_50 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__6;
lean_inc(x_20);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_20);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Array_mkArray3___rarg(x_47, x_49, x_51);
x_53 = l_Array_append___rarg(x_28, x_52);
lean_dec(x_52);
lean_inc(x_20);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_20);
lean_ctor_set(x_54, 1, x_27);
lean_ctor_set(x_54, 2, x_53);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__3;
lean_inc(x_20);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_20);
lean_ctor_set(x_56, 1, x_27);
lean_ctor_set(x_56, 2, x_55);
x_57 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__2;
x_58 = l_Lean_Syntax_node6(x_20, x_57, x_26, x_2, x_29, x_32, x_54, x_56);
if (lean_is_scalar(x_24)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_24;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_23);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_22, 0);
lean_inc(x_60);
lean_dec(x_22);
x_61 = lean_array_push(x_28, x_60);
x_62 = l_Array_append___rarg(x_28, x_61);
lean_dec(x_61);
lean_inc(x_20);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_20);
lean_ctor_set(x_63, 1, x_27);
lean_ctor_set(x_63, 2, x_62);
x_64 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__2;
x_65 = l_Lean_Syntax_node6(x_20, x_64, x_26, x_2, x_29, x_32, x_54, x_63);
if (lean_is_scalar(x_24)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_24;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_23);
return x_66;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpArgs", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Syntax_isNone(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(1u);
lean_inc(x_15);
x_18 = l_Lean_Syntax_matchesNull(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_2);
x_19 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg(x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Syntax_getArg(x_15, x_20);
lean_dec(x_15);
x_22 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___closed__2;
lean_inc(x_21);
x_23 = l_Lean_Syntax_isOfKind(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_2);
x_24 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg(x_13);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = l_Lean_Syntax_getArg(x_21, x_17);
lean_dec(x_21);
x_26 = l_Lean_Syntax_getArgs(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_box(0);
x_29 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1(x_1, x_2, x_4, x_28, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_27);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_15);
x_30 = lean_box(0);
x_31 = lean_box(0);
x_32 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1(x_1, x_2, x_4, x_31, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_32;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpTrace", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpTraceArgsRest", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__2;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_matchesNull(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg(x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
lean_dec(x_1);
x_21 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__4;
lean_inc(x_20);
x_22 = l_Lean_Syntax_isOfKind(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg(x_10);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_Syntax_getArg(x_20, x_16);
x_25 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4;
lean_inc(x_24);
x_26 = l_Lean_Syntax_isOfKind(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_20);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg(x_10);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Syntax_getArg(x_20, x_14);
x_29 = l_Lean_Syntax_matchesNull(x_28, x_16);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_24);
lean_dec(x_20);
x_30 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg(x_10);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Syntax_getArg(x_20, x_19);
x_32 = l_Lean_Syntax_isNone(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
lean_inc(x_31);
x_33 = l_Lean_Syntax_matchesNull(x_31, x_14);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_20);
x_34 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg(x_10);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = l_Lean_Syntax_getArg(x_31, x_16);
lean_dec(x_31);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_box(0);
x_38 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2(x_20, x_24, x_37, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_36);
lean_dec(x_20);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
x_39 = lean_box(0);
x_40 = lean_box(0);
x_41 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2(x_20, x_24, x_40, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_20);
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_saveState___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
x_13 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___lambda__1___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___lambda__2___boxed), 11, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__1;
x_2 = l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_withNonTerminal___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_13);
x_14 = lean_apply_10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_17 = 0;
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
x_19 = lean_apply_10(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_withNonTerminal(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_withNonTerminal___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_focus___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_apply_1(x_1, x_2);
x_13 = l_Lean_Elab_Tactic_focus___rarg(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_focus(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_focus___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_observing___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_42; 
x_12 = l_Lean_Elab_Tactic_saveState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = lean_apply_10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_15);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Elab_Tactic_saveState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = 1;
x_50 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 1);
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_45, 1, x_52);
lean_ctor_set(x_45, 0, x_50);
return x_45;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_47);
lean_ctor_set(x_45, 1, x_54);
lean_ctor_set(x_45, 0, x_55);
return x_45;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_45, 0);
x_57 = lean_ctor_get(x_45, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_45);
x_58 = 1;
x_59 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_ctor_set(x_62, 0, x_43);
lean_ctor_set(x_62, 1, x_56);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_42, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_42, 1);
lean_inc(x_65);
lean_dec(x_42);
x_16 = x_64;
x_17 = x_65;
goto block_41;
}
block_41:
{
uint8_t x_18; 
x_18 = l_Lean_Exception_isInterrupt(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Exception_isRuntime(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_15);
x_20 = l_Lean_Elab_Tactic_saveState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = 1;
x_25 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_20, 1, x_27);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_20, 1, x_29);
lean_ctor_set(x_20, 0, x_30);
return x_20;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = 1;
x_34 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
 lean_ctor_set_tag(x_37, 1);
}
lean_ctor_set(x_37, 0, x_16);
lean_ctor_set(x_37, 1, x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_15)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_15;
 lean_ctor_set_tag(x_39, 1);
}
lean_ctor_set(x_39, 0, x_16);
lean_ctor_set(x_39, 1, x_17);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_15)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_15;
 lean_ctor_set_tag(x_40, 1);
}
lean_ctor_set(x_40, 0, x_16);
lean_ctor_set(x_40, 1, x_17);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_observing(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_observing___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l_Lean_Syntax_structEq(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__2(x_2, x_1, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_uget(x_3, x_5);
lean_inc(x_8);
x_9 = l_Array_contains___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__1(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_array_push(x_6, x_8);
x_11 = 1;
x_12 = lean_usize_add(x_5, x_11);
x_5 = x_12;
x_6 = x_10;
goto _start;
}
else
{
size_t x_14; size_t x_15; 
lean_dec(x_8);
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_5 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_array_size(x_2);
x_5 = 0;
x_6 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__3(x_2, x_3, x_2, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__1(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___spec__3(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeSimp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Elab_Tactic_getSimpParams(x_1);
x_5 = l_Lean_Elab_Tactic_getSimpParams(x_2);
x_6 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams(x_4, x_5);
lean_dec(x_5);
x_7 = l_Lean_Elab_Tactic_setSimpParams(x_1, x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeSimp_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
lean_inc(x_1);
x_4 = l_Lean_Elab_Tactic_setSimpParams(x_1, x_3);
lean_inc(x_2);
x_5 = l_Lean_Elab_Tactic_setSimpParams(x_2, x_3);
x_6 = l_Lean_Syntax_structEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeSimp_x3f___lambda__1(x_1, x_2, x_8);
lean_dec(x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeSimp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeSimp_x3f___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeGrind_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Elab_Tactic_getGrindParams(x_1);
x_5 = l_Lean_Elab_Tactic_getGrindParams(x_2);
x_6 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeParams(x_4, x_5);
lean_dec(x_5);
x_7 = l_Lean_Elab_Tactic_setGrindParams(x_1, x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeGrind_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
lean_inc(x_1);
x_4 = l_Lean_Elab_Tactic_setGrindParams(x_1, x_3);
lean_inc(x_2);
x_5 = l_Lean_Elab_Tactic_setGrindParams(x_2, x_3);
x_6 = l_Lean_Syntax_structEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeGrind_x3f___lambda__1(x_1, x_2, x_8);
lean_dec(x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeGrind_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeGrind_x3f___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_merge_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_3 = l_Lean_Syntax_getKind(x_1);
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__2;
x_5 = lean_name_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__2;
x_7 = lean_name_eq(x_3, x_6);
lean_dec(x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeGrind_x3f(x_1, x_2);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeSimp_x3f(x_1, x_2);
return x_10;
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_nat_dec_lt(x_5, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_fget(x_1, x_5);
lean_inc(x_22);
x_25 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_merge_x3f(x_22, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
lean_dec(x_2);
x_26 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__1___closed__1;
lean_ctor_set(x_4, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_17);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
lean_inc(x_2);
lean_ctor_set(x_4, 1, x_28);
lean_ctor_set(x_4, 0, x_2);
x_29 = lean_ctor_get(x_3, 2);
x_30 = lean_nat_add(x_5, x_29);
lean_dec(x_5);
x_5 = x_30;
x_6 = lean_box(0);
x_7 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
lean_dec(x_4);
x_33 = lean_array_fget(x_1, x_5);
lean_inc(x_32);
x_34 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_merge_x3f(x_32, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_5);
lean_dec(x_2);
x_35 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__1___closed__1;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_17);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_32);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
lean_inc(x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_2);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_ctor_get(x_3, 2);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_4 = x_39;
x_5 = x_41;
x_6 = lean_box(0);
x_7 = lean_box(0);
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Syntax_getKind(x_6);
lean_inc(x_1);
x_8 = l_Lean_Syntax_getKind(x_1);
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = 1;
return x_10;
}
else
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
goto _start;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_2);
x_19 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__1(x_1, x_17, x_16, x_18, x_15, lean_box(0), lean_box(0), x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_16);
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
x_25 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__1(x_23, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get(x_13, x_1, x_14);
x_16 = lean_array_get_size(x_1);
x_17 = lean_nat_dec_lt(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__2(x_1, x_15, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_16);
lean_dec(x_16);
lean_inc(x_15);
x_22 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__2(x_15, x_1, x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__2(x_1, x_15, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = l_Array_isEmpty___rarg(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__3(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__1___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
return x_12;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Elab_Tactic_isGrindOnly(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Elab_Tactic_isGrindOnly(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__3(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Elab_Tactic_isSimpOnly(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__4(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Elab_Tactic_isSimpOnly(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Syntax_getKind(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__2;
x_5 = lean_name_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__2;
x_7 = lean_name_eq(x_1, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_9);
x_12 = 0;
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_15 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__1(x_2, x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__2(x_2, x_13, x_14);
return x_17;
}
}
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_array_get_size(x_2);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_18);
x_21 = 0;
return x_21;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_24 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__3(x_2, x_22, x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
else
{
uint8_t x_26; 
x_26 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__4(x_2, x_22, x_23);
return x_26;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get(x_3, x_1, x_4);
x_6 = l_Lean_Syntax_getKind(x_5);
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___lambda__1(x_6, x_1, x_9);
lean_dec(x_6);
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__5(x_6, x_1, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___lambda__1(x_6, x_1, x_14);
lean_dec(x_6);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = 0;
return x_16;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Array_isEmpty___rarg(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___lambda__2(x_1, x_3);
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__2(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__3(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__4(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___spec__5(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_2, x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_array_uget(x_3, x_2);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_3, x_2, x_19);
x_21 = lean_ctor_get(x_12, 5);
x_22 = 0;
x_23 = l_Lean_SourceInfo_fromRef(x_21, x_22);
x_24 = lean_st_ref_get(x_13, x_14);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__6;
lean_inc(x_23);
lean_ctor_set_tag(x_24, 2);
lean_ctor_set(x_24, 1, x_28);
lean_ctor_set(x_24, 0, x_23);
x_29 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__5;
lean_inc(x_23);
x_30 = l_Lean_Syntax_node1(x_23, x_29, x_24);
x_31 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__2;
lean_inc(x_23);
x_32 = l_Lean_Syntax_node1(x_23, x_31, x_30);
x_33 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__4;
lean_inc(x_23);
x_34 = l_Lean_Syntax_node1(x_23, x_33, x_32);
x_35 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_23);
x_36 = l_Lean_Syntax_node1(x_23, x_35, x_18);
x_37 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_23);
x_38 = l_Lean_Syntax_node1(x_23, x_37, x_36);
x_39 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_23);
x_40 = l_Lean_Syntax_node1(x_23, x_39, x_38);
x_41 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__2;
x_42 = l_Lean_Syntax_node2(x_23, x_41, x_34, x_40);
x_43 = 1;
x_44 = lean_usize_add(x_2, x_43);
x_45 = lean_array_uset(x_20, x_2, x_42);
x_2 = x_44;
x_3 = x_45;
x_14 = x_26;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; 
x_47 = lean_ctor_get(x_24, 1);
lean_inc(x_47);
lean_dec(x_24);
x_48 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__6;
lean_inc(x_23);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_23);
lean_ctor_set(x_49, 1, x_48);
x_50 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__5;
lean_inc(x_23);
x_51 = l_Lean_Syntax_node1(x_23, x_50, x_49);
x_52 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__2;
lean_inc(x_23);
x_53 = l_Lean_Syntax_node1(x_23, x_52, x_51);
x_54 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__4;
lean_inc(x_23);
x_55 = l_Lean_Syntax_node1(x_23, x_54, x_53);
x_56 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_23);
x_57 = l_Lean_Syntax_node1(x_23, x_56, x_18);
x_58 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_23);
x_59 = l_Lean_Syntax_node1(x_23, x_58, x_57);
x_60 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_23);
x_61 = l_Lean_Syntax_node1(x_23, x_60, x_59);
x_62 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__2;
x_63 = l_Lean_Syntax_node2(x_23, x_62, x_55, x_61);
x_64 = 1;
x_65 = lean_usize_add(x_2, x_64);
x_66 = lean_array_uset(x_20, x_2, x_63);
x_2 = x_65;
x_3 = x_66;
x_14 = x_47;
goto _start;
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_10, x_9);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_12);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
x_26 = lean_array_uget(x_8, x_10);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_3, x_36);
lean_inc(x_4);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_4);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
x_39 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(x_1, x_2, x_37, x_38, x_5, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2___closed__1;
lean_ctor_set(x_40, 0, x_44);
x_27 = x_40;
x_28 = x_41;
goto block_35;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2___closed__1;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_27 = x_47;
x_28 = x_41;
goto block_35;
}
}
else
{
uint8_t x_48; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
return x_39;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_39);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_53 = l_Lean_Syntax_getKind(x_26);
x_54 = lean_name_eq(x_53, x_52);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_26);
x_55 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2___closed__1;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_12);
x_27 = x_56;
x_28 = x_22;
goto block_35;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_3, x_57);
lean_inc(x_4);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_26);
lean_ctor_set(x_59, 1, x_4);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
x_60 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(x_1, x_2, x_58, x_59, x_5, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2___closed__1;
lean_ctor_set(x_61, 0, x_65);
x_27 = x_61;
x_28 = x_62;
goto block_35;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_dec(x_61);
x_67 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2___closed__1;
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_27 = x_68;
x_28 = x_62;
goto block_35;
}
}
else
{
uint8_t x_69; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_60);
if (x_69 == 0)
{
return x_60;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_60, 0);
x_71 = lean_ctor_get(x_60, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_60);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
block_35:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = 1;
x_33 = lean_usize_add(x_10, x_32);
x_10 = x_33;
x_11 = x_31;
x_12 = x_30;
x_22 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_push(x_2, x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__1___boxed), 12, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic_<;>_", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<;>", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__1;
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_size(x_1);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__1(x_19, x_20, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_12, 5);
lean_inc(x_26);
x_27 = 0;
x_28 = l_Lean_SourceInfo_fromRef(x_26, x_27);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_13, x_23);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_31 = lean_ctor_get(x_29, 1);
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__6;
lean_inc(x_28);
lean_ctor_set_tag(x_29, 2);
lean_ctor_set(x_29, 1, x_33);
lean_ctor_set(x_29, 0, x_28);
x_34 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__5;
lean_inc(x_28);
x_35 = l_Lean_Syntax_node1(x_28, x_34, x_29);
x_36 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__2;
lean_inc(x_28);
x_37 = l_Lean_Syntax_node1(x_28, x_36, x_35);
x_38 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__4;
lean_inc(x_28);
x_39 = l_Lean_Syntax_node1(x_28, x_38, x_37);
x_40 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
x_41 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
lean_inc(x_28);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
x_43 = l_Array_mkArray2___rarg(x_2, x_42);
x_44 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5;
x_45 = l_Lean_Syntax_SepArray_ofElems(x_44, x_24);
lean_dec(x_24);
x_46 = l_Array_append___rarg(x_43, x_45);
lean_dec(x_45);
lean_inc(x_28);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_28);
lean_ctor_set(x_47, 1, x_40);
lean_ctor_set(x_47, 2, x_46);
x_48 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_28);
x_49 = l_Lean_Syntax_node1(x_28, x_48, x_47);
x_50 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_28);
x_51 = l_Lean_Syntax_node1(x_28, x_50, x_49);
x_52 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__2;
x_53 = l_Lean_Syntax_node2(x_28, x_52, x_39, x_51);
x_54 = lean_apply_12(x_15, x_53, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_31);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_55 = lean_ctor_get(x_29, 1);
lean_inc(x_55);
lean_dec(x_29);
x_56 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__6;
lean_inc(x_28);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_28);
lean_ctor_set(x_57, 1, x_56);
x_58 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__5;
lean_inc(x_28);
x_59 = l_Lean_Syntax_node1(x_28, x_58, x_57);
x_60 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__2;
lean_inc(x_28);
x_61 = l_Lean_Syntax_node1(x_28, x_60, x_59);
x_62 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__4;
lean_inc(x_28);
x_63 = l_Lean_Syntax_node1(x_28, x_62, x_61);
x_64 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
x_65 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
lean_inc(x_28);
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_28);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_65);
x_67 = l_Array_mkArray2___rarg(x_2, x_66);
x_68 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5;
x_69 = l_Lean_Syntax_SepArray_ofElems(x_68, x_24);
lean_dec(x_24);
x_70 = l_Array_append___rarg(x_67, x_69);
lean_dec(x_69);
lean_inc(x_28);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_28);
lean_ctor_set(x_71, 1, x_64);
lean_ctor_set(x_71, 2, x_70);
x_72 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_28);
x_73 = l_Lean_Syntax_node1(x_28, x_72, x_71);
x_74 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_28);
x_75 = l_Lean_Syntax_node1(x_28, x_74, x_73);
x_76 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__2;
x_77 = l_Lean_Syntax_node2(x_28, x_76, x_63, x_75);
x_78 = lean_apply_12(x_15, x_77, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_55);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_1);
x_79 = lean_ctor_get(x_16, 1);
lean_inc(x_79);
lean_dec(x_16);
x_80 = lean_ctor_get(x_17, 0);
lean_inc(x_80);
lean_dec(x_17);
x_81 = lean_ctor_get(x_12, 5);
lean_inc(x_81);
x_82 = 0;
x_83 = l_Lean_SourceInfo_fromRef(x_81, x_82);
lean_dec(x_81);
x_84 = lean_st_ref_get(x_13, x_79);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_84, 1);
x_87 = lean_ctor_get(x_84, 0);
lean_dec(x_87);
x_88 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__4;
lean_inc(x_83);
lean_ctor_set_tag(x_84, 2);
lean_ctor_set(x_84, 1, x_88);
lean_ctor_set(x_84, 0, x_83);
x_89 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__3;
x_90 = l_Lean_Syntax_node3(x_83, x_89, x_2, x_84, x_80);
x_91 = lean_apply_12(x_15, x_90, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_86);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_84, 1);
lean_inc(x_92);
lean_dec(x_84);
x_93 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__4;
lean_inc(x_83);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_83);
lean_ctor_set(x_94, 1, x_93);
x_95 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__3;
x_96 = l_Lean_Syntax_node3(x_83, x_95, x_2, x_94, x_80);
x_97 = lean_apply_12(x_15, x_96, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_92);
return x_97;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sorry", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_array_get_size(x_6);
x_20 = lean_nat_dec_lt(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_array_get_size(x_2);
x_22 = lean_nat_dec_lt(x_3, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
x_23 = lean_array_mk(x_4);
x_24 = l_Array_reverse___rarg(x_23);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2(x_24, x_1, x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isOnlyAndNonOnly(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2(x_24, x_1, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_16);
return x_32;
}
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_array_fget(x_2, x_3);
x_34 = l_Array_isEmpty___rarg(x_33);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_box(0);
x_36 = lean_array_size(x_33);
x_37 = 0;
x_38 = lean_box(0);
x_39 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2(x_1, x_2, x_3, x_4, x_5, x_33, x_35, x_33, x_36, x_37, x_38, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_33);
lean_dec(x_3);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_38);
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_39, 0, x_45);
return x_39;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
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
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_38);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_39);
if (x_52 == 0)
{
return x_39;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_39, 0);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_39);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_33);
x_56 = lean_ctor_get(x_14, 5);
lean_inc(x_56);
x_57 = 0;
x_58 = l_Lean_SourceInfo_fromRef(x_56, x_57);
lean_dec(x_56);
x_59 = lean_st_ref_get(x_15, x_16);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_59, 1);
x_62 = lean_ctor_get(x_59, 0);
lean_dec(x_62);
x_63 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___closed__1;
lean_inc(x_58);
lean_ctor_set_tag(x_59, 2);
lean_ctor_set(x_59, 1, x_63);
lean_ctor_set(x_59, 0, x_58);
x_64 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__2;
x_65 = l_Lean_Syntax_node1(x_58, x_64, x_59);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_3, x_66);
lean_dec(x_3);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_4);
x_3 = x_67;
x_4 = x_68;
x_16 = x_61;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_59, 1);
lean_inc(x_70);
lean_dec(x_59);
x_71 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___closed__1;
lean_inc(x_58);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_58);
lean_ctor_set(x_72, 1, x_71);
x_73 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__2;
x_74 = l_Lean_Syntax_node1(x_58, x_73, x_72);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_3, x_75);
lean_dec(x_3);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_4);
x_3 = x_76;
x_4 = x_77;
x_16 = x_70;
goto _start;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_6);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_16);
return x_81;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_16 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_17 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__1(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2___boxed(lean_object** _args) {
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
_start:
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_24 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_25 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23, x_24, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_5);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionsCore(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 2);
x_13 = l_Lean_isTracingEnabledForCore(x_1, x_12, x_11);
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
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_6, x_5);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_array_uget(x_4, x_6);
x_21 = lean_ctor_get(x_15, 5);
x_22 = 0;
x_23 = l_Lean_SourceInfo_fromRef(x_21, x_22);
x_24 = lean_st_ref_get(x_16, x_17);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__4;
lean_inc(x_23);
lean_ctor_set_tag(x_24, 2);
lean_ctor_set(x_24, 1, x_28);
lean_ctor_set(x_24, 0, x_23);
x_29 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__3;
lean_inc(x_1);
x_30 = l_Lean_Syntax_node3(x_23, x_29, x_1, x_24, x_20);
x_31 = lean_array_push(x_7, x_30);
x_32 = 1;
x_33 = lean_usize_add(x_6, x_32);
x_6 = x_33;
x_7 = x_31;
x_17 = x_26;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; 
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_dec(x_24);
x_36 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__4;
lean_inc(x_23);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__3;
lean_inc(x_1);
x_39 = l_Lean_Syntax_node3(x_23, x_38, x_1, x_37, x_20);
x_40 = lean_array_push(x_7, x_39);
x_41 = 1;
x_42 = lean_usize_add(x_6, x_41);
x_6 = x_42;
x_7 = x_40;
x_17 = x_35;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_8, x_7);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_9);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_array_uget(x_6, x_8);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_unsigned_to_nat(0u);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(x_1, x_3, x_24, x_2, x_23, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = 1;
x_30 = lean_usize_add(x_8, x_29);
x_8 = x_30;
x_9 = x_28;
x_19 = x_27;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_7);
x_8 = l_Lean_Syntax_getKind(x_7);
x_9 = l_Array_contains___at_Lean_Server_FileWorker_collectSyntaxBasedSemanticTokens___spec__4(x_1, x_8);
lean_dec(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
if (x_9 == 0)
{
lean_object* x_12; 
x_12 = lean_array_push(x_5, x_7);
x_3 = x_11;
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_11;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__6(size_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; size_t x_13; size_t x_14; 
x_8 = lean_array_uget(x_6, x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_6, x_5, x_9);
x_11 = lean_array_get_size(x_8);
x_12 = lean_nat_dec_lt(x_9, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_5, x_13);
if (x_12 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_8);
lean_inc(x_2);
x_15 = lean_array_uset(x_10, x_5, x_2);
x_5 = x_14;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_11, x_11);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_8);
lean_inc(x_2);
x_18 = lean_array_uset(x_10, x_5, x_2);
x_5 = x_14;
x_6 = x_18;
goto _start;
}
else
{
size_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_usize_of_nat(x_11);
lean_dec(x_11);
lean_inc(x_2);
x_21 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__5(x_3, x_8, x_1, x_20, x_2);
lean_dec(x_8);
x_22 = lean_array_uset(x_10, x_5, x_21);
x_5 = x_14;
x_6 = x_22;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__7(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Array_isEmpty___rarg(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__8(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Array_isEmpty___rarg(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__9(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_MessageData_ofName(x_5);
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
x_11 = l_Lean_MessageData_ofName(x_9);
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
static double _init_l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_10, 5);
x_14 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_take(x_11, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_18, 3);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; double x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10___closed__1;
x_28 = 0;
x_29 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5;
x_30 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_float(x_30, sizeof(void*)*2, x_27);
lean_ctor_set_float(x_30, sizeof(void*)*2 + 8, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 16, x_28);
x_31 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_32 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_15);
lean_ctor_set(x_32, 2, x_31);
lean_inc(x_13);
lean_ctor_set(x_17, 1, x_32);
lean_ctor_set(x_17, 0, x_13);
x_33 = l_Lean_PersistentArray_push___rarg(x_26, x_17);
lean_ctor_set(x_19, 0, x_33);
x_34 = lean_st_ref_set(x_11, x_18, x_21);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint64_t x_41; lean_object* x_42; double x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_42 = lean_ctor_get(x_19, 0);
lean_inc(x_42);
lean_dec(x_19);
x_43 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10___closed__1;
x_44 = 0;
x_45 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5;
x_46 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_float(x_46, sizeof(void*)*2, x_43);
lean_ctor_set_float(x_46, sizeof(void*)*2 + 8, x_43);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 16, x_44);
x_47 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_48 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_15);
lean_ctor_set(x_48, 2, x_47);
lean_inc(x_13);
lean_ctor_set(x_17, 1, x_48);
lean_ctor_set(x_17, 0, x_13);
x_49 = l_Lean_PersistentArray_push___rarg(x_42, x_17);
x_50 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_uint64(x_50, sizeof(void*)*1, x_41);
lean_ctor_set(x_18, 3, x_50);
x_51 = lean_st_ref_set(x_11, x_18, x_21);
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
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; lean_object* x_65; double x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_56 = lean_ctor_get(x_18, 0);
x_57 = lean_ctor_get(x_18, 1);
x_58 = lean_ctor_get(x_18, 2);
x_59 = lean_ctor_get(x_18, 4);
x_60 = lean_ctor_get(x_18, 5);
x_61 = lean_ctor_get(x_18, 6);
x_62 = lean_ctor_get(x_18, 7);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_18);
x_63 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_64 = lean_ctor_get(x_19, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_65 = x_19;
} else {
 lean_dec_ref(x_19);
 x_65 = lean_box(0);
}
x_66 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10___closed__1;
x_67 = 0;
x_68 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5;
x_69 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set_float(x_69, sizeof(void*)*2, x_66);
lean_ctor_set_float(x_69, sizeof(void*)*2 + 8, x_66);
lean_ctor_set_uint8(x_69, sizeof(void*)*2 + 16, x_67);
x_70 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_71 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_15);
lean_ctor_set(x_71, 2, x_70);
lean_inc(x_13);
lean_ctor_set(x_17, 1, x_71);
lean_ctor_set(x_17, 0, x_13);
x_72 = l_Lean_PersistentArray_push___rarg(x_64, x_17);
if (lean_is_scalar(x_65)) {
 x_73 = lean_alloc_ctor(0, 1, 8);
} else {
 x_73 = x_65;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set_uint64(x_73, sizeof(void*)*1, x_63);
x_74 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_74, 0, x_56);
lean_ctor_set(x_74, 1, x_57);
lean_ctor_set(x_74, 2, x_58);
lean_ctor_set(x_74, 3, x_73);
lean_ctor_set(x_74, 4, x_59);
lean_ctor_set(x_74, 5, x_60);
lean_ctor_set(x_74, 6, x_61);
lean_ctor_set(x_74, 7, x_62);
x_75 = lean_st_ref_set(x_11, x_74, x_21);
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
x_78 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint64_t x_89; lean_object* x_90; lean_object* x_91; double x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_80 = lean_ctor_get(x_17, 1);
lean_inc(x_80);
lean_dec(x_17);
x_81 = lean_ctor_get(x_18, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_18, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_18, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_18, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_18, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_18, 6);
lean_inc(x_86);
x_87 = lean_ctor_get(x_18, 7);
lean_inc(x_87);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 lean_ctor_release(x_18, 6);
 lean_ctor_release(x_18, 7);
 x_88 = x_18;
} else {
 lean_dec_ref(x_18);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_90 = lean_ctor_get(x_19, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_91 = x_19;
} else {
 lean_dec_ref(x_19);
 x_91 = lean_box(0);
}
x_92 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10___closed__1;
x_93 = 0;
x_94 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5;
x_95 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set_float(x_95, sizeof(void*)*2, x_92);
lean_ctor_set_float(x_95, sizeof(void*)*2 + 8, x_92);
lean_ctor_set_uint8(x_95, sizeof(void*)*2 + 16, x_93);
x_96 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_97 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_15);
lean_ctor_set(x_97, 2, x_96);
lean_inc(x_13);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_13);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_PersistentArray_push___rarg(x_90, x_98);
if (lean_is_scalar(x_91)) {
 x_100 = lean_alloc_ctor(0, 1, 8);
} else {
 x_100 = x_91;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set_uint64(x_100, sizeof(void*)*1, x_89);
if (lean_is_scalar(x_88)) {
 x_101 = lean_alloc_ctor(0, 8, 0);
} else {
 x_101 = x_88;
}
lean_ctor_set(x_101, 0, x_81);
lean_ctor_set(x_101, 1, x_82);
lean_ctor_set(x_101, 2, x_83);
lean_ctor_set(x_101, 3, x_100);
lean_ctor_set(x_101, 4, x_84);
lean_ctor_set(x_101, 5, x_85);
lean_ctor_set(x_101, 6, x_86);
lean_ctor_set(x_101, 7, x_87);
x_102 = lean_st_ref_set(x_11, x_101, x_80);
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
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_10, 5);
x_14 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_take(x_11, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_18, 3);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; double x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10___closed__1;
x_28 = 0;
x_29 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5;
x_30 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_float(x_30, sizeof(void*)*2, x_27);
lean_ctor_set_float(x_30, sizeof(void*)*2 + 8, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 16, x_28);
x_31 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_32 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_15);
lean_ctor_set(x_32, 2, x_31);
lean_inc(x_13);
lean_ctor_set(x_17, 1, x_32);
lean_ctor_set(x_17, 0, x_13);
x_33 = l_Lean_PersistentArray_push___rarg(x_26, x_17);
lean_ctor_set(x_19, 0, x_33);
x_34 = lean_st_ref_set(x_11, x_18, x_21);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint64_t x_41; lean_object* x_42; double x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_42 = lean_ctor_get(x_19, 0);
lean_inc(x_42);
lean_dec(x_19);
x_43 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10___closed__1;
x_44 = 0;
x_45 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5;
x_46 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_float(x_46, sizeof(void*)*2, x_43);
lean_ctor_set_float(x_46, sizeof(void*)*2 + 8, x_43);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 16, x_44);
x_47 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_48 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_15);
lean_ctor_set(x_48, 2, x_47);
lean_inc(x_13);
lean_ctor_set(x_17, 1, x_48);
lean_ctor_set(x_17, 0, x_13);
x_49 = l_Lean_PersistentArray_push___rarg(x_42, x_17);
x_50 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set_uint64(x_50, sizeof(void*)*1, x_41);
lean_ctor_set(x_18, 3, x_50);
x_51 = lean_st_ref_set(x_11, x_18, x_21);
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
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; lean_object* x_65; double x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_56 = lean_ctor_get(x_18, 0);
x_57 = lean_ctor_get(x_18, 1);
x_58 = lean_ctor_get(x_18, 2);
x_59 = lean_ctor_get(x_18, 4);
x_60 = lean_ctor_get(x_18, 5);
x_61 = lean_ctor_get(x_18, 6);
x_62 = lean_ctor_get(x_18, 7);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_18);
x_63 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_64 = lean_ctor_get(x_19, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_65 = x_19;
} else {
 lean_dec_ref(x_19);
 x_65 = lean_box(0);
}
x_66 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10___closed__1;
x_67 = 0;
x_68 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5;
x_69 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set_float(x_69, sizeof(void*)*2, x_66);
lean_ctor_set_float(x_69, sizeof(void*)*2 + 8, x_66);
lean_ctor_set_uint8(x_69, sizeof(void*)*2 + 16, x_67);
x_70 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_71 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_15);
lean_ctor_set(x_71, 2, x_70);
lean_inc(x_13);
lean_ctor_set(x_17, 1, x_71);
lean_ctor_set(x_17, 0, x_13);
x_72 = l_Lean_PersistentArray_push___rarg(x_64, x_17);
if (lean_is_scalar(x_65)) {
 x_73 = lean_alloc_ctor(0, 1, 8);
} else {
 x_73 = x_65;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set_uint64(x_73, sizeof(void*)*1, x_63);
x_74 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_74, 0, x_56);
lean_ctor_set(x_74, 1, x_57);
lean_ctor_set(x_74, 2, x_58);
lean_ctor_set(x_74, 3, x_73);
lean_ctor_set(x_74, 4, x_59);
lean_ctor_set(x_74, 5, x_60);
lean_ctor_set(x_74, 6, x_61);
lean_ctor_set(x_74, 7, x_62);
x_75 = lean_st_ref_set(x_11, x_74, x_21);
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
x_78 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint64_t x_89; lean_object* x_90; lean_object* x_91; double x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_80 = lean_ctor_get(x_17, 1);
lean_inc(x_80);
lean_dec(x_17);
x_81 = lean_ctor_get(x_18, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_18, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_18, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_18, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_18, 5);
lean_inc(x_85);
x_86 = lean_ctor_get(x_18, 6);
lean_inc(x_86);
x_87 = lean_ctor_get(x_18, 7);
lean_inc(x_87);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 lean_ctor_release(x_18, 6);
 lean_ctor_release(x_18, 7);
 x_88 = x_18;
} else {
 lean_dec_ref(x_18);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_90 = lean_ctor_get(x_19, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_91 = x_19;
} else {
 lean_dec_ref(x_19);
 x_91 = lean_box(0);
}
x_92 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10___closed__1;
x_93 = 0;
x_94 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5;
x_95 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set_float(x_95, sizeof(void*)*2, x_92);
lean_ctor_set_float(x_95, sizeof(void*)*2 + 8, x_92);
lean_ctor_set_uint8(x_95, sizeof(void*)*2 + 16, x_93);
x_96 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_97 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_15);
lean_ctor_set(x_97, 2, x_96);
lean_inc(x_13);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_13);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_PersistentArray_push___rarg(x_90, x_98);
if (lean_is_scalar(x_91)) {
 x_100 = lean_alloc_ctor(0, 1, 8);
} else {
 x_100 = x_91;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set_uint64(x_100, sizeof(void*)*1, x_89);
if (lean_is_scalar(x_88)) {
 x_101 = lean_alloc_ctor(0, 8, 0);
} else {
 x_101 = x_88;
}
lean_ctor_set(x_101, 0, x_81);
lean_ctor_set(x_101, 1, x_82);
lean_ctor_set(x_101, 2, x_83);
lean_ctor_set(x_101, 3, x_100);
lean_ctor_set(x_101, 4, x_84);
lean_ctor_set(x_101, 5, x_85);
lean_ctor_set(x_101, 6, x_86);
lean_ctor_set(x_101, 7, x_87);
x_102 = lean_st_ref_set(x_11, x_101, x_80);
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
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_6, x_5);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_7);
x_20 = lean_array_uget(x_4, x_6);
lean_inc(x_1);
x_21 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_6, x_25);
x_27 = lean_box(0);
x_6 = x_26;
x_7 = x_27;
x_17 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_21, 1);
x_31 = lean_ctor_get(x_21, 0);
lean_dec(x_31);
x_32 = l_Lean_MessageData_ofSyntax(x_20);
x_33 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12___closed__2;
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_32);
lean_ctor_set(x_21, 0, x_33);
x_34 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_1);
x_36 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__11(x_1, x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_30);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = 1;
x_39 = lean_usize_add(x_6, x_38);
x_40 = lean_box(0);
x_6 = x_39;
x_7 = x_40;
x_17 = x_37;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_21, 1);
lean_inc(x_42);
lean_dec(x_21);
x_43 = l_Lean_MessageData_ofSyntax(x_20);
x_44 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12___closed__2;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_inc(x_1);
x_48 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__11(x_1, x_47, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_42);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = 1;
x_51 = lean_usize_add(x_6, x_50);
x_52 = lean_box(0);
x_6 = x_51;
x_7 = x_52;
x_17 = x_49;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___lambda__1(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_box(0);
x_17 = lean_array_size(x_1);
x_18 = lean_box(0);
x_19 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12(x_2, x_1, x_16, x_1, x_17, x_3, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("goal #", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" tactics", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_7, x_6);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_array_uget(x_5, x_7);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_8, x_22);
lean_dec(x_8);
lean_inc(x_3);
x_24 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
lean_inc(x_3);
x_29 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___lambda__1(x_21, x_3, x_1, x_23, x_28, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_27);
lean_dec(x_21);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = 1;
x_34 = lean_usize_add(x_7, x_33);
x_7 = x_34;
x_8 = x_32;
x_18 = x_31;
goto _start;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
x_37 = lean_ctor_get(x_24, 1);
x_38 = lean_ctor_get(x_24, 0);
lean_dec(x_38);
lean_inc(x_23);
x_39 = l___private_Init_Data_Repr_0__Nat_reprFast(x_23);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_MessageData_ofFormat(x_40);
x_42 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__2;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_41);
lean_ctor_set(x_24, 0, x_42);
x_43 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__4;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_3);
x_45 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_3, x_44, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_37);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_3);
x_48 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___lambda__1(x_21, x_3, x_1, x_23, x_46, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_47);
lean_dec(x_46);
lean_dec(x_21);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = 1;
x_53 = lean_usize_add(x_7, x_52);
x_7 = x_53;
x_8 = x_51;
x_18 = x_50;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; 
x_55 = lean_ctor_get(x_24, 1);
lean_inc(x_55);
lean_dec(x_24);
lean_inc(x_23);
x_56 = l___private_Init_Data_Repr_0__Nat_reprFast(x_23);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lean_MessageData_ofFormat(x_57);
x_59 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__2;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__4;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_inc(x_3);
x_63 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_3, x_62, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_55);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_3);
x_66 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___lambda__1(x_21, x_3, x_1, x_23, x_64, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_65);
lean_dec(x_64);
lean_dec(x_21);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = 1;
x_71 = lean_usize_add(x_7, x_70);
x_7 = x_71;
x_8 = x_69;
x_18 = x_68;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__1___boxed), 12, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; size_t x_20; lean_object* x_21; 
lean_inc(x_1);
x_19 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll(x_1);
x_20 = lean_array_size(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__4(x_2, x_3, x_1, x_19, x_4, x_19, x_20, x_5, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_41; lean_object* x_42; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_size(x_1);
x_25 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__6(x_5, x_6, x_19, x_24, x_5, x_1);
lean_dec(x_19);
x_26 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2___closed__1;
x_41 = l_Array_isEmpty___rarg(x_22);
if (x_41 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_array_get_size(x_25);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_nat_dec_lt(x_57, x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_56);
x_59 = lean_box(0);
x_27 = x_59;
goto block_40;
}
else
{
size_t x_60; uint8_t x_61; 
x_60 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_61 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__8(x_25, x_5, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_box(0);
x_27 = x_62;
goto block_40;
}
else
{
lean_object* x_63; 
x_63 = lean_box(0);
x_42 = x_63;
goto block_55;
}
}
}
else
{
lean_object* x_64; 
x_64 = lean_box(0);
x_42 = x_64;
goto block_55;
}
block_40:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_27);
x_28 = lean_box(0);
x_29 = lean_unsigned_to_nat(0u);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_30 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go(x_2, x_25, x_29, x_3, x_28, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_23);
lean_dec(x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = lean_apply_12(x_26, x_33, x_34, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_32);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
block_55:
{
lean_dec(x_42);
if (x_41 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_box(0);
x_44 = lean_apply_12(x_26, x_22, x_43, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_23);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_array_get_size(x_25);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_lt(x_46, x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_box(0);
x_49 = lean_apply_12(x_26, x_22, x_48, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_23);
return x_49;
}
else
{
size_t x_50; uint8_t x_51; 
x_50 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_51 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__7(x_25, x_5, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_box(0);
x_53 = lean_apply_12(x_26, x_22, x_52, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_23);
return x_53;
}
else
{
lean_object* x_54; 
x_54 = lean_box(0);
x_27 = x_54;
goto block_40;
}
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_21);
if (x_65 == 0)
{
return x_21;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_21, 0);
x_67 = lean_ctor_get(x_21, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_21);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("try", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("chain", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__1;
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__2;
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("kinds: ", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_box(0);
lean_inc(x_1);
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacsSolvedAll(x_1);
x_17 = lean_box(0);
x_18 = lean_array_size(x_16);
x_19 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
lean_inc(x_2);
x_20 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__3(x_2, x_16, x_17, x_16, x_18, x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs(x_1, x_16);
lean_dec(x_16);
x_25 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__4;
x_26 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_20);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2(x_24, x_2, x_15, x_17, x_3, x_19, x_22, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_29);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_33 = lean_ctor_get(x_26, 1);
x_34 = lean_ctor_get(x_26, 0);
lean_dec(x_34);
lean_inc(x_24);
x_35 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll(x_24);
x_36 = lean_array_to_list(x_35);
x_37 = l_List_mapTR_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__9(x_36, x_15);
x_38 = l_Lean_MessageData_ofList(x_37);
x_39 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__6;
lean_ctor_set_tag(x_26, 7);
lean_ctor_set(x_26, 1, x_38);
lean_ctor_set(x_26, 0, x_39);
x_40 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_40);
lean_ctor_set(x_20, 0, x_26);
x_41 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_25, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2(x_24, x_2, x_15, x_17, x_3, x_19, x_22, x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_43);
lean_dec(x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_45 = lean_ctor_get(x_26, 1);
lean_inc(x_45);
lean_dec(x_26);
lean_inc(x_24);
x_46 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll(x_24);
x_47 = lean_array_to_list(x_46);
x_48 = l_List_mapTR_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__9(x_47, x_15);
x_49 = l_Lean_MessageData_ofList(x_48);
x_50 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__6;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_52);
lean_ctor_set(x_20, 0, x_51);
x_53 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_25, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_45);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2(x_24, x_2, x_15, x_17, x_3, x_19, x_22, x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_55);
lean_dec(x_54);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_57 = lean_ctor_get(x_20, 0);
x_58 = lean_ctor_get(x_20, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_20);
x_59 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_eraseTacs(x_1, x_16);
lean_dec(x_16);
x_60 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__4;
x_61 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_60, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_58);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_box(0);
x_66 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2(x_59, x_2, x_15, x_17, x_3, x_19, x_57, x_65, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_68 = x_61;
} else {
 lean_dec_ref(x_61);
 x_68 = lean_box(0);
}
lean_inc(x_59);
x_69 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getKindsSolvedAll(x_59);
x_70 = lean_array_to_list(x_69);
x_71 = l_List_mapTR_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__9(x_70, x_15);
x_72 = l_Lean_MessageData_ofList(x_71);
x_73 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__6;
if (lean_is_scalar(x_68)) {
 x_74 = lean_alloc_ctor(7, 2, 0);
} else {
 x_74 = x_68;
 lean_ctor_set_tag(x_74, 7);
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_60, x_76, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_67);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2(x_59, x_2, x_15, x_17, x_3, x_19, x_57, x_78, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_79);
lean_dec(x_78);
return x_80;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkChainResult -----", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_16 = lean_box(0);
x_17 = lean_array_size(x_1);
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_19 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13(x_2, x_1, x_3, x_16, x_1, x_17, x_2, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_3);
x_21 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = lean_apply_11(x_4, x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4___closed__2;
x_29 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_3, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_apply_11(x_4, x_30, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_31);
return x_32;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__1;
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkChainResultCore tac1", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_array_size(x_2);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__1(x_13, x_14, x_2);
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__1;
x_17 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3(x_15, x_1, x_14, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_17, 1);
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___boxed__const__1;
lean_inc(x_1);
lean_inc(x_15);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___boxed), 14, 3);
lean_closure_set(x_27, 0, x_15);
lean_closure_set(x_27, 1, x_1);
lean_closure_set(x_27, 2, x_26);
x_28 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_17);
lean_dec(x_1);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_box(0);
x_33 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4(x_15, x_14, x_16, x_27, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
lean_dec(x_15);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_28, 1);
x_36 = lean_ctor_get(x_28, 0);
lean_dec(x_36);
x_37 = l_Lean_MessageData_ofSyntax(x_1);
x_38 = l_Lean_indentD(x_37);
x_39 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__3;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_38);
lean_ctor_set(x_28, 0, x_39);
x_40 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_40);
lean_ctor_set(x_17, 0, x_28);
x_41 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4(x_15, x_14, x_16, x_27, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
lean_dec(x_42);
lean_dec(x_15);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_dec(x_28);
x_46 = l_Lean_MessageData_ofSyntax(x_1);
x_47 = l_Lean_indentD(x_46);
x_48 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__3;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_50);
lean_ctor_set(x_17, 0, x_49);
x_51 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4(x_15, x_14, x_16, x_27, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_53);
lean_dec(x_52);
lean_dec(x_15);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_17, 1);
lean_inc(x_55);
lean_dec(x_17);
x_56 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___boxed__const__1;
lean_inc(x_1);
lean_inc(x_15);
x_57 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___boxed), 14, 3);
lean_closure_set(x_57, 0, x_15);
lean_closure_set(x_57, 1, x_1);
lean_closure_set(x_57, 2, x_56);
x_58 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_55);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_1);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_box(0);
x_63 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4(x_15, x_14, x_16, x_57, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_61);
lean_dec(x_15);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
 x_65 = lean_box(0);
}
x_66 = l_Lean_MessageData_ofSyntax(x_1);
x_67 = l_Lean_indentD(x_66);
x_68 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__3;
if (lean_is_scalar(x_65)) {
 x_69 = lean_alloc_ctor(7, 2, 0);
} else {
 x_69 = x_65;
 lean_ctor_set_tag(x_69, 7);
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_16, x_71, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_64);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4(x_15, x_14, x_16, x_57, x_73, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_74);
lean_dec(x_73);
lean_dec(x_15);
return x_75;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__3___boxed(lean_object** _args) {
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
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_20 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__3(x_1, x_2, x_3, x_4, x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__4___boxed(lean_object** _args) {
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
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_21 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_22 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_20, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__5(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__6(x_7, x_2, x_3, x_8, x_9, x_6);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__7(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__8(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12___boxed(lean_object** _args) {
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
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_20 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12(x_1, x_2, x_3, x_4, x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; lean_object* x_17; 
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___lambda__1(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___boxed(lean_object** _args) {
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
size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_19 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_22 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13(x_19, x_2, x_3, x_4, x_5, x_20, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_22;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2___boxed(lean_object** _args) {
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
size_t x_19; lean_object* x_20; 
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2(x_1, x_2, x_3, x_4, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_8);
lean_dec(x_4);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; lean_object* x_16; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; lean_object* x_17; 
x_16 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_17 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1___rarg), 1, 0);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 4);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_19 = l_Lean_Elab_Tactic_mkGrindOnly(x_2, x_3, x_4, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_mk(x_24);
x_26 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions(x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_25);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
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
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind` succeeded", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_17 = l_Lean_Elab_Tactic_elabGrindConfig(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 4);
x_23 = 0;
lean_ctor_set_uint8(x_18, sizeof(void*)*6, x_22);
lean_ctor_set_uint8(x_18, sizeof(void*)*6 + 6, x_23);
x_24 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind(x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_27 = l_Lean_Elab_Tactic_evalGrindCore(x_25, x_18, x_3, x_4, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__1;
x_31 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_box(0);
x_36 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__1(x_25, x_1, x_6, x_28, x_35, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_34);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2___closed__2;
x_39 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_30, x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__1(x_25, x_1, x_6, x_28, x_40, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_41);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_27);
if (x_43 == 0)
{
return x_27;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_27, 0);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_27);
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
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_24);
if (x_47 == 0)
{
return x_24;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_24, 0);
x_49 = lean_ctor_get(x_24, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_24);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_51 = lean_ctor_get(x_7, 1);
x_52 = lean_ctor_get_uint8(x_51, sizeof(void*)*1 + 4);
x_53 = lean_ctor_get(x_18, 0);
x_54 = lean_ctor_get(x_18, 1);
x_55 = lean_ctor_get(x_18, 2);
x_56 = lean_ctor_get(x_18, 3);
x_57 = lean_ctor_get_uint8(x_18, sizeof(void*)*6 + 1);
x_58 = lean_ctor_get_uint8(x_18, sizeof(void*)*6 + 2);
x_59 = lean_ctor_get_uint8(x_18, sizeof(void*)*6 + 3);
x_60 = lean_ctor_get_uint8(x_18, sizeof(void*)*6 + 4);
x_61 = lean_ctor_get(x_18, 4);
x_62 = lean_ctor_get(x_18, 5);
x_63 = lean_ctor_get_uint8(x_18, sizeof(void*)*6 + 5);
x_64 = lean_ctor_get_uint8(x_18, sizeof(void*)*6 + 7);
x_65 = lean_ctor_get_uint8(x_18, sizeof(void*)*6 + 8);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_18);
x_66 = 0;
x_67 = lean_alloc_ctor(0, 6, 9);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_54);
lean_ctor_set(x_67, 2, x_55);
lean_ctor_set(x_67, 3, x_56);
lean_ctor_set(x_67, 4, x_61);
lean_ctor_set(x_67, 5, x_62);
lean_ctor_set_uint8(x_67, sizeof(void*)*6, x_52);
lean_ctor_set_uint8(x_67, sizeof(void*)*6 + 1, x_57);
lean_ctor_set_uint8(x_67, sizeof(void*)*6 + 2, x_58);
lean_ctor_set_uint8(x_67, sizeof(void*)*6 + 3, x_59);
lean_ctor_set_uint8(x_67, sizeof(void*)*6 + 4, x_60);
lean_ctor_set_uint8(x_67, sizeof(void*)*6 + 5, x_63);
lean_ctor_set_uint8(x_67, sizeof(void*)*6 + 6, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*6 + 7, x_64);
lean_ctor_set_uint8(x_67, sizeof(void*)*6 + 8, x_65);
x_68 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind(x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_71 = l_Lean_Elab_Tactic_evalGrindCore(x_69, x_67, x_3, x_4, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__1;
x_75 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_74, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_box(0);
x_80 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__1(x_69, x_1, x_6, x_72, x_79, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_78);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_dec(x_75);
x_82 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2___closed__2;
x_83 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_74, x_82, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_81);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__1(x_69, x_1, x_6, x_72, x_84, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_85);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_69);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_87 = lean_ctor_get(x_71, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_71, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_89 = x_71;
} else {
 lean_dec_ref(x_71);
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
lean_dec(x_67);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_91 = lean_ctor_get(x_68, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_68, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_93 = x_68;
} else {
 lean_dec_ref(x_68);
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
else
{
uint8_t x_95; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_17);
if (x_95 == 0)
{
return x_17;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_17, 0);
x_97 = lean_ctor_get(x_17, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_17);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(4u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Syntax_isNone(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(2u);
lean_inc(x_17);
x_20 = l_Lean_Syntax_matchesNull(x_17, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1___rarg(x_15);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_17, x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_box(0);
x_26 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2(x_2, x_1, x_3, x_5, x_25, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_17);
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2(x_2, x_1, x_3, x_5, x_28, x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_isNone(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_inc(x_16);
x_18 = l_Lean_Syntax_matchesNull(x_16, x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1___rarg(x_14);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_getArg(x_16, x_20);
lean_dec(x_16);
x_22 = l_Lean_Syntax_getArgs(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_box(0);
x_25 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__3(x_1, x_2, x_4, x_24, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__3(x_1, x_2, x_4, x_27, x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__2;
lean_inc(x_1);
x_13 = l_Lean_Syntax_isOfKind(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1___rarg(x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4;
lean_inc(x_16);
x_18 = l_Lean_Syntax_isOfKind(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1___rarg(x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = l_Lean_Syntax_isNone(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_inc(x_21);
x_23 = l_Lean_Syntax_matchesNull(x_21, x_15);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1___rarg(x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Syntax_getArg(x_21, x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_box(0);
x_29 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__4(x_1, x_16, x_28, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_21);
x_30 = lean_box(0);
x_31 = lean_box(0);
x_32 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__4(x_1, x_16, x_31, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(x_1, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
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
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___spec__1___rarg), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_19 = l_Lean_Elab_Tactic_mkSimpCallStx(x_1, x_18, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_3);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_mk(x_23);
x_25 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions(x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*1 + 4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_18 = l_Lean_Elab_Tactic_mkSimpCallStx(x_1, x_17, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_mk(x_23);
x_25 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions(x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_2 = 1;
x_3 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`simp` succeeded", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_unsigned_to_nat(4u);
x_77 = l_Lean_Syntax_getArg(x_1, x_76);
x_78 = l_Lean_Syntax_getOptional_x3f(x_77);
lean_dec(x_77);
x_79 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_78) == 0)
{
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_box(0);
x_15 = x_82;
x_16 = x_80;
x_17 = x_81;
goto block_75;
}
else
{
uint8_t x_83; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
return x_79;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_79, 0);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_79);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_78);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_79, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_79, 1);
lean_inc(x_89);
lean_dec(x_79);
x_15 = x_78;
x_16 = x_88;
x_17 = x_89;
goto block_75;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_78, 0);
lean_inc(x_90);
lean_dec(x_78);
x_91 = lean_ctor_get(x_79, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_79, 1);
lean_inc(x_92);
lean_dec(x_79);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_90);
x_15 = x_93;
x_16 = x_91;
x_17 = x_92;
goto block_75;
}
}
else
{
uint8_t x_94; 
lean_dec(x_78);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_94 = !lean_is_exclusive(x_79);
if (x_94 == 0)
{
return x_79;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_79, 0);
x_96 = lean_ctor_get(x_79, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_79);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
block_75:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = 0;
x_19 = 0;
x_20 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_16);
x_21 = l_Lean_Elab_Tactic_mkSimpContext(x_16, x_18, x_19, x_18, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_box(0);
x_28 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__2;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = l_Lean_Elab_Tactic_simpLocation(x_24, x_25, x_26, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__1;
x_33 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_31);
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
x_38 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__1(x_16, x_30, x_27, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_30);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__4;
x_41 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_32, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__1(x_16, x_30, x_27, x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_43);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_42);
lean_dec(x_30);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
return x_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_29, 0);
x_47 = lean_ctor_get(x_29, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_29);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_15, 0);
lean_inc(x_49);
lean_dec(x_15);
x_50 = l_Lean_Elab_Tactic_expandLocation(x_49);
lean_dec(x_49);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_51 = l_Lean_Elab_Tactic_simpLocation(x_24, x_25, x_26, x_50, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__1;
x_55 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_53);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_box(0);
x_60 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__2(x_16, x_52, x_59, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_58);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_52);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_dec(x_55);
x_62 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__4;
x_63 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_54, x_62, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_61);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__2(x_16, x_52, x_64, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_65);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_64);
lean_dec(x_52);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_67 = !lean_is_exclusive(x_51);
if (x_67 == 0)
{
return x_51;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_51, 0);
x_69 = lean_ctor_get(x_51, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_51);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_71 = !lean_is_exclusive(x_21);
if (x_71 == 0)
{
return x_21;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_21, 0);
x_73 = lean_ctor_get(x_21, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_21);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_isNone(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(1u);
lean_inc(x_16);
x_19 = l_Lean_Syntax_matchesNull(x_16, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1___rarg(x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_16, x_21);
lean_dec(x_16);
x_23 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___closed__2;
lean_inc(x_22);
x_24 = l_Lean_Syntax_isOfKind(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_25 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1___rarg(x_14);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = l_Lean_Syntax_getArg(x_22, x_18);
lean_dec(x_22);
x_27 = l_Lean_Syntax_getArgs(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_box(0);
x_30 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3(x_1, x_2, x_29, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_28);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_16);
x_31 = lean_box(0);
x_32 = lean_box(0);
x_33 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3(x_1, x_2, x_32, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_33;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___spec__1___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__2;
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___closed__1;
x_18 = l_Lean_MVarId_withContext___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___spec__1___rarg(x_13, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_matchesNull(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___closed__1;
x_24 = l_Lean_MVarId_withContext___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___spec__1___rarg(x_13, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_unsigned_to_nat(2u);
x_26 = l_Lean_Syntax_getArg(x_1, x_25);
x_27 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__4;
lean_inc(x_26);
x_28 = l_Lean_Syntax_isOfKind(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_1);
x_29 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___closed__1;
x_30 = l_Lean_MVarId_withContext___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___spec__1___rarg(x_13, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = l_Lean_Syntax_getArg(x_26, x_21);
x_32 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4;
x_33 = l_Lean_Syntax_isOfKind(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_26);
lean_dec(x_1);
x_34 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___closed__1;
x_35 = l_Lean_MVarId_withContext___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___spec__1___rarg(x_13, x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_35;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Syntax_getArg(x_26, x_19);
x_37 = l_Lean_Syntax_matchesNull(x_36, x_21);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_26);
lean_dec(x_1);
x_38 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___closed__1;
x_39 = l_Lean_MVarId_withContext___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___spec__1___rarg(x_13, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Syntax_getArg(x_26, x_25);
x_41 = l_Lean_Syntax_isNone(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
lean_inc(x_40);
x_42 = l_Lean_Syntax_matchesNull(x_40, x_19);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_26);
lean_dec(x_1);
x_43 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___closed__1;
x_44 = l_Lean_MVarId_withContext___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___spec__1___rarg(x_13, x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = l_Lean_Syntax_getArg(x_40, x_21);
lean_dec(x_40);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__4___boxed), 14, 4);
lean_closure_set(x_48, 0, x_26);
lean_closure_set(x_48, 1, x_1);
lean_closure_set(x_48, 2, x_47);
lean_closure_set(x_48, 3, x_46);
x_49 = l_Lean_MVarId_withContext___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___spec__1___rarg(x_13, x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_40);
x_50 = lean_box(0);
x_51 = lean_box(0);
x_52 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__4___boxed), 14, 4);
lean_closure_set(x_52, 0, x_26);
lean_closure_set(x_52, 1, x_1);
lean_closure_set(x_52, 2, x_51);
lean_closure_set(x_52, 3, x_50);
x_53 = l_Lean_MVarId_withContext___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___spec__1___rarg(x_13, x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_53;
}
}
}
}
}
}
}
else
{
uint8_t x_54; 
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
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
return x_12;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_12, 0);
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_12);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalSuggest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_eval_suggest_tactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed", 6, 6);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_dec(x_7);
lean_inc(x_3);
lean_ctor_set(x_6, 1, x_3);
x_32 = l_Lean_Elab_Tactic_setGoals(x_6, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_1);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalSuggest___boxed), 11, 2);
lean_closure_set(x_34, 0, x_1);
lean_closure_set(x_34, 1, x_9);
x_35 = l_Lean_Elab_Tactic_saveState___rarg(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_38 = l_Lean_Elab_Tactic_withoutRecover___rarg(x_34, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_24 = x_39;
x_25 = x_40;
goto block_31;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
x_44 = l_Lean_Exception_isInterrupt(x_42);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Exception_isRuntime(x_42);
if (x_45 == 0)
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_free_object(x_38);
lean_dec(x_42);
x_46 = 0;
x_47 = l_Lean_Elab_Tactic_SavedState_restore(x_36, x_46, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_43);
x_48 = lean_ctor_get(x_9, 1);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1 + 3);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___closed__2;
x_52 = l_Lean_throwError___at_Lean_Elab_Tactic_Try_evalSuggestExact___spec__1(x_51, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_50);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
lean_dec(x_47);
x_58 = lean_ctor_get(x_16, 5);
lean_inc(x_58);
x_59 = l_Lean_SourceInfo_fromRef(x_58, x_46);
lean_dec(x_58);
x_60 = lean_st_ref_get(x_17, x_57);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_60, 1);
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
x_64 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___closed__1;
lean_inc(x_59);
lean_ctor_set_tag(x_60, 2);
lean_ctor_set(x_60, 1, x_64);
lean_ctor_set(x_60, 0, x_59);
x_65 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__2;
x_66 = l_Lean_Syntax_node1(x_59, x_65, x_60);
x_24 = x_66;
x_25 = x_62;
goto block_31;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___closed__1;
lean_inc(x_59);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_59);
lean_ctor_set(x_69, 1, x_68);
x_70 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__2;
x_71 = l_Lean_Syntax_node1(x_59, x_70, x_69);
x_24 = x_71;
x_25 = x_67;
goto block_31;
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_38;
}
}
else
{
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_38;
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_38, 0);
x_73 = lean_ctor_get(x_38, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_38);
x_74 = l_Lean_Exception_isInterrupt(x_72);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = l_Lean_Exception_isRuntime(x_72);
if (x_75 == 0)
{
uint8_t x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_72);
x_76 = 0;
x_77 = l_Lean_Elab_Tactic_SavedState_restore(x_36, x_76, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_73);
x_78 = lean_ctor_get(x_9, 1);
lean_inc(x_78);
x_79 = lean_ctor_get_uint8(x_78, sizeof(void*)*1 + 3);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___closed__2;
x_82 = l_Lean_throwError___at_Lean_Elab_Tactic_Try_evalSuggestExact___spec__1(x_81, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_80);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
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
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_77, 1);
lean_inc(x_87);
lean_dec(x_77);
x_88 = lean_ctor_get(x_16, 5);
lean_inc(x_88);
x_89 = l_Lean_SourceInfo_fromRef(x_88, x_76);
lean_dec(x_88);
x_90 = lean_st_ref_get(x_17, x_87);
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
x_93 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___closed__1;
lean_inc(x_89);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(2, 2, 0);
} else {
 x_94 = x_92;
 lean_ctor_set_tag(x_94, 2);
}
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_93);
x_95 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__2;
x_96 = l_Lean_Syntax_node1(x_89, x_95, x_94);
x_24 = x_96;
x_25 = x_91;
goto block_31;
}
}
else
{
lean_object* x_97; 
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_72);
lean_ctor_set(x_97, 1, x_73);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_36);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_72);
lean_ctor_set(x_98, 1, x_73);
return x_98;
}
}
}
block_31:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_22, x_26);
lean_dec(x_22);
x_28 = lean_array_push(x_23, x_24);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_6 = x_21;
x_7 = x_29;
x_8 = lean_box(0);
x_18 = x_25;
goto _start;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_99 = lean_ctor_get(x_6, 0);
x_100 = lean_ctor_get(x_6, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_6);
x_101 = lean_ctor_get(x_7, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_7, 1);
lean_inc(x_102);
lean_dec(x_7);
lean_inc(x_3);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_99);
lean_ctor_set(x_111, 1, x_3);
x_112 = l_Lean_Elab_Tactic_setGoals(x_111, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
lean_inc(x_9);
lean_inc(x_1);
x_114 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalSuggest___boxed), 11, 2);
lean_closure_set(x_114, 0, x_1);
lean_closure_set(x_114, 1, x_9);
x_115 = l_Lean_Elab_Tactic_saveState___rarg(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_113);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_118 = l_Lean_Elab_Tactic_withoutRecover___rarg(x_114, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_116);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_103 = x_119;
x_104 = x_120;
goto block_110;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_123 = x_118;
} else {
 lean_dec_ref(x_118);
 x_123 = lean_box(0);
}
x_124 = l_Lean_Exception_isInterrupt(x_121);
if (x_124 == 0)
{
uint8_t x_125; 
x_125 = l_Lean_Exception_isRuntime(x_121);
if (x_125 == 0)
{
uint8_t x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_dec(x_123);
lean_dec(x_121);
x_126 = 0;
x_127 = l_Lean_Elab_Tactic_SavedState_restore(x_116, x_126, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_122);
x_128 = lean_ctor_get(x_9, 1);
lean_inc(x_128);
x_129 = lean_ctor_get_uint8(x_128, sizeof(void*)*1 + 3);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___closed__2;
x_132 = l_Lean_throwError___at_Lean_Elab_Tactic_Try_evalSuggestExact___spec__1(x_131, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_130);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
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
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_137 = lean_ctor_get(x_127, 1);
lean_inc(x_137);
lean_dec(x_127);
x_138 = lean_ctor_get(x_16, 5);
lean_inc(x_138);
x_139 = l_Lean_SourceInfo_fromRef(x_138, x_126);
lean_dec(x_138);
x_140 = lean_st_ref_get(x_17, x_137);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
x_143 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___closed__1;
lean_inc(x_139);
if (lean_is_scalar(x_142)) {
 x_144 = lean_alloc_ctor(2, 2, 0);
} else {
 x_144 = x_142;
 lean_ctor_set_tag(x_144, 2);
}
lean_ctor_set(x_144, 0, x_139);
lean_ctor_set(x_144, 1, x_143);
x_145 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__2;
x_146 = l_Lean_Syntax_node1(x_139, x_145, x_144);
x_103 = x_146;
x_104 = x_141;
goto block_110;
}
}
else
{
lean_object* x_147; 
lean_dec(x_116);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_123)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_123;
}
lean_ctor_set(x_147, 0, x_121);
lean_ctor_set(x_147, 1, x_122);
return x_147;
}
}
else
{
lean_object* x_148; 
lean_dec(x_116);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_123)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_123;
}
lean_ctor_set(x_148, 0, x_121);
lean_ctor_set(x_148, 1, x_122);
return x_148;
}
}
block_110:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_101, x_105);
lean_dec(x_101);
x_107 = lean_array_push(x_102, x_103);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_6 = x_100;
x_7 = x_108;
x_8 = lean_box(0);
x_18 = x_104;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 5);
x_13 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_7, x_8, x_9, x_10, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
lean_inc(x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__3(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`<;>` failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = 0;
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = lean_eval_suggest_tactic(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Tactic_getGoals___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Tactic_setGoals(x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_22);
x_29 = l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1(x_2, x_22, x_24, x_27, x_22, x_22, x_28, lean_box(0), x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_22);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_41 = lean_array_get_size(x_32);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_lt(x_42, x_41);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_19);
x_44 = lean_box(0);
x_33 = x_44;
goto block_40;
}
else
{
size_t x_45; size_t x_46; uint8_t x_47; 
x_45 = 0;
x_46 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_47 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__3(x_32, x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_32);
lean_dec(x_19);
x_48 = lean_box(0);
x_33 = x_48;
goto block_40;
}
else
{
lean_object* x_49; 
x_49 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult(x_19, x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
return x_49;
}
}
block_40:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_33);
x_34 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__3;
x_35 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__2(x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_50; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_29);
if (x_50 == 0)
{
return x_29;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_29, 0);
x_52 = lean_ctor_get(x_29, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_29);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_18);
if (x_54 == 0)
{
return x_18;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_18, 0);
x_56 = lean_ctor_get(x_18, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_18);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid `<;>` occurrence in non-terminal position for `try\?` script", 67, 67);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = l_Lean_MessageData_ofSyntax(x_14);
x_16 = l_Lean_indentD(x_15);
x_17 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__3___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__2(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2(x_1, x_2, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__3), 12, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
x_14 = l_Lean_Elab_Tactic_focus___rarg(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___boxed(lean_object** _args) {
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
lean_object* x_19; 
x_19 = l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__3(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_2, x_1);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_uget(x_3, x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_3, x_2, x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = lean_eval_suggest_tactic(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_2, x_22);
x_24 = lean_array_uset(x_18, x_2, x_20);
x_2 = x_23;
x_3 = x_24;
x_13 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_nat_dec_lt(x_5, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_box(0);
x_22 = lean_array_get(x_21, x_1, x_5);
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
x_25 = 0;
lean_inc(x_24);
lean_inc(x_23);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_25);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_27 = lean_eval_suggest_tactic(x_22, x_26, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq(x_4, x_28);
x_31 = lean_ctor_get(x_3, 2);
x_32 = lean_nat_add(x_5, x_31);
lean_dec(x_5);
x_4 = x_30;
x_5 = x_32;
x_6 = lean_box(0);
x_7 = lean_box(0);
x_17 = x_29;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_17 = lean_array_uget(x_4, x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_4, x_3, x_18);
lean_inc(x_1);
x_20 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSeq(x_1, x_17);
x_21 = 1;
x_22 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq(x_20, x_21, x_12, x_13, x_14);
lean_dec(x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_array_uset(x_19, x_3, x_23);
x_3 = x_26;
x_4 = x_27;
x_14 = x_24;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_12 == 0)
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_array_size(x_1);
x_14 = 0;
lean_inc(x_10);
lean_inc(x_9);
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__1(x_13, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 0;
x_19 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq(x_16, x_18, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_16);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_array_get_size(x_1);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
lean_dec(x_24);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_25);
x_29 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__2(x_1, x_28, x_28, x_29, x_27, lean_box(0), lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = l_Array_back_x21___rarg(x_33, x_1);
lean_dec(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_35 = lean_eval_suggest_tactic(x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic(x_36);
x_39 = lean_array_size(x_38);
x_40 = 0;
x_41 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__3(x_31, x_39, x_40, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
lean_dec(x_2);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_42);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_31);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
uint8_t x_49; 
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
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
return x_30;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_30, 0);
x_51 = lean_ctor_get(x_30, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_30);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__1(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__2___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq___spec__3(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_size(x_1);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore___spec__1(x_12, x_13, x_1);
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 5);
x_13 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_7, x_8, x_9, x_10, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
lean_inc(x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeq), 11, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpeted sequence", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__1;
x_13 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_1);
x_14 = l_Lean_Syntax_isOfKind(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_1);
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__3;
x_16 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_dec(x_1);
x_23 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f___closed__2;
lean_inc(x_22);
x_24 = l_Lean_Syntax_isOfKind(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_22);
x_26 = l_Lean_Syntax_isOfKind(x_22, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_22);
x_27 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__3;
x_28 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___spec__1(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = l_Lean_Syntax_getArg(x_22, x_21);
lean_dec(x_22);
x_34 = l_Lean_Syntax_getArgs(x_33);
lean_dec(x_33);
x_35 = l_Lean_Syntax_TSepArray_getElems___rarg(x_34);
lean_dec(x_34);
x_36 = lean_apply_11(x_12, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = l_Lean_Syntax_getArg(x_22, x_37);
lean_dec(x_22);
x_39 = l_Lean_Syntax_getArgs(x_38);
lean_dec(x_38);
x_40 = l_Lean_Syntax_TSepArray_getElems___rarg(x_39);
lean_dec(x_39);
x_41 = lean_apply_11(x_12, x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_nat_dec_eq(x_2, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_box(0);
x_18 = lean_array_get(x_17, x_1, x_2);
lean_inc(x_3);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq), 11, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_3);
x_20 = l_Lean_Elab_Tactic_saveState___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Elab_Tactic_withoutRecover___rarg(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_21);
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
uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_23);
lean_dec(x_25);
x_29 = 0;
x_30 = l_Lean_Elab_Tactic_SavedState_restore(x_21, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_32;
x_12 = x_31;
goto _start;
}
else
{
lean_dec(x_21);
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
return x_23;
}
}
else
{
lean_dec(x_21);
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
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_34);
x_38 = 0;
x_39 = l_Lean_Elab_Tactic_SavedState_restore(x_21, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_41;
x_12 = x_40;
goto _start;
}
else
{
lean_object* x_43; 
lean_dec(x_21);
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
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_35);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_21);
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
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_35);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_box(0);
x_46 = lean_array_get(x_45, x_1, x_2);
lean_dec(x_2);
x_47 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq(x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst_go(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`first` expects at least one argument", 37, 37);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst_go(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___closed__2;
x_17 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__2(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq), 11, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = l_Lean_Elab_Tactic_saveState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_Elab_Tactic_withoutRecover___rarg(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_14);
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
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_Exception_isInterrupt(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_18);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; uint8_t x_24; 
lean_free_object(x_16);
lean_dec(x_18);
x_22 = 0;
x_23 = l_Lean_Elab_Tactic_SavedState_restore(x_14, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_9, 5);
lean_inc(x_27);
lean_dec(x_9);
x_28 = l_Lean_SourceInfo_fromRef(x_27, x_22);
lean_dec(x_27);
x_29 = lean_st_ref_get(x_10, x_25);
lean_dec(x_10);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3;
lean_inc(x_28);
lean_ctor_set_tag(x_23, 2);
lean_ctor_set(x_23, 1, x_32);
lean_ctor_set(x_23, 0, x_28);
x_33 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4;
x_34 = l_Lean_Syntax_node1(x_28, x_33, x_23);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3;
lean_inc(x_28);
lean_ctor_set_tag(x_23, 2);
lean_ctor_set(x_23, 1, x_36);
lean_ctor_set(x_23, 0, x_28);
x_37 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4;
x_38 = l_Lean_Syntax_node1(x_28, x_37, x_23);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_dec(x_23);
x_41 = lean_ctor_get(x_9, 5);
lean_inc(x_41);
lean_dec(x_9);
x_42 = l_Lean_SourceInfo_fromRef(x_41, x_22);
lean_dec(x_41);
x_43 = lean_st_ref_get(x_10, x_40);
lean_dec(x_10);
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
x_46 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3;
lean_inc(x_42);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4;
x_49 = l_Lean_Syntax_node1(x_42, x_48, x_47);
if (lean_is_scalar(x_45)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_45;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
return x_50;
}
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
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
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
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_16, 0);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_16);
x_53 = l_Lean_Exception_isInterrupt(x_51);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = l_Lean_Exception_isRuntime(x_51);
if (x_54 == 0)
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_51);
x_55 = 0;
x_56 = l_Lean_Elab_Tactic_SavedState_restore(x_14, x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_52);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_59 = lean_ctor_get(x_9, 5);
lean_inc(x_59);
lean_dec(x_9);
x_60 = l_Lean_SourceInfo_fromRef(x_59, x_55);
lean_dec(x_59);
x_61 = lean_st_ref_get(x_10, x_57);
lean_dec(x_10);
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
x_64 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3;
lean_inc(x_60);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(2, 2, 0);
} else {
 x_65 = x_58;
 lean_ctor_set_tag(x_65, 2);
}
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4;
x_67 = l_Lean_Syntax_node1(x_60, x_66, x_65);
if (lean_is_scalar(x_63)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_63;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
return x_68;
}
else
{
lean_object* x_69; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_51);
lean_ctor_set(x_69, 1, x_52);
return x_69;
}
}
else
{
lean_object* x_70; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_52);
return x_70;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 5);
x_13 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_7, x_8, x_9, x_10, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
lean_inc(x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_1, x_18);
x_20 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_appendSuggestion(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_5);
x_22 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go(x_6, x_19, x_21, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go(x_6, x_19, x_4, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go(x_6, x_19, x_26, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_27;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`attempt_all` failed", 20, 20);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`attempt_all` argument succeeded", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_1);
x_16 = lean_nat_dec_lt(x_2, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_17 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__2;
x_18 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___spec__1(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = 0;
x_21 = l_Lean_Elab_Tactic_SavedState_restore(x_19, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_box(0);
x_25 = lean_array_get(x_24, x_1, x_2);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq), 11, 1);
lean_closure_set(x_26, 0, x_25);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l_Lean_Elab_Tactic_Try_observing___rarg(x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 1);
x_33 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__1;
x_34 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_29);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_28);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_box(0);
x_39 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___lambda__1(x_2, x_4, x_31, x_3, x_32, x_1, x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_37);
lean_dec(x_2);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_34, 1);
x_42 = lean_ctor_get(x_34, 0);
lean_dec(x_42);
lean_inc(x_31);
x_43 = l_Lean_MessageData_ofSyntax(x_31);
x_44 = l_Lean_indentD(x_43);
x_45 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__4;
lean_ctor_set_tag(x_34, 7);
lean_ctor_set(x_34, 1, x_44);
lean_ctor_set(x_34, 0, x_45);
x_46 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_46);
lean_ctor_set(x_28, 0, x_34);
x_47 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_33, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_41);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___lambda__1(x_2, x_4, x_31, x_3, x_32, x_1, x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_49);
lean_dec(x_48);
lean_dec(x_2);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_dec(x_34);
lean_inc(x_31);
x_52 = l_Lean_MessageData_ofSyntax(x_31);
x_53 = l_Lean_indentD(x_52);
x_54 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__4;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_56);
lean_ctor_set(x_28, 0, x_55);
x_57 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_33, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_51);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___lambda__1(x_2, x_4, x_31, x_3, x_32, x_1, x_58, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_59);
lean_dec(x_58);
lean_dec(x_2);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_28, 0);
x_62 = lean_ctor_get(x_28, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_28);
x_63 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__1;
x_64 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_63, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_29);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_box(0);
x_69 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___lambda__1(x_2, x_4, x_61, x_3, x_62, x_1, x_68, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_67);
lean_dec(x_2);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
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
lean_inc(x_61);
x_72 = l_Lean_MessageData_ofSyntax(x_61);
x_73 = l_Lean_indentD(x_72);
x_74 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__4;
if (lean_is_scalar(x_71)) {
 x_75 = lean_alloc_ctor(7, 2, 0);
} else {
 x_75 = x_71;
 lean_ctor_set_tag(x_75, 7);
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_63, x_77, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_70);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___lambda__1(x_2, x_4, x_61, x_3, x_62, x_1, x_79, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_80);
lean_dec(x_79);
lean_dec(x_2);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_28);
x_82 = lean_ctor_get(x_27, 1);
lean_inc(x_82);
lean_dec(x_27);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_add(x_2, x_83);
lean_dec(x_2);
x_2 = x_84;
x_14 = x_82;
goto _start;
}
}
else
{
uint8_t x_86; 
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
x_86 = !lean_is_exclusive(x_27);
if (x_86 == 0)
{
return x_27;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_27, 0);
x_88 = lean_ctor_get(x_27, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_27);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___lambda__1___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4;
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go(x_1, x_14, x_13, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid occurrence of `attempt_all` in non-terminal position for `try\?` script", 78, 78);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = l_Lean_MessageData_ofSyntax(x_13);
x_15 = l_Lean_indentD(x_14);
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___closed__2;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__2(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___lambda__1(x_1, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsolved goals", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_List_isEmpty___rarg(x_16);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_free_object(x_14);
lean_dec(x_1);
x_19 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___closed__2;
x_20 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__2(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = l_List_isEmpty___rarg(x_25);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_28 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___closed__2;
x_29 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__2(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
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
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("first", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticTry_", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attemptAll", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("seq1", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___boxed), 11, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact\?", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__10;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__3;
lean_inc(x_1);
x_14 = l_Lean_Syntax_isOfKind(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__2;
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4;
lean_inc(x_1);
x_18 = l_Lean_Syntax_isOfKind(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__4;
lean_inc(x_1);
x_20 = l_Lean_Syntax_isOfKind(x_1, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__6;
lean_inc(x_1);
x_22 = l_Lean_Syntax_isOfKind(x_1, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_inc(x_1);
x_23 = l_Lean_Syntax_getKind(x_1);
x_24 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__8;
x_25 = lean_name_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__9;
x_27 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__2;
x_28 = lean_name_eq(x_23, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__2;
x_30 = lean_name_eq(x_23, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__11;
x_32 = lean_name_eq(x_23, x_31);
lean_dec(x_23);
if (x_32 == 0)
{
lean_object* x_33; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_apply_11(x_26, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
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
lean_dec(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_41 = l_Lean_Elab_Tactic_Try_evalSuggestExact(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_apply_11(x_26, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
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
lean_object* x_49; 
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_49 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_apply_11(x_26, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_51);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
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
lean_object* x_57; 
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_57 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_apply_11(x_26, x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_59);
return x_60;
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
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_57);
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
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_23);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Lean_Syntax_getArg(x_1, x_65);
lean_dec(x_1);
x_67 = l_Lean_Syntax_getSepArgs(x_66);
lean_dec(x_66);
x_68 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore(x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; 
x_69 = lean_unsigned_to_nat(1u);
x_70 = l_Lean_Syntax_getArg(x_1, x_69);
x_71 = l_Lean_Syntax_getArgs(x_70);
lean_dec(x_70);
x_72 = lean_array_size(x_71);
x_73 = 0;
x_74 = l_Array_mapMUnsafe_map___at_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___spec__1(x_72, x_73, x_71);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_inc(x_1);
x_75 = l_Lean_Syntax_getKind(x_1);
x_76 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__8;
x_77 = lean_name_eq(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__9;
x_79 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__2;
x_80 = lean_name_eq(x_75, x_79);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__2;
x_82 = lean_name_eq(x_75, x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__11;
x_84 = lean_name_eq(x_75, x_83);
lean_dec(x_75);
if (x_84 == 0)
{
lean_object* x_85; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_85 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_apply_11(x_78, x_86, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_87);
return x_88;
}
else
{
uint8_t x_89; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_89 = !lean_is_exclusive(x_85);
if (x_89 == 0)
{
return x_85;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_85, 0);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_85);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; 
lean_dec(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_93 = l_Lean_Elab_Tactic_Try_evalSuggestExact(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_apply_11(x_78, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_95);
return x_96;
}
else
{
uint8_t x_97; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_97 = !lean_is_exclusive(x_93);
if (x_97 == 0)
{
return x_93;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_93, 0);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_93);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
else
{
lean_object* x_101; 
lean_dec(x_75);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_101 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_apply_11(x_78, x_102, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_103);
return x_104;
}
else
{
uint8_t x_105; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_105 = !lean_is_exclusive(x_101);
if (x_105 == 0)
{
return x_101;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_101, 0);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_101);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
else
{
lean_object* x_109; 
lean_dec(x_75);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_109 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_apply_11(x_78, x_110, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_111);
return x_112;
}
else
{
uint8_t x_113; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_113 = !lean_is_exclusive(x_109);
if (x_113 == 0)
{
return x_109;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_109, 0);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_109);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_75);
x_117 = lean_unsigned_to_nat(0u);
x_118 = l_Lean_Syntax_getArg(x_1, x_117);
lean_dec(x_1);
x_119 = l_Lean_Syntax_getSepArgs(x_118);
lean_dec(x_118);
x_120 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore(x_119, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_1);
x_121 = lean_ctor_get(x_74, 0);
lean_inc(x_121);
lean_dec(x_74);
x_122 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll(x_121, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_123 = lean_unsigned_to_nat(1u);
x_124 = l_Lean_Syntax_getArg(x_1, x_123);
x_125 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_124);
x_126 = l_Lean_Syntax_isOfKind(x_124, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
lean_dec(x_124);
lean_inc(x_1);
x_127 = l_Lean_Syntax_getKind(x_1);
x_128 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__8;
x_129 = lean_name_eq(x_127, x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__9;
x_131 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__2;
x_132 = lean_name_eq(x_127, x_131);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__2;
x_134 = lean_name_eq(x_127, x_133);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__11;
x_136 = lean_name_eq(x_127, x_135);
lean_dec(x_127);
if (x_136 == 0)
{
lean_object* x_137; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_137 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_apply_11(x_130, x_138, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_139);
return x_140;
}
else
{
uint8_t x_141; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_141 = !lean_is_exclusive(x_137);
if (x_141 == 0)
{
return x_137;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_137, 0);
x_143 = lean_ctor_get(x_137, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_137);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
lean_object* x_145; 
lean_dec(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_145 = l_Lean_Elab_Tactic_Try_evalSuggestExact(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_apply_11(x_130, x_146, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_147);
return x_148;
}
else
{
uint8_t x_149; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_149 = !lean_is_exclusive(x_145);
if (x_149 == 0)
{
return x_145;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_145, 0);
x_151 = lean_ctor_get(x_145, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_145);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
else
{
lean_object* x_153; 
lean_dec(x_127);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_153 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_apply_11(x_130, x_154, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_155);
return x_156;
}
else
{
uint8_t x_157; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_157 = !lean_is_exclusive(x_153);
if (x_157 == 0)
{
return x_153;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_153, 0);
x_159 = lean_ctor_get(x_153, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_153);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
else
{
lean_object* x_161; 
lean_dec(x_127);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_161 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_apply_11(x_130, x_162, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_163);
return x_164;
}
else
{
uint8_t x_165; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_165 = !lean_is_exclusive(x_161);
if (x_165 == 0)
{
return x_161;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_161, 0);
x_167 = lean_ctor_get(x_161, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_161);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_127);
x_169 = lean_unsigned_to_nat(0u);
x_170 = l_Lean_Syntax_getArg(x_1, x_169);
lean_dec(x_1);
x_171 = l_Lean_Syntax_getSepArgs(x_170);
lean_dec(x_170);
x_172 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore(x_171, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_172;
}
}
else
{
lean_object* x_173; 
lean_dec(x_1);
x_173 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTry(x_124, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_174 = lean_unsigned_to_nat(1u);
x_175 = l_Lean_Syntax_getArg(x_1, x_174);
x_176 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_175);
x_177 = l_Lean_Syntax_isOfKind(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_dec(x_175);
lean_inc(x_1);
x_178 = l_Lean_Syntax_getKind(x_1);
x_179 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__8;
x_180 = lean_name_eq(x_178, x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_181 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__9;
x_182 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__2;
x_183 = lean_name_eq(x_178, x_182);
if (x_183 == 0)
{
lean_object* x_184; uint8_t x_185; 
x_184 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__2;
x_185 = lean_name_eq(x_178, x_184);
if (x_185 == 0)
{
lean_object* x_186; uint8_t x_187; 
x_186 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__11;
x_187 = lean_name_eq(x_178, x_186);
lean_dec(x_178);
if (x_187 == 0)
{
lean_object* x_188; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_188 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_apply_11(x_181, x_189, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_190);
return x_191;
}
else
{
uint8_t x_192; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_192 = !lean_is_exclusive(x_188);
if (x_192 == 0)
{
return x_188;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_188, 0);
x_194 = lean_ctor_get(x_188, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_188);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_196 = l_Lean_Elab_Tactic_Try_evalSuggestExact(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_apply_11(x_181, x_197, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_198);
return x_199;
}
else
{
uint8_t x_200; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_200 = !lean_is_exclusive(x_196);
if (x_200 == 0)
{
return x_196;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_196, 0);
x_202 = lean_ctor_get(x_196, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_196);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
}
else
{
lean_object* x_204; 
lean_dec(x_178);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_204 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_apply_11(x_181, x_205, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_206);
return x_207;
}
else
{
uint8_t x_208; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_208 = !lean_is_exclusive(x_204);
if (x_208 == 0)
{
return x_204;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_204, 0);
x_210 = lean_ctor_get(x_204, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_204);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
}
else
{
lean_object* x_212; 
lean_dec(x_178);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_212 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_apply_11(x_181, x_213, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_214);
return x_215;
}
else
{
uint8_t x_216; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_216 = !lean_is_exclusive(x_212);
if (x_216 == 0)
{
return x_212;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_212, 0);
x_218 = lean_ctor_get(x_212, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_212);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_178);
x_220 = lean_unsigned_to_nat(0u);
x_221 = l_Lean_Syntax_getArg(x_1, x_220);
lean_dec(x_1);
x_222 = l_Lean_Syntax_getSepArgs(x_221);
lean_dec(x_221);
x_223 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore(x_222, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_223;
}
}
else
{
lean_object* x_224; 
lean_dec(x_1);
x_224 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq(x_175, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_224;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; size_t x_228; size_t x_229; lean_object* x_230; 
x_225 = lean_unsigned_to_nat(1u);
x_226 = l_Lean_Syntax_getArg(x_1, x_225);
x_227 = l_Lean_Syntax_getArgs(x_226);
lean_dec(x_226);
x_228 = lean_array_size(x_227);
x_229 = 0;
x_230 = l_Array_mapMUnsafe_map___at_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___spec__1(x_228, x_229, x_227);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; 
lean_inc(x_1);
x_231 = l_Lean_Syntax_getKind(x_1);
x_232 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__8;
x_233 = lean_name_eq(x_231, x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_234 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__9;
x_235 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__2;
x_236 = lean_name_eq(x_231, x_235);
if (x_236 == 0)
{
lean_object* x_237; uint8_t x_238; 
x_237 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__2;
x_238 = lean_name_eq(x_231, x_237);
if (x_238 == 0)
{
lean_object* x_239; uint8_t x_240; 
x_239 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__11;
x_240 = lean_name_eq(x_231, x_239);
lean_dec(x_231);
if (x_240 == 0)
{
lean_object* x_241; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_241 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAtomic(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_apply_11(x_234, x_242, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_243);
return x_244;
}
else
{
uint8_t x_245; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_245 = !lean_is_exclusive(x_241);
if (x_245 == 0)
{
return x_241;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_241, 0);
x_247 = lean_ctor_get(x_241, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_241);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
else
{
lean_object* x_249; 
lean_dec(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_249 = l_Lean_Elab_Tactic_Try_evalSuggestExact(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_apply_11(x_234, x_250, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_251);
return x_252;
}
else
{
uint8_t x_253; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_253 = !lean_is_exclusive(x_249);
if (x_253 == 0)
{
return x_249;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_249, 0);
x_255 = lean_ctor_get(x_249, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_249);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
}
else
{
lean_object* x_257; 
lean_dec(x_231);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_257 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_apply_11(x_234, x_258, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_259);
return x_260;
}
else
{
uint8_t x_261; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_261 = !lean_is_exclusive(x_257);
if (x_261 == 0)
{
return x_257;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_257, 0);
x_263 = lean_ctor_get(x_257, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_257);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
}
else
{
lean_object* x_265; 
lean_dec(x_231);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_265 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = lean_apply_11(x_234, x_266, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_267);
return x_268;
}
else
{
uint8_t x_269; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_269 = !lean_is_exclusive(x_265);
if (x_269 == 0)
{
return x_265;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_265, 0);
x_271 = lean_ctor_get(x_265, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_265);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_231);
x_273 = lean_unsigned_to_nat(0u);
x_274 = l_Lean_Syntax_getArg(x_1, x_273);
lean_dec(x_1);
x_275 = l_Lean_Syntax_getSepArgs(x_274);
lean_dec(x_274);
x_276 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSeqCore(x_275, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; 
lean_dec(x_1);
x_277 = lean_ctor_get(x_230, 0);
lean_inc(x_277);
lean_dec(x_230);
x_278 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst(x_277, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_277);
return x_278;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_unsigned_to_nat(0u);
x_280 = l_Lean_Syntax_getArg(x_1, x_279);
x_281 = lean_unsigned_to_nat(2u);
x_282 = l_Lean_Syntax_getArg(x_1, x_281);
lean_dec(x_1);
x_283 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain(x_280, x_282, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_283;
}
}
}
LEAN_EXPORT lean_object* lean_eval_suggest_tactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__1;
x_13 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__2(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
lean_inc(x_1);
x_22 = l_Lean_MessageData_ofSyntax(x_1);
x_23 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_23);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_12, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3(x_1, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
lean_dec(x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_dec(x_13);
lean_inc(x_1);
x_30 = l_Lean_MessageData_ofSyntax(x_1);
x_31 = l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10(x_12, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3(x_1, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
lean_dec(x_35);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionsCore(x_1);
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions___spec__1(x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions___spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("try\?", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("consider using `grind` manually, or `try\? +missing` for partial proofs containing `sorry`", 89, 89);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__5;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("consider using `grind` manually", 31, 31);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__8;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__9;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__2;
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__6;
x_17 = l_Lean_Meta_throwTacticEx___rarg(x_15, x_13, x_16, x_6, x_7, x_8, x_9, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__2;
x_21 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__10;
x_22 = l_Lean_Meta_throwTacticEx___rarg(x_20, x_18, x_21, x_6, x_7, x_8, x_9, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try these:", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try this: ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_9, 5);
lean_inc(x_15);
x_16 = lean_array_size(x_2);
x_17 = 0;
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___spec__1(x_16, x_17, x_2);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_15);
x_20 = lean_box(0);
x_21 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___closed__1;
x_22 = l_Lean_Meta_Tactic_TryThis_addSuggestions(x_1, x_18, x_19, x_21, x_20, x_20, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_9, 5);
lean_inc(x_23);
x_24 = l_Lean_Meta_Tactic_TryThis_instInhabitedSuggestion;
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_get(x_24, x_2, x_25);
lean_dec(x_2);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_23);
x_28 = lean_box(0);
x_29 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___closed__2;
x_30 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_26, x_27, x_29, x_28, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_27);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalAndSuggest___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestions(x_3);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_toSubarray___rarg(x_13, x_15, x_14);
x_17 = l_Array_ofSubarray___rarg(x_16);
lean_dec(x_16);
x_18 = l_Array_isEmpty___rarg(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions(x_2, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_17);
x_20 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalAndSuggest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = 1;
lean_inc(x_3);
lean_inc(x_2);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_13);
x_15 = l_Lean_Elab_Tactic_saveState___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = lean_eval_suggest_tactic(x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Tactic_Try_evalAndSuggest___lambda__1(x_3, x_1, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
x_25 = l_Lean_Exception_isInterrupt(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Exception_isRuntime(x_23);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_free_object(x_18);
lean_dec(x_23);
x_27 = 0;
x_28 = l_Lean_Elab_Tactic_SavedState_restore(x_16, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
}
else
{
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_18, 0);
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_18);
x_37 = l_Lean_Exception_isInterrupt(x_35);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_Lean_Exception_isRuntime(x_35);
if (x_38 == 0)
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_35);
x_39 = 0;
x_40 = l_Lean_Elab_Tactic_SavedState_restore(x_16, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_36);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_41);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
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
else
{
lean_object* x_47; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set(x_47, 1, x_36);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_35);
lean_ctor_set(x_48, 1, x_36);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalAndSuggest___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Try_evalAndSuggest___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalAndSuggest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_Try_evalAndSuggest(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toIdent___closed__1;
x_9 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__18(x_1, x_7, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_mk_syntax_ident(x_11);
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
x_15 = lean_mk_syntax_ident(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("group", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("|", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_5, x_4, x_8);
x_10 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__3;
lean_inc(x_1);
x_11 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Syntax_node1(x_1, x_2, x_7);
x_13 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_1);
x_14 = l_Lean_Syntax_node1(x_1, x_13, x_12);
x_15 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_1);
x_16 = l_Lean_Syntax_node1(x_1, x_15, x_14);
x_17 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__2;
lean_inc(x_1);
x_18 = l_Lean_Syntax_node2(x_1, x_17, x_11, x_16);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_21 = lean_array_uset(x_9, x_4, x_18);
x_4 = x_20;
x_5 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_2, 5);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = lean_st_ref_get(x_3, x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__1;
lean_inc(x_10);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_array_size(x_1);
x_17 = 0;
x_18 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_10);
x_19 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1(x_10, x_18, x_16, x_17, x_1);
x_20 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
x_21 = l_Array_append___rarg(x_20, x_19);
lean_dec(x_19);
lean_inc(x_10);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
x_23 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__2;
x_24 = l_Lean_Syntax_node2(x_10, x_23, x_15, x_22);
lean_ctor_set(x_11, 0, x_24);
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
x_26 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__1;
lean_inc(x_10);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_array_size(x_1);
x_29 = 0;
x_30 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_10);
x_31 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1(x_10, x_30, x_28, x_29, x_1);
x_32 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
x_33 = l_Array_append___rarg(x_32, x_31);
lean_dec(x_31);
lean_inc(x_10);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_33);
x_35 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__2;
x_36 = l_Lean_Syntax_node2(x_10, x_35, x_27, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_25);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_array_get(x_38, x_1, x_39);
lean_dec(x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__2;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__6;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__3;
x_4 = l_Lean_Syntax_mkSep(x_2, x_3);
x_5 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__5;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__1;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_array_mk(x_8);
x_10 = lean_box(2);
x_11 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
x_12 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_9);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_setArg(x_1, x_13, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindParam", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindLemma", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Attr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindMod", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__5;
x_4 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindEq", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__5;
x_4 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("=", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toIdent(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_6, 5);
lean_inc(x_17);
x_18 = 0;
x_19 = l_Lean_SourceInfo_fromRef(x_17, x_18);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_7, x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__10;
lean_inc(x_19);
lean_ctor_set_tag(x_20, 2);
lean_ctor_set(x_20, 1, x_24);
lean_ctor_set(x_20, 0, x_19);
x_25 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__9;
lean_inc(x_19);
x_26 = l_Lean_Syntax_node1(x_19, x_25, x_20);
x_27 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__7;
lean_inc(x_19);
x_28 = l_Lean_Syntax_node1(x_19, x_27, x_26);
x_29 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_19);
x_30 = l_Lean_Syntax_node1(x_19, x_29, x_28);
x_31 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__4;
lean_inc(x_19);
x_32 = l_Lean_Syntax_node2(x_19, x_31, x_30, x_15);
x_33 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__2;
x_34 = l_Lean_Syntax_node1(x_19, x_33, x_32);
x_35 = 1;
x_36 = lean_usize_add(x_2, x_35);
x_37 = lean_array_uset(x_13, x_2, x_34);
x_2 = x_36;
x_3 = x_37;
x_8 = x_22;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; 
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_dec(x_20);
x_40 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__10;
lean_inc(x_19);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_19);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__9;
lean_inc(x_19);
x_43 = l_Lean_Syntax_node1(x_19, x_42, x_41);
x_44 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__7;
lean_inc(x_19);
x_45 = l_Lean_Syntax_node1(x_19, x_44, x_43);
x_46 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_19);
x_47 = l_Lean_Syntax_node1(x_19, x_46, x_45);
x_48 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__4;
lean_inc(x_19);
x_49 = l_Lean_Syntax_node2(x_19, x_48, x_47, x_15);
x_50 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__2;
x_51 = l_Lean_Syntax_node1(x_19, x_50, x_49);
x_52 = 1;
x_53 = lean_usize_add(x_2, x_52);
x_54 = lean_array_uset(x_13, x_2, x_51);
x_2 = x_53;
x_3 = x_54;
x_8 = x_39;
goto _start;
}
}
else
{
uint8_t x_56; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_14);
if (x_56 == 0)
{
return x_14;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_14, 0);
x_58 = lean_ctor_get(x_14, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_14);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_array_size(x_1);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1(x_7, x_8, x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Array_isEmpty___rarg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_1, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__2___closed__1;
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___spec__1(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams(x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams(x_2, x_15);
lean_dec(x_15);
x_18 = lean_array_push(x_3, x_17);
x_19 = lean_box(0);
x_20 = lean_apply_7(x_10, x_18, x_19, x_5, x_6, x_7, x_8, x_16);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = lean_apply_7(x_10, x_3, x_25, x_5, x_6, x_7, x_8, x_9);
return x_26;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind\?", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 5);
lean_inc(x_7);
x_8 = 0;
x_9 = l_Lean_SourceInfo_fromRef(x_7, x_8);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_5, x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___closed__1;
lean_inc(x_9);
lean_ctor_set_tag(x_10, 2);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_9);
x_15 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
lean_inc(x_9);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
x_18 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4;
lean_inc(x_17);
lean_inc(x_9);
x_19 = l_Lean_Syntax_node1(x_9, x_18, x_17);
x_20 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__2;
lean_inc_n(x_17, 2);
x_21 = l_Lean_Syntax_node5(x_9, x_20, x_10, x_19, x_17, x_17, x_17);
x_22 = lean_box(0);
lean_inc(x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_mk(x_23);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
x_26 = l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___spec__1(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams(x_27, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_21);
x_31 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams(x_21, x_29);
lean_dec(x_29);
x_32 = lean_array_push(x_24, x_31);
x_33 = lean_box(0);
x_34 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__2(x_1, x_21, x_32, x_33, x_2, x_3, x_4, x_5, x_30);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_28, 0);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_28);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_25);
x_39 = lean_box(0);
x_40 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__2(x_1, x_21, x_24, x_39, x_2, x_3, x_4, x_5, x_12);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_dec(x_10);
x_42 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___closed__1;
lean_inc(x_9);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
x_45 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
lean_inc(x_9);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_9);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
x_47 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4;
lean_inc(x_46);
lean_inc(x_9);
x_48 = l_Lean_Syntax_node1(x_9, x_47, x_46);
x_49 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__2;
lean_inc_n(x_46, 2);
x_50 = l_Lean_Syntax_node5(x_9, x_49, x_43, x_48, x_46, x_46, x_46);
x_51 = lean_box(0);
lean_inc(x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_mk(x_52);
x_54 = lean_ctor_get(x_1, 2);
lean_inc(x_54);
x_55 = l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___spec__1(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_57 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams(x_56, x_2, x_3, x_4, x_5, x_41);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_50);
x_60 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams(x_50, x_58);
lean_dec(x_58);
x_61 = lean_array_push(x_53, x_60);
x_62 = lean_box(0);
x_63 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__2(x_1, x_50, x_61, x_62, x_2, x_3, x_4, x_5, x_59);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_57, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_66 = x_57;
} else {
 lean_dec_ref(x_57);
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
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_54);
x_68 = lean_box(0);
x_69 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__2(x_1, x_50, x_53, x_68, x_2, x_3, x_4, x_5, x_41);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___spec__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Try_Collector_OrdSet_isEmpty___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___spec__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp\?", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpStar", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("*", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("configItem", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("posConfigItem", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("+", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("arith", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__10;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 5);
x_5 = 0;
x_6 = l_Lean_SourceInfo_fromRef(x_4, x_5);
x_7 = lean_st_ref_get(x_2, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__1;
lean_inc(x_6);
x_11 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__3;
lean_inc(x_6);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__1;
lean_inc(x_6);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
x_17 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
lean_inc(x_6);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4;
lean_inc(x_18);
lean_inc(x_6);
x_20 = l_Lean_Syntax_node1(x_6, x_19, x_18);
x_21 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__4;
lean_inc_n(x_18, 4);
lean_inc(x_20);
lean_inc(x_6);
x_22 = l_Lean_Syntax_node5(x_6, x_21, x_20, x_18, x_18, x_18, x_18);
x_23 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__2;
lean_inc(x_18);
lean_inc(x_15);
lean_inc(x_6);
x_24 = l_Lean_Syntax_node3(x_6, x_23, x_15, x_18, x_22);
lean_inc(x_6);
x_25 = l_Lean_Syntax_node1(x_6, x_16, x_24);
x_26 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_6);
x_27 = l_Lean_Syntax_node1(x_6, x_26, x_25);
x_28 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_6);
x_29 = l_Lean_Syntax_node1(x_6, x_28, x_27);
x_30 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__2;
lean_inc(x_13);
lean_inc(x_6);
x_31 = l_Lean_Syntax_node2(x_6, x_30, x_13, x_29);
x_32 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__5;
lean_inc(x_6);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_6);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__4;
lean_inc(x_6);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_6);
lean_ctor_set(x_35, 1, x_34);
x_36 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__3;
lean_inc(x_6);
x_37 = l_Lean_Syntax_node1(x_6, x_36, x_35);
lean_inc(x_6);
x_38 = l_Lean_Syntax_node1(x_6, x_16, x_37);
x_39 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__6;
lean_inc(x_6);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_39);
x_41 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___closed__2;
lean_inc(x_6);
x_42 = l_Lean_Syntax_node3(x_6, x_41, x_33, x_38, x_40);
lean_inc(x_6);
x_43 = l_Lean_Syntax_node1(x_6, x_16, x_42);
lean_inc(x_43);
lean_inc_n(x_18, 3);
lean_inc(x_6);
x_44 = l_Lean_Syntax_node5(x_6, x_21, x_20, x_18, x_18, x_43, x_18);
lean_inc(x_18);
lean_inc(x_15);
lean_inc(x_6);
x_45 = l_Lean_Syntax_node3(x_6, x_23, x_15, x_18, x_44);
lean_inc(x_6);
x_46 = l_Lean_Syntax_node1(x_6, x_16, x_45);
lean_inc(x_6);
x_47 = l_Lean_Syntax_node1(x_6, x_26, x_46);
lean_inc(x_6);
x_48 = l_Lean_Syntax_node1(x_6, x_28, x_47);
lean_inc(x_13);
lean_inc(x_6);
x_49 = l_Lean_Syntax_node2(x_6, x_30, x_13, x_48);
x_50 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__9;
lean_inc(x_6);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_6);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_box(0);
x_53 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__11;
x_54 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__12;
lean_inc(x_6);
x_55 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_55, 0, x_6);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set(x_55, 3, x_52);
x_56 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__8;
lean_inc(x_6);
x_57 = l_Lean_Syntax_node2(x_6, x_56, x_51, x_55);
x_58 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__6;
lean_inc(x_6);
x_59 = l_Lean_Syntax_node1(x_6, x_58, x_57);
lean_inc(x_6);
x_60 = l_Lean_Syntax_node1(x_6, x_16, x_59);
lean_inc(x_6);
x_61 = l_Lean_Syntax_node1(x_6, x_19, x_60);
lean_inc_n(x_18, 4);
lean_inc(x_61);
lean_inc(x_6);
x_62 = l_Lean_Syntax_node5(x_6, x_21, x_61, x_18, x_18, x_18, x_18);
lean_inc(x_18);
lean_inc(x_15);
lean_inc(x_6);
x_63 = l_Lean_Syntax_node3(x_6, x_23, x_15, x_18, x_62);
lean_inc(x_6);
x_64 = l_Lean_Syntax_node1(x_6, x_16, x_63);
lean_inc(x_6);
x_65 = l_Lean_Syntax_node1(x_6, x_26, x_64);
lean_inc(x_6);
x_66 = l_Lean_Syntax_node1(x_6, x_28, x_65);
lean_inc(x_13);
lean_inc(x_6);
x_67 = l_Lean_Syntax_node2(x_6, x_30, x_13, x_66);
lean_inc_n(x_18, 3);
lean_inc(x_6);
x_68 = l_Lean_Syntax_node5(x_6, x_21, x_61, x_18, x_18, x_43, x_18);
lean_inc(x_6);
x_69 = l_Lean_Syntax_node3(x_6, x_23, x_15, x_18, x_68);
lean_inc(x_6);
x_70 = l_Lean_Syntax_node1(x_6, x_16, x_69);
lean_inc(x_6);
x_71 = l_Lean_Syntax_node1(x_6, x_26, x_70);
lean_inc(x_6);
x_72 = l_Lean_Syntax_node1(x_6, x_28, x_71);
lean_inc(x_6);
x_73 = l_Lean_Syntax_node2(x_6, x_30, x_13, x_72);
lean_inc(x_6);
x_74 = l_Lean_Syntax_node4(x_6, x_16, x_31, x_49, x_67, x_73);
x_75 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__2;
x_76 = l_Lean_Syntax_node2(x_6, x_75, x_11, x_74);
lean_ctor_set(x_7, 0, x_76);
return x_7;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_77 = lean_ctor_get(x_7, 1);
lean_inc(x_77);
lean_dec(x_7);
x_78 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__1;
lean_inc(x_6);
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_6);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__3;
lean_inc(x_6);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_6);
lean_ctor_set(x_81, 1, x_80);
x_82 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__1;
lean_inc(x_6);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_6);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
x_85 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
lean_inc(x_6);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_6);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 2, x_85);
x_87 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4;
lean_inc(x_86);
lean_inc(x_6);
x_88 = l_Lean_Syntax_node1(x_6, x_87, x_86);
x_89 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__4;
lean_inc_n(x_86, 4);
lean_inc(x_88);
lean_inc(x_6);
x_90 = l_Lean_Syntax_node5(x_6, x_89, x_88, x_86, x_86, x_86, x_86);
x_91 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__2;
lean_inc(x_86);
lean_inc(x_83);
lean_inc(x_6);
x_92 = l_Lean_Syntax_node3(x_6, x_91, x_83, x_86, x_90);
lean_inc(x_6);
x_93 = l_Lean_Syntax_node1(x_6, x_84, x_92);
x_94 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_6);
x_95 = l_Lean_Syntax_node1(x_6, x_94, x_93);
x_96 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_6);
x_97 = l_Lean_Syntax_node1(x_6, x_96, x_95);
x_98 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__2;
lean_inc(x_81);
lean_inc(x_6);
x_99 = l_Lean_Syntax_node2(x_6, x_98, x_81, x_97);
x_100 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__5;
lean_inc(x_6);
x_101 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_101, 0, x_6);
lean_ctor_set(x_101, 1, x_100);
x_102 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__4;
lean_inc(x_6);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_6);
lean_ctor_set(x_103, 1, x_102);
x_104 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__3;
lean_inc(x_6);
x_105 = l_Lean_Syntax_node1(x_6, x_104, x_103);
lean_inc(x_6);
x_106 = l_Lean_Syntax_node1(x_6, x_84, x_105);
x_107 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__6;
lean_inc(x_6);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_6);
lean_ctor_set(x_108, 1, x_107);
x_109 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___closed__2;
lean_inc(x_6);
x_110 = l_Lean_Syntax_node3(x_6, x_109, x_101, x_106, x_108);
lean_inc(x_6);
x_111 = l_Lean_Syntax_node1(x_6, x_84, x_110);
lean_inc(x_111);
lean_inc_n(x_86, 3);
lean_inc(x_6);
x_112 = l_Lean_Syntax_node5(x_6, x_89, x_88, x_86, x_86, x_111, x_86);
lean_inc(x_86);
lean_inc(x_83);
lean_inc(x_6);
x_113 = l_Lean_Syntax_node3(x_6, x_91, x_83, x_86, x_112);
lean_inc(x_6);
x_114 = l_Lean_Syntax_node1(x_6, x_84, x_113);
lean_inc(x_6);
x_115 = l_Lean_Syntax_node1(x_6, x_94, x_114);
lean_inc(x_6);
x_116 = l_Lean_Syntax_node1(x_6, x_96, x_115);
lean_inc(x_81);
lean_inc(x_6);
x_117 = l_Lean_Syntax_node2(x_6, x_98, x_81, x_116);
x_118 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__9;
lean_inc(x_6);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_6);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_box(0);
x_121 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__11;
x_122 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__12;
lean_inc(x_6);
x_123 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_123, 0, x_6);
lean_ctor_set(x_123, 1, x_121);
lean_ctor_set(x_123, 2, x_122);
lean_ctor_set(x_123, 3, x_120);
x_124 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__8;
lean_inc(x_6);
x_125 = l_Lean_Syntax_node2(x_6, x_124, x_119, x_123);
x_126 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__6;
lean_inc(x_6);
x_127 = l_Lean_Syntax_node1(x_6, x_126, x_125);
lean_inc(x_6);
x_128 = l_Lean_Syntax_node1(x_6, x_84, x_127);
lean_inc(x_6);
x_129 = l_Lean_Syntax_node1(x_6, x_87, x_128);
lean_inc_n(x_86, 4);
lean_inc(x_129);
lean_inc(x_6);
x_130 = l_Lean_Syntax_node5(x_6, x_89, x_129, x_86, x_86, x_86, x_86);
lean_inc(x_86);
lean_inc(x_83);
lean_inc(x_6);
x_131 = l_Lean_Syntax_node3(x_6, x_91, x_83, x_86, x_130);
lean_inc(x_6);
x_132 = l_Lean_Syntax_node1(x_6, x_84, x_131);
lean_inc(x_6);
x_133 = l_Lean_Syntax_node1(x_6, x_94, x_132);
lean_inc(x_6);
x_134 = l_Lean_Syntax_node1(x_6, x_96, x_133);
lean_inc(x_81);
lean_inc(x_6);
x_135 = l_Lean_Syntax_node2(x_6, x_98, x_81, x_134);
lean_inc_n(x_86, 3);
lean_inc(x_6);
x_136 = l_Lean_Syntax_node5(x_6, x_89, x_129, x_86, x_86, x_111, x_86);
lean_inc(x_6);
x_137 = l_Lean_Syntax_node3(x_6, x_91, x_83, x_86, x_136);
lean_inc(x_6);
x_138 = l_Lean_Syntax_node1(x_6, x_84, x_137);
lean_inc(x_6);
x_139 = l_Lean_Syntax_node1(x_6, x_94, x_138);
lean_inc(x_6);
x_140 = l_Lean_Syntax_node1(x_6, x_96, x_139);
lean_inc(x_6);
x_141 = l_Lean_Syntax_node2(x_6, x_98, x_81, x_140);
lean_inc(x_6);
x_142 = l_Lean_Syntax_node4(x_6, x_84, x_99, x_117, x_135, x_141);
x_143 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__2;
x_144 = l_Lean_Syntax_node2(x_6, x_143, x_79, x_142);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_77);
return x_145;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attempt_all", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticRfl", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rfl", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assumption", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 5);
x_5 = 0;
x_6 = l_Lean_SourceInfo_fromRef(x_4, x_5);
x_7 = lean_st_ref_get(x_2, x_3);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__1;
lean_inc(x_6);
x_11 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__3;
lean_inc(x_6);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__4;
lean_inc(x_6);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__3;
lean_inc(x_6);
x_17 = l_Lean_Syntax_node1(x_6, x_16, x_15);
x_18 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_6);
x_19 = l_Lean_Syntax_node1(x_6, x_18, x_17);
x_20 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_6);
x_21 = l_Lean_Syntax_node1(x_6, x_20, x_19);
x_22 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_6);
x_23 = l_Lean_Syntax_node1(x_6, x_22, x_21);
x_24 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__2;
lean_inc(x_13);
lean_inc(x_6);
x_25 = l_Lean_Syntax_node2(x_6, x_24, x_13, x_23);
x_26 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__5;
lean_inc(x_6);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_26);
x_28 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__6;
lean_inc(x_6);
x_29 = l_Lean_Syntax_node1(x_6, x_28, x_27);
lean_inc(x_6);
x_30 = l_Lean_Syntax_node1(x_6, x_18, x_29);
lean_inc(x_6);
x_31 = l_Lean_Syntax_node1(x_6, x_20, x_30);
lean_inc(x_6);
x_32 = l_Lean_Syntax_node1(x_6, x_22, x_31);
lean_inc(x_6);
x_33 = l_Lean_Syntax_node2(x_6, x_24, x_13, x_32);
lean_inc(x_6);
x_34 = l_Lean_Syntax_node2(x_6, x_18, x_25, x_33);
x_35 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__6;
x_36 = l_Lean_Syntax_node2(x_6, x_35, x_11, x_34);
lean_ctor_set(x_7, 0, x_36);
return x_7;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_dec(x_7);
x_38 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__1;
lean_inc(x_6);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_6);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__3;
lean_inc(x_6);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__4;
lean_inc(x_6);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_42);
x_44 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__3;
lean_inc(x_6);
x_45 = l_Lean_Syntax_node1(x_6, x_44, x_43);
x_46 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_6);
x_47 = l_Lean_Syntax_node1(x_6, x_46, x_45);
x_48 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_6);
x_49 = l_Lean_Syntax_node1(x_6, x_48, x_47);
x_50 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_6);
x_51 = l_Lean_Syntax_node1(x_6, x_50, x_49);
x_52 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__2;
lean_inc(x_41);
lean_inc(x_6);
x_53 = l_Lean_Syntax_node2(x_6, x_52, x_41, x_51);
x_54 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__5;
lean_inc(x_6);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_6);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__6;
lean_inc(x_6);
x_57 = l_Lean_Syntax_node1(x_6, x_56, x_55);
lean_inc(x_6);
x_58 = l_Lean_Syntax_node1(x_6, x_46, x_57);
lean_inc(x_6);
x_59 = l_Lean_Syntax_node1(x_6, x_48, x_58);
lean_inc(x_6);
x_60 = l_Lean_Syntax_node1(x_6, x_50, x_59);
lean_inc(x_6);
x_61 = l_Lean_Syntax_node2(x_6, x_52, x_41, x_60);
lean_inc(x_6);
x_62 = l_Lean_Syntax_node2(x_6, x_46, x_53, x_61);
x_63 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__6;
x_64 = l_Lean_Syntax_node2(x_6, x_63, x_39, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_37);
return x_65;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("funInduction", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fun_induction", 13, 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
x_10 = l_Lean_PrettyPrinter_delab(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_7, 5);
lean_inc(x_13);
x_14 = 0;
x_15 = l_Lean_SourceInfo_fromRef(x_13, x_14);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_8, x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__3;
lean_inc(x_15);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
x_23 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
lean_inc(x_15);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__2;
lean_inc(x_24);
lean_inc(x_15);
x_26 = l_Lean_Syntax_node4(x_15, x_25, x_21, x_11, x_24, x_24);
x_27 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__4;
lean_inc(x_15);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_27);
x_29 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__3;
lean_inc(x_15);
x_30 = l_Lean_Syntax_node3(x_15, x_29, x_26, x_28, x_3);
if (x_4 == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_free_object(x_16);
x_31 = lean_st_ref_get(x_8, x_18);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_33 = lean_ctor_get(x_31, 1);
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5;
lean_inc(x_15);
lean_ctor_set_tag(x_31, 2);
lean_ctor_set(x_31, 1, x_35);
lean_ctor_set(x_31, 0, x_15);
x_36 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__14;
lean_inc(x_15);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_15);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__13;
lean_inc(x_15);
x_39 = l_Lean_Syntax_node1(x_15, x_38, x_37);
x_40 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15;
lean_inc(x_15);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_30);
lean_inc(x_15);
x_42 = l_Lean_Syntax_node3(x_15, x_22, x_39, x_41, x_30);
x_43 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_15);
x_44 = l_Lean_Syntax_node1(x_15, x_43, x_42);
x_45 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_15);
x_46 = l_Lean_Syntax_node1(x_15, x_45, x_44);
x_47 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18;
lean_inc(x_15);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_15);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4;
x_50 = l_Lean_Syntax_node3(x_15, x_49, x_31, x_46, x_48);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_30);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_array_mk(x_53);
x_55 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_54, x_7, x_8, x_33);
lean_dec(x_8);
lean_dec(x_7);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_56 = lean_ctor_get(x_31, 1);
lean_inc(x_56);
lean_dec(x_31);
x_57 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5;
lean_inc(x_15);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_15);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__14;
lean_inc(x_15);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_15);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__13;
lean_inc(x_15);
x_62 = l_Lean_Syntax_node1(x_15, x_61, x_60);
x_63 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15;
lean_inc(x_15);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_15);
lean_ctor_set(x_64, 1, x_63);
lean_inc(x_30);
lean_inc(x_15);
x_65 = l_Lean_Syntax_node3(x_15, x_22, x_62, x_64, x_30);
x_66 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_15);
x_67 = l_Lean_Syntax_node1(x_15, x_66, x_65);
x_68 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_15);
x_69 = l_Lean_Syntax_node1(x_15, x_68, x_67);
x_70 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18;
lean_inc(x_15);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_15);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4;
x_73 = l_Lean_Syntax_node3(x_15, x_72, x_58, x_69, x_71);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_30);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_array_mk(x_76);
x_78 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_77, x_7, x_8, x_56);
lean_dec(x_8);
lean_dec(x_7);
return x_78;
}
}
else
{
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_79 = lean_ctor_get(x_16, 1);
lean_inc(x_79);
lean_dec(x_16);
x_80 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__3;
lean_inc(x_15);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_15);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
x_83 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
lean_inc(x_15);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_15);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_84, 2, x_83);
x_85 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__2;
lean_inc(x_84);
lean_inc(x_15);
x_86 = l_Lean_Syntax_node4(x_15, x_85, x_81, x_11, x_84, x_84);
x_87 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__4;
lean_inc(x_15);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_15);
lean_ctor_set(x_88, 1, x_87);
x_89 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__3;
lean_inc(x_15);
x_90 = l_Lean_Syntax_node3(x_15, x_89, x_86, x_88, x_3);
if (x_4 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_91 = lean_st_ref_get(x_8, x_79);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5;
lean_inc(x_15);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(2, 2, 0);
} else {
 x_95 = x_93;
 lean_ctor_set_tag(x_95, 2);
}
lean_ctor_set(x_95, 0, x_15);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__14;
lean_inc(x_15);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_15);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__13;
lean_inc(x_15);
x_99 = l_Lean_Syntax_node1(x_15, x_98, x_97);
x_100 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15;
lean_inc(x_15);
x_101 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_101, 0, x_15);
lean_ctor_set(x_101, 1, x_100);
lean_inc(x_90);
lean_inc(x_15);
x_102 = l_Lean_Syntax_node3(x_15, x_82, x_99, x_101, x_90);
x_103 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_15);
x_104 = l_Lean_Syntax_node1(x_15, x_103, x_102);
x_105 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_15);
x_106 = l_Lean_Syntax_node1(x_15, x_105, x_104);
x_107 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18;
lean_inc(x_15);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_15);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4;
x_110 = l_Lean_Syntax_node3(x_15, x_109, x_95, x_106, x_108);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_90);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_array_mk(x_113);
x_115 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_114, x_7, x_8, x_92);
lean_dec(x_8);
lean_dec(x_7);
return x_115;
}
else
{
lean_object* x_116; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_90);
lean_ctor_set(x_116, 1, x_79);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_117 = !lean_is_exclusive(x_10);
if (x_117 == 0)
{
return x_10;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_10, 0);
x_119 = lean_ctor_get(x_10, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_10);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Expr_getAppFn(x_2);
x_10 = l_Lean_Expr_constName_x21(x_9);
lean_dec(x_9);
x_11 = l_Lean_NameSet_contains(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_2);
x_12 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___boxed), 9, 4);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_13);
x_17 = l_Lean_Meta_withExposedNames___rarg(x_16, x_4, x_5, x_6, x_7, x_14);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toIdent(x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_6, 5);
lean_inc(x_25);
lean_dec(x_6);
x_26 = 0;
x_27 = l_Lean_SourceInfo_fromRef(x_25, x_26);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_7, x_24);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__3;
lean_inc(x_27);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
x_34 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
lean_inc(x_27);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
x_36 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__2;
lean_inc(x_35);
lean_inc(x_27);
x_37 = l_Lean_Syntax_node4(x_27, x_36, x_32, x_23, x_35, x_35);
x_38 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__4;
lean_inc(x_27);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__3;
x_41 = l_Lean_Syntax_node3(x_27, x_40, x_37, x_39, x_3);
lean_ctor_set(x_28, 0, x_41);
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_dec(x_28);
x_43 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__3;
lean_inc(x_27);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
x_46 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
lean_inc(x_27);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_27);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_46);
x_48 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__2;
lean_inc(x_47);
lean_inc(x_27);
x_49 = l_Lean_Syntax_node4(x_27, x_48, x_44, x_23, x_47, x_47);
x_50 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__4;
lean_inc(x_27);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_27);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__3;
x_53 = l_Lean_Syntax_node3(x_27, x_52, x_49, x_51, x_3);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_42);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_22);
if (x_55 == 0)
{
return x_22;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_22, 0);
x_57 = lean_ctor_get(x_22, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_22);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_5, x_4);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_5, x_4, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx(x_2, x_13, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_21 = lean_array_uset(x_15, x_4, x_17);
x_4 = x_20;
x_5 = x_21;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Meta_FunInd_SeenCalls_uniques(x_8);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_array_size(x_10);
x_12 = 0;
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx___spec__1(x_2, x_9, x_11, x_12, x_10, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx(x_14, x_5, x_6, x_15);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_6);
lean_dec(x_5);
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
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpAll", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp_all", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("intros", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx(x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx(x_4, x_5, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx(x_1, x_2, x_3, x_4, x_5, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_4, 5);
lean_inc(x_18);
x_19 = 0;
x_20 = l_Lean_SourceInfo_fromRef(x_18, x_19);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_5, x_17);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__1;
lean_inc(x_20);
lean_ctor_set_tag(x_21, 2);
lean_ctor_set(x_21, 1, x_25);
lean_ctor_set(x_21, 0, x_20);
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__3;
lean_inc(x_20);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_26);
lean_ctor_set(x_11, 0, x_20);
x_27 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_20);
x_28 = l_Lean_Syntax_node1(x_20, x_27, x_9);
x_29 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_20);
x_30 = l_Lean_Syntax_node1(x_20, x_29, x_28);
x_31 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_20);
x_32 = l_Lean_Syntax_node1(x_20, x_31, x_30);
x_33 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__2;
lean_inc(x_11);
lean_inc(x_20);
x_34 = l_Lean_Syntax_node2(x_20, x_33, x_11, x_32);
lean_inc(x_20);
x_35 = l_Lean_Syntax_node1(x_20, x_27, x_13);
lean_inc(x_20);
x_36 = l_Lean_Syntax_node1(x_20, x_29, x_35);
lean_inc(x_20);
x_37 = l_Lean_Syntax_node1(x_20, x_31, x_36);
lean_inc(x_11);
lean_inc(x_20);
x_38 = l_Lean_Syntax_node2(x_20, x_33, x_11, x_37);
lean_inc(x_20);
x_39 = l_Lean_Syntax_node1(x_20, x_27, x_16);
lean_inc(x_20);
x_40 = l_Lean_Syntax_node1(x_20, x_29, x_39);
lean_inc(x_20);
x_41 = l_Lean_Syntax_node1(x_20, x_31, x_40);
lean_inc(x_11);
lean_inc(x_20);
x_42 = l_Lean_Syntax_node2(x_20, x_33, x_11, x_41);
x_43 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__3;
lean_inc(x_20);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_43);
lean_ctor_set(x_7, 0, x_20);
x_44 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
lean_inc(x_20);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_20);
lean_ctor_set(x_45, 1, x_27);
lean_ctor_set(x_45, 2, x_44);
x_46 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4;
lean_inc(x_45);
lean_inc(x_20);
x_47 = l_Lean_Syntax_node1(x_20, x_46, x_45);
x_48 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__2;
lean_inc_n(x_45, 3);
lean_inc(x_20);
x_49 = l_Lean_Syntax_node5(x_20, x_48, x_7, x_47, x_45, x_45, x_45);
lean_inc(x_20);
x_50 = l_Lean_Syntax_node1(x_20, x_27, x_49);
lean_inc(x_20);
x_51 = l_Lean_Syntax_node1(x_20, x_29, x_50);
lean_inc(x_20);
x_52 = l_Lean_Syntax_node1(x_20, x_31, x_51);
lean_inc(x_11);
lean_inc(x_20);
x_53 = l_Lean_Syntax_node2(x_20, x_33, x_11, x_52);
lean_inc(x_38);
lean_inc(x_34);
lean_inc(x_20);
x_54 = l_Lean_Syntax_node4(x_20, x_27, x_34, x_38, x_42, x_53);
x_55 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__6;
lean_inc(x_20);
x_56 = l_Lean_Syntax_node2(x_20, x_55, x_21, x_54);
lean_inc(x_5);
lean_inc(x_56);
x_57 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx(x_1, x_56, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_st_ref_get(x_5, x_59);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_62 = lean_ctor_get(x_60, 1);
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
x_64 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5;
lean_inc(x_20);
lean_ctor_set_tag(x_60, 2);
lean_ctor_set(x_60, 1, x_64);
lean_ctor_set(x_60, 0, x_20);
x_65 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__4;
lean_inc(x_20);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_20);
lean_ctor_set(x_66, 1, x_65);
x_67 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__5;
lean_inc(x_45);
lean_inc(x_20);
x_68 = l_Lean_Syntax_node2(x_20, x_67, x_66, x_45);
x_69 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15;
lean_inc(x_20);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_20);
lean_ctor_set(x_70, 1, x_69);
x_71 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__1;
lean_inc(x_20);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_20);
lean_ctor_set(x_72, 1, x_71);
x_73 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__10;
lean_inc(x_20);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_20);
lean_ctor_set(x_74, 1, x_73);
x_75 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__11;
lean_inc(x_20);
x_76 = l_Lean_Syntax_node2(x_20, x_75, x_74, x_45);
lean_inc(x_20);
x_77 = l_Lean_Syntax_node1(x_20, x_27, x_76);
lean_inc(x_20);
x_78 = l_Lean_Syntax_node1(x_20, x_29, x_77);
lean_inc(x_20);
x_79 = l_Lean_Syntax_node1(x_20, x_31, x_78);
lean_inc(x_11);
lean_inc(x_20);
x_80 = l_Lean_Syntax_node2(x_20, x_33, x_11, x_79);
lean_inc(x_20);
x_81 = l_Lean_Syntax_node3(x_20, x_27, x_34, x_38, x_80);
x_82 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__2;
lean_inc(x_72);
lean_inc(x_20);
x_83 = l_Lean_Syntax_node2(x_20, x_82, x_72, x_81);
lean_inc(x_20);
x_84 = l_Lean_Syntax_node3(x_20, x_27, x_68, x_70, x_83);
lean_inc(x_20);
x_85 = l_Lean_Syntax_node1(x_20, x_29, x_84);
lean_inc(x_20);
x_86 = l_Lean_Syntax_node1(x_20, x_31, x_85);
x_87 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18;
lean_inc(x_20);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_20);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4;
lean_inc(x_20);
x_90 = l_Lean_Syntax_node3(x_20, x_89, x_60, x_86, x_88);
x_91 = lean_st_ref_get(x_5, x_62);
lean_dec(x_5);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
lean_inc(x_20);
x_94 = l_Lean_Syntax_node1(x_20, x_27, x_56);
lean_inc(x_20);
x_95 = l_Lean_Syntax_node1(x_20, x_29, x_94);
lean_inc(x_20);
x_96 = l_Lean_Syntax_node1(x_20, x_31, x_95);
lean_inc(x_11);
lean_inc(x_20);
x_97 = l_Lean_Syntax_node2(x_20, x_33, x_11, x_96);
lean_inc(x_20);
x_98 = l_Lean_Syntax_node1(x_20, x_27, x_58);
lean_inc(x_20);
x_99 = l_Lean_Syntax_node1(x_20, x_29, x_98);
lean_inc(x_20);
x_100 = l_Lean_Syntax_node1(x_20, x_31, x_99);
lean_inc(x_11);
lean_inc(x_20);
x_101 = l_Lean_Syntax_node2(x_20, x_33, x_11, x_100);
lean_inc(x_20);
x_102 = l_Lean_Syntax_node1(x_20, x_27, x_90);
lean_inc(x_20);
x_103 = l_Lean_Syntax_node1(x_20, x_29, x_102);
lean_inc(x_20);
x_104 = l_Lean_Syntax_node1(x_20, x_31, x_103);
lean_inc(x_20);
x_105 = l_Lean_Syntax_node2(x_20, x_33, x_11, x_104);
lean_inc(x_20);
x_106 = l_Lean_Syntax_node3(x_20, x_27, x_97, x_101, x_105);
x_107 = l_Lean_Syntax_node2(x_20, x_82, x_72, x_106);
lean_ctor_set(x_91, 0, x_107);
return x_91;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_108 = lean_ctor_get(x_91, 1);
lean_inc(x_108);
lean_dec(x_91);
lean_inc(x_20);
x_109 = l_Lean_Syntax_node1(x_20, x_27, x_56);
lean_inc(x_20);
x_110 = l_Lean_Syntax_node1(x_20, x_29, x_109);
lean_inc(x_20);
x_111 = l_Lean_Syntax_node1(x_20, x_31, x_110);
lean_inc(x_11);
lean_inc(x_20);
x_112 = l_Lean_Syntax_node2(x_20, x_33, x_11, x_111);
lean_inc(x_20);
x_113 = l_Lean_Syntax_node1(x_20, x_27, x_58);
lean_inc(x_20);
x_114 = l_Lean_Syntax_node1(x_20, x_29, x_113);
lean_inc(x_20);
x_115 = l_Lean_Syntax_node1(x_20, x_31, x_114);
lean_inc(x_11);
lean_inc(x_20);
x_116 = l_Lean_Syntax_node2(x_20, x_33, x_11, x_115);
lean_inc(x_20);
x_117 = l_Lean_Syntax_node1(x_20, x_27, x_90);
lean_inc(x_20);
x_118 = l_Lean_Syntax_node1(x_20, x_29, x_117);
lean_inc(x_20);
x_119 = l_Lean_Syntax_node1(x_20, x_31, x_118);
lean_inc(x_20);
x_120 = l_Lean_Syntax_node2(x_20, x_33, x_11, x_119);
lean_inc(x_20);
x_121 = l_Lean_Syntax_node3(x_20, x_27, x_112, x_116, x_120);
x_122 = l_Lean_Syntax_node2(x_20, x_82, x_72, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_108);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_124 = lean_ctor_get(x_60, 1);
lean_inc(x_124);
lean_dec(x_60);
x_125 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5;
lean_inc(x_20);
x_126 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_126, 0, x_20);
lean_ctor_set(x_126, 1, x_125);
x_127 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__4;
lean_inc(x_20);
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_20);
lean_ctor_set(x_128, 1, x_127);
x_129 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__5;
lean_inc(x_45);
lean_inc(x_20);
x_130 = l_Lean_Syntax_node2(x_20, x_129, x_128, x_45);
x_131 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15;
lean_inc(x_20);
x_132 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_132, 0, x_20);
lean_ctor_set(x_132, 1, x_131);
x_133 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__1;
lean_inc(x_20);
x_134 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_134, 0, x_20);
lean_ctor_set(x_134, 1, x_133);
x_135 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__10;
lean_inc(x_20);
x_136 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_136, 0, x_20);
lean_ctor_set(x_136, 1, x_135);
x_137 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__11;
lean_inc(x_20);
x_138 = l_Lean_Syntax_node2(x_20, x_137, x_136, x_45);
lean_inc(x_20);
x_139 = l_Lean_Syntax_node1(x_20, x_27, x_138);
lean_inc(x_20);
x_140 = l_Lean_Syntax_node1(x_20, x_29, x_139);
lean_inc(x_20);
x_141 = l_Lean_Syntax_node1(x_20, x_31, x_140);
lean_inc(x_11);
lean_inc(x_20);
x_142 = l_Lean_Syntax_node2(x_20, x_33, x_11, x_141);
lean_inc(x_20);
x_143 = l_Lean_Syntax_node3(x_20, x_27, x_34, x_38, x_142);
x_144 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__2;
lean_inc(x_134);
lean_inc(x_20);
x_145 = l_Lean_Syntax_node2(x_20, x_144, x_134, x_143);
lean_inc(x_20);
x_146 = l_Lean_Syntax_node3(x_20, x_27, x_130, x_132, x_145);
lean_inc(x_20);
x_147 = l_Lean_Syntax_node1(x_20, x_29, x_146);
lean_inc(x_20);
x_148 = l_Lean_Syntax_node1(x_20, x_31, x_147);
x_149 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18;
lean_inc(x_20);
x_150 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_150, 0, x_20);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4;
lean_inc(x_20);
x_152 = l_Lean_Syntax_node3(x_20, x_151, x_126, x_148, x_150);
x_153 = lean_st_ref_get(x_5, x_124);
lean_dec(x_5);
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
lean_inc(x_20);
x_156 = l_Lean_Syntax_node1(x_20, x_27, x_56);
lean_inc(x_20);
x_157 = l_Lean_Syntax_node1(x_20, x_29, x_156);
lean_inc(x_20);
x_158 = l_Lean_Syntax_node1(x_20, x_31, x_157);
lean_inc(x_11);
lean_inc(x_20);
x_159 = l_Lean_Syntax_node2(x_20, x_33, x_11, x_158);
lean_inc(x_20);
x_160 = l_Lean_Syntax_node1(x_20, x_27, x_58);
lean_inc(x_20);
x_161 = l_Lean_Syntax_node1(x_20, x_29, x_160);
lean_inc(x_20);
x_162 = l_Lean_Syntax_node1(x_20, x_31, x_161);
lean_inc(x_11);
lean_inc(x_20);
x_163 = l_Lean_Syntax_node2(x_20, x_33, x_11, x_162);
lean_inc(x_20);
x_164 = l_Lean_Syntax_node1(x_20, x_27, x_152);
lean_inc(x_20);
x_165 = l_Lean_Syntax_node1(x_20, x_29, x_164);
lean_inc(x_20);
x_166 = l_Lean_Syntax_node1(x_20, x_31, x_165);
lean_inc(x_20);
x_167 = l_Lean_Syntax_node2(x_20, x_33, x_11, x_166);
lean_inc(x_20);
x_168 = l_Lean_Syntax_node3(x_20, x_27, x_159, x_163, x_167);
x_169 = l_Lean_Syntax_node2(x_20, x_144, x_134, x_168);
if (lean_is_scalar(x_155)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_155;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_154);
return x_170;
}
}
else
{
uint8_t x_171; 
lean_dec(x_56);
lean_dec(x_45);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_20);
lean_dec(x_5);
x_171 = !lean_is_exclusive(x_57);
if (x_171 == 0)
{
return x_57;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_57, 0);
x_173 = lean_ctor_get(x_57, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_57);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_175 = lean_ctor_get(x_21, 1);
lean_inc(x_175);
lean_dec(x_21);
x_176 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__1;
lean_inc(x_20);
x_177 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_177, 0, x_20);
lean_ctor_set(x_177, 1, x_176);
x_178 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__3;
lean_inc(x_20);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_178);
lean_ctor_set(x_11, 0, x_20);
x_179 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_20);
x_180 = l_Lean_Syntax_node1(x_20, x_179, x_9);
x_181 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_20);
x_182 = l_Lean_Syntax_node1(x_20, x_181, x_180);
x_183 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_20);
x_184 = l_Lean_Syntax_node1(x_20, x_183, x_182);
x_185 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__2;
lean_inc(x_11);
lean_inc(x_20);
x_186 = l_Lean_Syntax_node2(x_20, x_185, x_11, x_184);
lean_inc(x_20);
x_187 = l_Lean_Syntax_node1(x_20, x_179, x_13);
lean_inc(x_20);
x_188 = l_Lean_Syntax_node1(x_20, x_181, x_187);
lean_inc(x_20);
x_189 = l_Lean_Syntax_node1(x_20, x_183, x_188);
lean_inc(x_11);
lean_inc(x_20);
x_190 = l_Lean_Syntax_node2(x_20, x_185, x_11, x_189);
lean_inc(x_20);
x_191 = l_Lean_Syntax_node1(x_20, x_179, x_16);
lean_inc(x_20);
x_192 = l_Lean_Syntax_node1(x_20, x_181, x_191);
lean_inc(x_20);
x_193 = l_Lean_Syntax_node1(x_20, x_183, x_192);
lean_inc(x_11);
lean_inc(x_20);
x_194 = l_Lean_Syntax_node2(x_20, x_185, x_11, x_193);
x_195 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__3;
lean_inc(x_20);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_195);
lean_ctor_set(x_7, 0, x_20);
x_196 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
lean_inc(x_20);
x_197 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_197, 0, x_20);
lean_ctor_set(x_197, 1, x_179);
lean_ctor_set(x_197, 2, x_196);
x_198 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4;
lean_inc(x_197);
lean_inc(x_20);
x_199 = l_Lean_Syntax_node1(x_20, x_198, x_197);
x_200 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__2;
lean_inc_n(x_197, 3);
lean_inc(x_20);
x_201 = l_Lean_Syntax_node5(x_20, x_200, x_7, x_199, x_197, x_197, x_197);
lean_inc(x_20);
x_202 = l_Lean_Syntax_node1(x_20, x_179, x_201);
lean_inc(x_20);
x_203 = l_Lean_Syntax_node1(x_20, x_181, x_202);
lean_inc(x_20);
x_204 = l_Lean_Syntax_node1(x_20, x_183, x_203);
lean_inc(x_11);
lean_inc(x_20);
x_205 = l_Lean_Syntax_node2(x_20, x_185, x_11, x_204);
lean_inc(x_190);
lean_inc(x_186);
lean_inc(x_20);
x_206 = l_Lean_Syntax_node4(x_20, x_179, x_186, x_190, x_194, x_205);
x_207 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__6;
lean_inc(x_20);
x_208 = l_Lean_Syntax_node2(x_20, x_207, x_177, x_206);
lean_inc(x_5);
lean_inc(x_208);
x_209 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx(x_1, x_208, x_2, x_3, x_4, x_5, x_175);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_st_ref_get(x_5, x_211);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
x_215 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5;
lean_inc(x_20);
if (lean_is_scalar(x_214)) {
 x_216 = lean_alloc_ctor(2, 2, 0);
} else {
 x_216 = x_214;
 lean_ctor_set_tag(x_216, 2);
}
lean_ctor_set(x_216, 0, x_20);
lean_ctor_set(x_216, 1, x_215);
x_217 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__4;
lean_inc(x_20);
x_218 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_218, 0, x_20);
lean_ctor_set(x_218, 1, x_217);
x_219 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__5;
lean_inc(x_197);
lean_inc(x_20);
x_220 = l_Lean_Syntax_node2(x_20, x_219, x_218, x_197);
x_221 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15;
lean_inc(x_20);
x_222 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_222, 0, x_20);
lean_ctor_set(x_222, 1, x_221);
x_223 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__1;
lean_inc(x_20);
x_224 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_224, 0, x_20);
lean_ctor_set(x_224, 1, x_223);
x_225 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__10;
lean_inc(x_20);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_20);
lean_ctor_set(x_226, 1, x_225);
x_227 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__11;
lean_inc(x_20);
x_228 = l_Lean_Syntax_node2(x_20, x_227, x_226, x_197);
lean_inc(x_20);
x_229 = l_Lean_Syntax_node1(x_20, x_179, x_228);
lean_inc(x_20);
x_230 = l_Lean_Syntax_node1(x_20, x_181, x_229);
lean_inc(x_20);
x_231 = l_Lean_Syntax_node1(x_20, x_183, x_230);
lean_inc(x_11);
lean_inc(x_20);
x_232 = l_Lean_Syntax_node2(x_20, x_185, x_11, x_231);
lean_inc(x_20);
x_233 = l_Lean_Syntax_node3(x_20, x_179, x_186, x_190, x_232);
x_234 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__2;
lean_inc(x_224);
lean_inc(x_20);
x_235 = l_Lean_Syntax_node2(x_20, x_234, x_224, x_233);
lean_inc(x_20);
x_236 = l_Lean_Syntax_node3(x_20, x_179, x_220, x_222, x_235);
lean_inc(x_20);
x_237 = l_Lean_Syntax_node1(x_20, x_181, x_236);
lean_inc(x_20);
x_238 = l_Lean_Syntax_node1(x_20, x_183, x_237);
x_239 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18;
lean_inc(x_20);
x_240 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_240, 0, x_20);
lean_ctor_set(x_240, 1, x_239);
x_241 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4;
lean_inc(x_20);
x_242 = l_Lean_Syntax_node3(x_20, x_241, x_216, x_238, x_240);
x_243 = lean_st_ref_get(x_5, x_213);
lean_dec(x_5);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_245 = x_243;
} else {
 lean_dec_ref(x_243);
 x_245 = lean_box(0);
}
lean_inc(x_20);
x_246 = l_Lean_Syntax_node1(x_20, x_179, x_208);
lean_inc(x_20);
x_247 = l_Lean_Syntax_node1(x_20, x_181, x_246);
lean_inc(x_20);
x_248 = l_Lean_Syntax_node1(x_20, x_183, x_247);
lean_inc(x_11);
lean_inc(x_20);
x_249 = l_Lean_Syntax_node2(x_20, x_185, x_11, x_248);
lean_inc(x_20);
x_250 = l_Lean_Syntax_node1(x_20, x_179, x_210);
lean_inc(x_20);
x_251 = l_Lean_Syntax_node1(x_20, x_181, x_250);
lean_inc(x_20);
x_252 = l_Lean_Syntax_node1(x_20, x_183, x_251);
lean_inc(x_11);
lean_inc(x_20);
x_253 = l_Lean_Syntax_node2(x_20, x_185, x_11, x_252);
lean_inc(x_20);
x_254 = l_Lean_Syntax_node1(x_20, x_179, x_242);
lean_inc(x_20);
x_255 = l_Lean_Syntax_node1(x_20, x_181, x_254);
lean_inc(x_20);
x_256 = l_Lean_Syntax_node1(x_20, x_183, x_255);
lean_inc(x_20);
x_257 = l_Lean_Syntax_node2(x_20, x_185, x_11, x_256);
lean_inc(x_20);
x_258 = l_Lean_Syntax_node3(x_20, x_179, x_249, x_253, x_257);
x_259 = l_Lean_Syntax_node2(x_20, x_234, x_224, x_258);
if (lean_is_scalar(x_245)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_245;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_244);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_208);
lean_dec(x_197);
lean_dec(x_190);
lean_dec(x_186);
lean_dec(x_11);
lean_dec(x_20);
lean_dec(x_5);
x_261 = lean_ctor_get(x_209, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_209, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_263 = x_209;
} else {
 lean_dec_ref(x_209);
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
}
else
{
uint8_t x_265; 
lean_free_object(x_11);
lean_dec(x_13);
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_265 = !lean_is_exclusive(x_15);
if (x_265 == 0)
{
return x_15;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_15, 0);
x_267 = lean_ctor_get(x_15, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_15);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_11, 0);
x_270 = lean_ctor_get(x_11, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_271 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx(x_1, x_2, x_3, x_4, x_5, x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_ctor_get(x_4, 5);
lean_inc(x_274);
x_275 = 0;
x_276 = l_Lean_SourceInfo_fromRef(x_274, x_275);
lean_dec(x_274);
x_277 = lean_st_ref_get(x_5, x_273);
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_279 = x_277;
} else {
 lean_dec_ref(x_277);
 x_279 = lean_box(0);
}
x_280 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__1;
lean_inc(x_276);
if (lean_is_scalar(x_279)) {
 x_281 = lean_alloc_ctor(2, 2, 0);
} else {
 x_281 = x_279;
 lean_ctor_set_tag(x_281, 2);
}
lean_ctor_set(x_281, 0, x_276);
lean_ctor_set(x_281, 1, x_280);
x_282 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__3;
lean_inc(x_276);
x_283 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_283, 0, x_276);
lean_ctor_set(x_283, 1, x_282);
x_284 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_276);
x_285 = l_Lean_Syntax_node1(x_276, x_284, x_9);
x_286 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_276);
x_287 = l_Lean_Syntax_node1(x_276, x_286, x_285);
x_288 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_276);
x_289 = l_Lean_Syntax_node1(x_276, x_288, x_287);
x_290 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__2;
lean_inc(x_283);
lean_inc(x_276);
x_291 = l_Lean_Syntax_node2(x_276, x_290, x_283, x_289);
lean_inc(x_276);
x_292 = l_Lean_Syntax_node1(x_276, x_284, x_269);
lean_inc(x_276);
x_293 = l_Lean_Syntax_node1(x_276, x_286, x_292);
lean_inc(x_276);
x_294 = l_Lean_Syntax_node1(x_276, x_288, x_293);
lean_inc(x_283);
lean_inc(x_276);
x_295 = l_Lean_Syntax_node2(x_276, x_290, x_283, x_294);
lean_inc(x_276);
x_296 = l_Lean_Syntax_node1(x_276, x_284, x_272);
lean_inc(x_276);
x_297 = l_Lean_Syntax_node1(x_276, x_286, x_296);
lean_inc(x_276);
x_298 = l_Lean_Syntax_node1(x_276, x_288, x_297);
lean_inc(x_283);
lean_inc(x_276);
x_299 = l_Lean_Syntax_node2(x_276, x_290, x_283, x_298);
x_300 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__3;
lean_inc(x_276);
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_300);
lean_ctor_set(x_7, 0, x_276);
x_301 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
lean_inc(x_276);
x_302 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_302, 0, x_276);
lean_ctor_set(x_302, 1, x_284);
lean_ctor_set(x_302, 2, x_301);
x_303 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4;
lean_inc(x_302);
lean_inc(x_276);
x_304 = l_Lean_Syntax_node1(x_276, x_303, x_302);
x_305 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__2;
lean_inc_n(x_302, 3);
lean_inc(x_276);
x_306 = l_Lean_Syntax_node5(x_276, x_305, x_7, x_304, x_302, x_302, x_302);
lean_inc(x_276);
x_307 = l_Lean_Syntax_node1(x_276, x_284, x_306);
lean_inc(x_276);
x_308 = l_Lean_Syntax_node1(x_276, x_286, x_307);
lean_inc(x_276);
x_309 = l_Lean_Syntax_node1(x_276, x_288, x_308);
lean_inc(x_283);
lean_inc(x_276);
x_310 = l_Lean_Syntax_node2(x_276, x_290, x_283, x_309);
lean_inc(x_295);
lean_inc(x_291);
lean_inc(x_276);
x_311 = l_Lean_Syntax_node4(x_276, x_284, x_291, x_295, x_299, x_310);
x_312 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__6;
lean_inc(x_276);
x_313 = l_Lean_Syntax_node2(x_276, x_312, x_281, x_311);
lean_inc(x_5);
lean_inc(x_313);
x_314 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx(x_1, x_313, x_2, x_3, x_4, x_5, x_278);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = lean_st_ref_get(x_5, x_316);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_319 = x_317;
} else {
 lean_dec_ref(x_317);
 x_319 = lean_box(0);
}
x_320 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5;
lean_inc(x_276);
if (lean_is_scalar(x_319)) {
 x_321 = lean_alloc_ctor(2, 2, 0);
} else {
 x_321 = x_319;
 lean_ctor_set_tag(x_321, 2);
}
lean_ctor_set(x_321, 0, x_276);
lean_ctor_set(x_321, 1, x_320);
x_322 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__4;
lean_inc(x_276);
x_323 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_323, 0, x_276);
lean_ctor_set(x_323, 1, x_322);
x_324 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__5;
lean_inc(x_302);
lean_inc(x_276);
x_325 = l_Lean_Syntax_node2(x_276, x_324, x_323, x_302);
x_326 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15;
lean_inc(x_276);
x_327 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_327, 0, x_276);
lean_ctor_set(x_327, 1, x_326);
x_328 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__1;
lean_inc(x_276);
x_329 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_329, 0, x_276);
lean_ctor_set(x_329, 1, x_328);
x_330 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__10;
lean_inc(x_276);
x_331 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_331, 0, x_276);
lean_ctor_set(x_331, 1, x_330);
x_332 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__11;
lean_inc(x_276);
x_333 = l_Lean_Syntax_node2(x_276, x_332, x_331, x_302);
lean_inc(x_276);
x_334 = l_Lean_Syntax_node1(x_276, x_284, x_333);
lean_inc(x_276);
x_335 = l_Lean_Syntax_node1(x_276, x_286, x_334);
lean_inc(x_276);
x_336 = l_Lean_Syntax_node1(x_276, x_288, x_335);
lean_inc(x_283);
lean_inc(x_276);
x_337 = l_Lean_Syntax_node2(x_276, x_290, x_283, x_336);
lean_inc(x_276);
x_338 = l_Lean_Syntax_node3(x_276, x_284, x_291, x_295, x_337);
x_339 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__2;
lean_inc(x_329);
lean_inc(x_276);
x_340 = l_Lean_Syntax_node2(x_276, x_339, x_329, x_338);
lean_inc(x_276);
x_341 = l_Lean_Syntax_node3(x_276, x_284, x_325, x_327, x_340);
lean_inc(x_276);
x_342 = l_Lean_Syntax_node1(x_276, x_286, x_341);
lean_inc(x_276);
x_343 = l_Lean_Syntax_node1(x_276, x_288, x_342);
x_344 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18;
lean_inc(x_276);
x_345 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_345, 0, x_276);
lean_ctor_set(x_345, 1, x_344);
x_346 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4;
lean_inc(x_276);
x_347 = l_Lean_Syntax_node3(x_276, x_346, x_321, x_343, x_345);
x_348 = lean_st_ref_get(x_5, x_318);
lean_dec(x_5);
x_349 = lean_ctor_get(x_348, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_350 = x_348;
} else {
 lean_dec_ref(x_348);
 x_350 = lean_box(0);
}
lean_inc(x_276);
x_351 = l_Lean_Syntax_node1(x_276, x_284, x_313);
lean_inc(x_276);
x_352 = l_Lean_Syntax_node1(x_276, x_286, x_351);
lean_inc(x_276);
x_353 = l_Lean_Syntax_node1(x_276, x_288, x_352);
lean_inc(x_283);
lean_inc(x_276);
x_354 = l_Lean_Syntax_node2(x_276, x_290, x_283, x_353);
lean_inc(x_276);
x_355 = l_Lean_Syntax_node1(x_276, x_284, x_315);
lean_inc(x_276);
x_356 = l_Lean_Syntax_node1(x_276, x_286, x_355);
lean_inc(x_276);
x_357 = l_Lean_Syntax_node1(x_276, x_288, x_356);
lean_inc(x_283);
lean_inc(x_276);
x_358 = l_Lean_Syntax_node2(x_276, x_290, x_283, x_357);
lean_inc(x_276);
x_359 = l_Lean_Syntax_node1(x_276, x_284, x_347);
lean_inc(x_276);
x_360 = l_Lean_Syntax_node1(x_276, x_286, x_359);
lean_inc(x_276);
x_361 = l_Lean_Syntax_node1(x_276, x_288, x_360);
lean_inc(x_276);
x_362 = l_Lean_Syntax_node2(x_276, x_290, x_283, x_361);
lean_inc(x_276);
x_363 = l_Lean_Syntax_node3(x_276, x_284, x_354, x_358, x_362);
x_364 = l_Lean_Syntax_node2(x_276, x_339, x_329, x_363);
if (lean_is_scalar(x_350)) {
 x_365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_365 = x_350;
}
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_349);
return x_365;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_313);
lean_dec(x_302);
lean_dec(x_295);
lean_dec(x_291);
lean_dec(x_283);
lean_dec(x_276);
lean_dec(x_5);
x_366 = lean_ctor_get(x_314, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_314, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_368 = x_314;
} else {
 lean_dec_ref(x_314);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(1, 2, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_366);
lean_ctor_set(x_369, 1, x_367);
return x_369;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_269);
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_370 = lean_ctor_get(x_271, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_271, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_372 = x_271;
} else {
 lean_dec_ref(x_271);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(1, 2, 0);
} else {
 x_373 = x_372;
}
lean_ctor_set(x_373, 0, x_370);
lean_ctor_set(x_373, 1, x_371);
return x_373;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_374 = lean_ctor_get(x_7, 0);
x_375 = lean_ctor_get(x_7, 1);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_7);
x_376 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx(x_4, x_5, x_375);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_379 = x_376;
} else {
 lean_dec_ref(x_376);
 x_379 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_380 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx(x_1, x_2, x_3, x_4, x_5, x_378);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_383 = lean_ctor_get(x_4, 5);
lean_inc(x_383);
x_384 = 0;
x_385 = l_Lean_SourceInfo_fromRef(x_383, x_384);
lean_dec(x_383);
x_386 = lean_st_ref_get(x_5, x_382);
x_387 = lean_ctor_get(x_386, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 x_388 = x_386;
} else {
 lean_dec_ref(x_386);
 x_388 = lean_box(0);
}
x_389 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__1;
lean_inc(x_385);
if (lean_is_scalar(x_388)) {
 x_390 = lean_alloc_ctor(2, 2, 0);
} else {
 x_390 = x_388;
 lean_ctor_set_tag(x_390, 2);
}
lean_ctor_set(x_390, 0, x_385);
lean_ctor_set(x_390, 1, x_389);
x_391 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__3;
lean_inc(x_385);
if (lean_is_scalar(x_379)) {
 x_392 = lean_alloc_ctor(2, 2, 0);
} else {
 x_392 = x_379;
 lean_ctor_set_tag(x_392, 2);
}
lean_ctor_set(x_392, 0, x_385);
lean_ctor_set(x_392, 1, x_391);
x_393 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11;
lean_inc(x_385);
x_394 = l_Lean_Syntax_node1(x_385, x_393, x_374);
x_395 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9;
lean_inc(x_385);
x_396 = l_Lean_Syntax_node1(x_385, x_395, x_394);
x_397 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7;
lean_inc(x_385);
x_398 = l_Lean_Syntax_node1(x_385, x_397, x_396);
x_399 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__2;
lean_inc(x_392);
lean_inc(x_385);
x_400 = l_Lean_Syntax_node2(x_385, x_399, x_392, x_398);
lean_inc(x_385);
x_401 = l_Lean_Syntax_node1(x_385, x_393, x_377);
lean_inc(x_385);
x_402 = l_Lean_Syntax_node1(x_385, x_395, x_401);
lean_inc(x_385);
x_403 = l_Lean_Syntax_node1(x_385, x_397, x_402);
lean_inc(x_392);
lean_inc(x_385);
x_404 = l_Lean_Syntax_node2(x_385, x_399, x_392, x_403);
lean_inc(x_385);
x_405 = l_Lean_Syntax_node1(x_385, x_393, x_381);
lean_inc(x_385);
x_406 = l_Lean_Syntax_node1(x_385, x_395, x_405);
lean_inc(x_385);
x_407 = l_Lean_Syntax_node1(x_385, x_397, x_406);
lean_inc(x_392);
lean_inc(x_385);
x_408 = l_Lean_Syntax_node2(x_385, x_399, x_392, x_407);
x_409 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__3;
lean_inc(x_385);
x_410 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_410, 0, x_385);
lean_ctor_set(x_410, 1, x_409);
x_411 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2;
lean_inc(x_385);
x_412 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_412, 0, x_385);
lean_ctor_set(x_412, 1, x_393);
lean_ctor_set(x_412, 2, x_411);
x_413 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4;
lean_inc(x_412);
lean_inc(x_385);
x_414 = l_Lean_Syntax_node1(x_385, x_413, x_412);
x_415 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__2;
lean_inc_n(x_412, 3);
lean_inc(x_385);
x_416 = l_Lean_Syntax_node5(x_385, x_415, x_410, x_414, x_412, x_412, x_412);
lean_inc(x_385);
x_417 = l_Lean_Syntax_node1(x_385, x_393, x_416);
lean_inc(x_385);
x_418 = l_Lean_Syntax_node1(x_385, x_395, x_417);
lean_inc(x_385);
x_419 = l_Lean_Syntax_node1(x_385, x_397, x_418);
lean_inc(x_392);
lean_inc(x_385);
x_420 = l_Lean_Syntax_node2(x_385, x_399, x_392, x_419);
lean_inc(x_404);
lean_inc(x_400);
lean_inc(x_385);
x_421 = l_Lean_Syntax_node4(x_385, x_393, x_400, x_404, x_408, x_420);
x_422 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__6;
lean_inc(x_385);
x_423 = l_Lean_Syntax_node2(x_385, x_422, x_390, x_421);
lean_inc(x_5);
lean_inc(x_423);
x_424 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkAllFunIndStx(x_1, x_423, x_2, x_3, x_4, x_5, x_387);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
x_427 = lean_st_ref_get(x_5, x_426);
x_428 = lean_ctor_get(x_427, 1);
lean_inc(x_428);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 x_429 = x_427;
} else {
 lean_dec_ref(x_427);
 x_429 = lean_box(0);
}
x_430 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5;
lean_inc(x_385);
if (lean_is_scalar(x_429)) {
 x_431 = lean_alloc_ctor(2, 2, 0);
} else {
 x_431 = x_429;
 lean_ctor_set_tag(x_431, 2);
}
lean_ctor_set(x_431, 0, x_385);
lean_ctor_set(x_431, 1, x_430);
x_432 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__4;
lean_inc(x_385);
x_433 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_433, 0, x_385);
lean_ctor_set(x_433, 1, x_432);
x_434 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__5;
lean_inc(x_412);
lean_inc(x_385);
x_435 = l_Lean_Syntax_node2(x_385, x_434, x_433, x_412);
x_436 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15;
lean_inc(x_385);
x_437 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_437, 0, x_385);
lean_ctor_set(x_437, 1, x_436);
x_438 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__1;
lean_inc(x_385);
x_439 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_439, 0, x_385);
lean_ctor_set(x_439, 1, x_438);
x_440 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__10;
lean_inc(x_385);
x_441 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_441, 0, x_385);
lean_ctor_set(x_441, 1, x_440);
x_442 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__11;
lean_inc(x_385);
x_443 = l_Lean_Syntax_node2(x_385, x_442, x_441, x_412);
lean_inc(x_385);
x_444 = l_Lean_Syntax_node1(x_385, x_393, x_443);
lean_inc(x_385);
x_445 = l_Lean_Syntax_node1(x_385, x_395, x_444);
lean_inc(x_385);
x_446 = l_Lean_Syntax_node1(x_385, x_397, x_445);
lean_inc(x_392);
lean_inc(x_385);
x_447 = l_Lean_Syntax_node2(x_385, x_399, x_392, x_446);
lean_inc(x_385);
x_448 = l_Lean_Syntax_node3(x_385, x_393, x_400, x_404, x_447);
x_449 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__2;
lean_inc(x_439);
lean_inc(x_385);
x_450 = l_Lean_Syntax_node2(x_385, x_449, x_439, x_448);
lean_inc(x_385);
x_451 = l_Lean_Syntax_node3(x_385, x_393, x_435, x_437, x_450);
lean_inc(x_385);
x_452 = l_Lean_Syntax_node1(x_385, x_395, x_451);
lean_inc(x_385);
x_453 = l_Lean_Syntax_node1(x_385, x_397, x_452);
x_454 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18;
lean_inc(x_385);
x_455 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_455, 0, x_385);
lean_ctor_set(x_455, 1, x_454);
x_456 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4;
lean_inc(x_385);
x_457 = l_Lean_Syntax_node3(x_385, x_456, x_431, x_453, x_455);
x_458 = lean_st_ref_get(x_5, x_428);
lean_dec(x_5);
x_459 = lean_ctor_get(x_458, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_460 = x_458;
} else {
 lean_dec_ref(x_458);
 x_460 = lean_box(0);
}
lean_inc(x_385);
x_461 = l_Lean_Syntax_node1(x_385, x_393, x_423);
lean_inc(x_385);
x_462 = l_Lean_Syntax_node1(x_385, x_395, x_461);
lean_inc(x_385);
x_463 = l_Lean_Syntax_node1(x_385, x_397, x_462);
lean_inc(x_392);
lean_inc(x_385);
x_464 = l_Lean_Syntax_node2(x_385, x_399, x_392, x_463);
lean_inc(x_385);
x_465 = l_Lean_Syntax_node1(x_385, x_393, x_425);
lean_inc(x_385);
x_466 = l_Lean_Syntax_node1(x_385, x_395, x_465);
lean_inc(x_385);
x_467 = l_Lean_Syntax_node1(x_385, x_397, x_466);
lean_inc(x_392);
lean_inc(x_385);
x_468 = l_Lean_Syntax_node2(x_385, x_399, x_392, x_467);
lean_inc(x_385);
x_469 = l_Lean_Syntax_node1(x_385, x_393, x_457);
lean_inc(x_385);
x_470 = l_Lean_Syntax_node1(x_385, x_395, x_469);
lean_inc(x_385);
x_471 = l_Lean_Syntax_node1(x_385, x_397, x_470);
lean_inc(x_385);
x_472 = l_Lean_Syntax_node2(x_385, x_399, x_392, x_471);
lean_inc(x_385);
x_473 = l_Lean_Syntax_node3(x_385, x_393, x_464, x_468, x_472);
x_474 = l_Lean_Syntax_node2(x_385, x_449, x_439, x_473);
if (lean_is_scalar(x_460)) {
 x_475 = lean_alloc_ctor(0, 2, 0);
} else {
 x_475 = x_460;
}
lean_ctor_set(x_475, 0, x_474);
lean_ctor_set(x_475, 1, x_459);
return x_475;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_423);
lean_dec(x_412);
lean_dec(x_404);
lean_dec(x_400);
lean_dec(x_392);
lean_dec(x_385);
lean_dec(x_5);
x_476 = lean_ctor_get(x_424, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_424, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 x_478 = x_424;
} else {
 lean_dec_ref(x_424);
 x_478 = lean_box(0);
}
if (lean_is_scalar(x_478)) {
 x_479 = lean_alloc_ctor(1, 2, 0);
} else {
 x_479 = x_478;
}
lean_ctor_set(x_479, 0, x_476);
lean_ctor_set(x_479, 1, x_477);
return x_479;
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_379);
lean_dec(x_377);
lean_dec(x_374);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_480 = lean_ctor_get(x_380, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_380, 1);
lean_inc(x_481);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_482 = x_380;
} else {
 lean_dec_ref(x_380);
 x_482 = lean_box(0);
}
if (lean_is_scalar(x_482)) {
 x_483 = lean_alloc_ctor(1, 2, 0);
} else {
 x_483 = x_482;
}
lean_ctor_set(x_483, 0, x_480);
lean_ctor_set(x_483, 1, x_481);
return x_483;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalTryTrace___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_Elab_Tactic_elabTryConfig(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_13);
x_18 = l_Lean_Meta_Try_Collector_main(x_16, x_13, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx(x_19, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Tactic_Try_evalAndSuggest(x_2, x_22, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
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
else
{
uint8_t x_33; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_12);
if (x_37 == 0)
{
return x_12;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_12, 0);
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_12);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalTryTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tryTrace", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Try_evalTryTrace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l_Lean_Elab_Tactic_Try_evalTryTrace___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalTryTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_Try_evalTryTrace___closed__2;
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
x_18 = l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4;
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
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalTryTrace___lambda__1___boxed), 11, 2);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_15);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___rarg), 10, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = l_Lean_Elab_Tactic_focus___rarg(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Try_evalTryTrace___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_Try_evalTryTrace___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalTryTrace", 12, 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__1;
x_3 = l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2;
x_4 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__2;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Try_evalTryTrace), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__4;
x_3 = l_Lean_Elab_Tactic_Try_evalTryTrace___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__3;
x_5 = l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init_Try(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_ExposeNames(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Try(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_LibrarySearch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Grind(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Try(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Try(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_ExposeNames(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Try(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_SimpTrace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_LibrarySearch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__1);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__2 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__2);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__3 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__3);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__4 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Try___hyg_6____closed__4);
l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__1);
l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__2);
l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__3);
l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__4);
l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5 = _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__5);
l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6 = _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTryConfig___lambda__1___closed__6);
l_Lean_Elab_Tactic_elabTryConfig___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTryConfig___lambda__2___closed__1);
l_Lean_Elab_Tactic_elabTryConfig___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTryConfig___lambda__2___closed__2);
l_Lean_Elab_Tactic_elabTryConfig___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTryConfig___lambda__3___closed__1);
l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__1);
l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__2);
l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__3 = _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__3);
l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__4 = _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__4);
l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__5 = _init_l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTryConfig___lambda__4___closed__5);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__5 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isExprAccessible___closed__5);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__1);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__2);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__3 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__3);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__4);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__5);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__6 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__6);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__7);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__8 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__8);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__9);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__10 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__10);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__11);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__12 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__12);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__13 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__13);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__14 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__14);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__15);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__16 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__16);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__17 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__17();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__17);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__4___closed__18);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__5___closed__1 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__5___closed__1);
l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__5___closed__2 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___lambda__5___closed__2);
l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__1 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__1);
l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__2 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__2);
l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__3 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__3);
l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__4 = _init_l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalSuggestExact___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getSuggestionOfTactic___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTrySuggestions___closed__4);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__1);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__2);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__3);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_filterSkipDone___spec__1___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_getTacSeqElems_x3f___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isCDotTac___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__5 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__5);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__6 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSeq___closed__6);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_isSorry___closed__2);
l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___spec__1___rarg___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__5 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__5);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__6 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__6);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__7 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___lambda__1___closed__7);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_grindTraceToGrind___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__1___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___lambda__2___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_simpTraceToSimp___closed__4);
l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__1 = _init_l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__1);
l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__2 = _init_l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__2);
l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__3 = _init_l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM___closed__3);
l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM = _init_l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_instMonadBacktrackSavedStateM);
l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__1___closed__1 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mergeAll_x3f___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___spec__2___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___lambda__2___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult_go___closed__1);
l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10___closed__1 = _init_l_Lean_addTrace___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__10___closed__1();
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12___closed__1);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__12___closed__2);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__1);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__2);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__3);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___spec__13___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__2___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__5 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__5);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__6 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__3___closed__6);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___lambda__4___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___boxed__const__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkChainResult___boxed__const__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestGrindTrace___lambda__2___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___lambda__3___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestSimpTrace___closed__1);
l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___closed__1 = _init_l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___closed__1);
l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___closed__2 = _init_l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___spec__1___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__2___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__3___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__3___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__3___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestChain___lambda__3___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestTacticSeq___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestFirst___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll_go___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestAttemptAll___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__2___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__5 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__5);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__6 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__6);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__7 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__7);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__8 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__8);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__9 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__9);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__10 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__10);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__11 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_evalSuggestImpl___lambda__3___closed__11);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toSuggestion___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__5 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__5);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__6 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__6);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__7 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__7);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__8 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__8);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__9 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__9);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__10 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_throwEvalAndSuggestFailed___rarg___closed__10);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_addSuggestions___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toIdent___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toIdent___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_toIdent___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFirstStx___spec__1___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__5 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_setGrindParams___closed__5);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__3);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__4 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__4);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__5 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__5);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__6 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__6);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__7 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__7();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__7);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__8 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__8();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__8);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__9 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__9();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__9);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__10 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__10();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindEqnParams___spec__1___closed__10);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__2___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___lambda__2___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkGrindStx___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__5 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__5);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__6 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__6);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__7 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__7);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__8 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__8);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__9 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__9);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__10 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__10);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__11 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__11);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__12 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpStx___closed__12);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__5 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__5);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__6 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkSimpleTacStx___closed__6);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkFunIndStx___lambda__1___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__1 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__1);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__2 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__2);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__3 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__3);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__4 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__4);
l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__5 = _init_l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Try_0__Lean_Elab_Tactic_Try_mkTryEvalSuggestStx___closed__5);
l_Lean_Elab_Tactic_Try_evalTryTrace___closed__1 = _init_l_Lean_Elab_Tactic_Try_evalTryTrace___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalTryTrace___closed__1);
l_Lean_Elab_Tactic_Try_evalTryTrace___closed__2 = _init_l_Lean_Elab_Tactic_Try_evalTryTrace___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Try_evalTryTrace___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_Try_evalTryTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
