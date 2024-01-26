// Lean compiler output
// Module: Lean.Compiler.LCNF.JoinPoints
// Imports: Init Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.PullFunDecls Lean.Compiler.LCNF.FVarUtil Lean.Compiler.LCNF.ScopeM Lean.Compiler.LCNF.InferType
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
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__9;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendState_fvarMap___default___spec__1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5041____closed__2;
LEAN_EXPORT uint8_t l_List_elem___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_pullFunDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ScopeM_clearScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__4;
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ScopeM_addToScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_FindState_candidates___default;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__16;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(lean_object*, lean_object*);
extern lean_object* l_Lean_instFVarIdSetInhabited;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__1(lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__2;
static lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__11___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__2(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__3___closed__1;
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5107_(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__22;
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__11;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__1(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__6___closed__1;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_hashset_mk_idx(lean_object*, uint64_t);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6___closed__1;
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__5;
lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_getType___spec__3(lean_object*, lean_object*);
lean_object* l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5107____closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendContext_candidates___default;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extendJoinPointContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__9(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendContext_currentJp_x3f___default;
static lean_object* l_Lean_Compiler_LCNF_findJoinPoints___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__6;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_mapCodeM___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6___closed__2;
static lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___closed__2;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__15;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__3(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__5;
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__1___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__17;
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5041____closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_findJoinPoints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__4;
static lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_FindState_scope___default___closed__1;
static lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__4;
static lean_object* l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__5;
static lean_object* l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__4;
lean_object* l_Lean_Compiler_LCNF_mkFreshJpName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendState_fvarMap___default;
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__19;
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__1;
static lean_object* l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_erase___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_instInhabitedCandidateInfo;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__7___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__21;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__7___closed__1;
lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
static lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__5;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_LCtx_addParam___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_commonJoinPointArgs;
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__1;
lean_object* l_Lean_Compiler_LCNF_ScopeM_getScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__8;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__1;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__6___closed__1;
uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_LCtx_addParam___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__3;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__1;
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__13;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_AnalysisCtx_jpScopes___default;
static lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointFinder_FindState_candidates___default___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_forCodeM___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ScopeM_isInScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___spec__2(lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__10(size_t, size_t, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__16;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_find_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__12(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__20;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5041_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__8;
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__24;
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__17;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_findJoinPoints___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_Compiler_LCNF_JoinPointFinder_instInhabitedCandidateInfo___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_findJoinPoints;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__7___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__14(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__1(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__2;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__14;
lean_object* l_Lean_Compiler_LCNF_ScopeM_setScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__14___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_mapCodeM___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__15;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_getArity___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_FindState_scope___default;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__14___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___spec__1(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_AnalysisState_jpJmpArgs___default;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_erase___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_commonJoinPointArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_findJoinPoints___closed__1;
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__1(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM;
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__1;
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__23;
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendState_fvarMap___default___spec__1___boxed(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__13;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__11;
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_mapCodeM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__7(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5107____closed__2;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__9___closed__1;
static lean_object* l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates(lean_object*);
lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__12;
static lean_object* l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normCodeImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__18;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__6(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__25;
static lean_object* l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__4;
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__3;
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__2(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__2;
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__2;
static lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__2;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonadOptionT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getParams(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__3(lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979_;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__2___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__3;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__14___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__4;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_findJoinPoints___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointFinder_FindState_candidates___default___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__10___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__3;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_replace___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_replace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMap_toArray___at_Lean_Compiler_LCNF_LCtx_toLocalContext___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_Compiler_LCNF_JoinPointFinder_instInhabitedCandidateInfo___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_findJoinPoints___closed__2;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__7;
static lean_object* l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__1;
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__1;
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_Compiler_LCNF_JoinPointFinder_instInhabitedCandidateInfo___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointFinder_instInhabitedCandidateInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSet___at_Lean_Compiler_LCNF_JoinPointFinder_instInhabitedCandidateInfo___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSet___at_Lean_Compiler_LCNF_JoinPointFinder_instInhabitedCandidateInfo___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointFinder_FindState_candidates___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointFinder_FindState_candidates___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointFinder_FindState_candidates___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointFinder_FindState_candidates___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointFinder_FindState_scope___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointFinder_FindState_scope___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_JoinPointFinder_FindState_scope___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_name_eq(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___spec__2(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___spec__1(x_13, x_1);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___spec__1(x_17, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_name_eq(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__3(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_AssocList_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__3(x_1, x_7);
lean_ctor_set(x_2, 2, x_9);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_AssocList_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__3(x_1, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
x_7 = lean_hashmap_mk_idx(x_5, x_6);
x_8 = lean_array_uget(x_4, x_7);
x_9 = l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__2(x_2, x_8);
if (x_9 == 0)
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
x_15 = l_Lean_AssocList_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__3(x_2, x_8);
x_16 = lean_array_uset(x_4, x_7, x_15);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_3, x_17);
lean_dec(x_3);
x_19 = l_Lean_AssocList_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__3(x_2, x_8);
x_20 = lean_array_uset(x_4, x_7, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_1 = x_13;
x_9 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_List_forM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__4(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
x_4 = x_16;
x_12 = x_17;
goto _start;
}
else
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_dec(x_2);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_st_ref_take(x_3, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = l_Lean_HashMapImp_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__1(x_24, x_1);
lean_dec(x_1);
lean_ctor_set(x_21, 0, x_25);
x_26 = lean_st_ref_set(x_3, x_21, x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_array_get_size(x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
lean_ctor_set(x_26, 0, x_35);
return x_26;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_32, x_32);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_box(0);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_26);
x_38 = 0;
x_39 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_40 = lean_box(0);
x_41 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__5(x_31, x_38, x_39, x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
lean_dec(x_31);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_dec(x_26);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_dec(x_19);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_array_get_size(x_44);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_lt(x_46, x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_45, x_45);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
return x_52;
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; 
x_53 = 0;
x_54 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_55 = lean_box(0);
x_56 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__5(x_44, x_53, x_54, x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
lean_dec(x_44);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_57 = lean_ctor_get(x_21, 0);
x_58 = lean_ctor_get(x_21, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_21);
x_59 = l_Lean_HashMapImp_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__1(x_57, x_1);
lean_dec(x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_st_ref_set(x_3, x_60, x_22);
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
x_64 = lean_ctor_get(x_19, 1);
lean_inc(x_64);
lean_dec(x_19);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_array_get_size(x_65);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_nat_dec_lt(x_67, x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_63;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_62);
return x_70;
}
else
{
uint8_t x_71; 
x_71 = lean_nat_dec_le(x_66, x_66);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_63;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_62);
return x_73;
}
else
{
size_t x_74; size_t x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_63);
x_74 = 0;
x_75 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_76 = lean_box(0);
x_77 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__5(x_65, x_74, x_75, x_76, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
lean_dec(x_65);
return x_77;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_HashMapImp_erase___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__5(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_apply_1(x_1, x_14);
lean_ctor_set(x_11, 0, x_15);
x_16 = lean_st_ref_set(x_3, x_11, x_12);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_apply_1(x_1, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_st_ref_set(x_3, x_26, x_12);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_instMonadCompilerM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__2;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__3;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__4;
x_11 = lean_panic_fn(x_10, x_1);
x_12 = lean_apply_8(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.FVarUtil", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Expr.forFVarM", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__1;
x_2 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__2;
x_3 = lean_unsigned_to_nat(42u);
x_4 = lean_unsigned_to_nat(38u);
x_5 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__4;
x_14 = l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
case 5:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_17 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_2 = x_16;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
case 6:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_26 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2(x_1, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_2 = x_25;
x_10 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
case 7:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 2);
lean_inc(x_34);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_35 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2(x_1, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_2 = x_34;
x_10 = x_36;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
case 8:
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__4;
x_43 = l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_43;
}
case 11:
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
lean_dec(x_1);
x_44 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__4;
x_45 = l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_45;
}
default: 
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_10);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
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
case 1:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_9(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___closed__1;
x_11 = l_Lean_Compiler_LCNF_Arg_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__1(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_3, x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_Lean_Compiler_LCNF_Arg_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__1(x_1, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_17;
x_13 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
else
{
lean_object* x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_13);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_3, x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_Lean_Compiler_LCNF_Arg_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__1(x_1, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_17;
x_13 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
else
{
lean_object* x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_13);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
case 3:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_14, x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_24 = lean_box(0);
x_25 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__2(x_1, x_13, x_22, x_23, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
return x_25;
}
}
}
case 4:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = lean_apply_9(x_1, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_array_get_size(x_27);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = lean_box(0);
lean_ctor_set(x_28, 0, x_35);
return x_28;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_32, x_32);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = lean_box(0);
lean_ctor_set(x_28, 0, x_37);
return x_28;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_28);
x_38 = 0;
x_39 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_40 = lean_box(0);
x_41 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__3(x_1, x_27, x_38, x_39, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_27);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_dec(x_28);
x_43 = lean_array_get_size(x_27);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_lt(x_44, x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_43, x_43);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_42);
return x_50;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_53 = lean_box(0);
x_54 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__3(x_1, x_27, x_51, x_52, x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_27);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_28);
if (x_55 == 0)
{
return x_28;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_28, 0);
x_57 = lean_ctor_get(x_28, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_28);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
default: 
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_10);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___closed__1;
x_11 = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__1(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__2(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_foldlMUnsafe_fold___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__3(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_4);
x_8 = lean_hashmap_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_12);
x_17 = lean_hashmap_mk_idx(x_15, x_16);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__4(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashMapImp_moveEntries___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__3(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__5(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__5(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
lean_inc(x_7);
x_9 = lean_hashmap_mk_idx(x_7, x_8);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_17 = lean_nat_dec_le(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashMapImp_expand___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__2(x_13, x_15);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__5(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
lean_inc(x_23);
x_25 = lean_hashmap_mk_idx(x_23, x_24);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_Lean_AssocList_contains___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate___spec__2(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_22, x_25, x_30);
x_32 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_29);
x_33 = lean_nat_dec_le(x_32, x_23);
lean_dec(x_23);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_HashMapImp_expand___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__2(x_29, x_31);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Lean_AssocList_replace___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__5(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__1(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Compiler_LCNF_JoinPointFinder_FindState_scope___default___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___lambda__1), 3, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_name_eq(x_1, x_4);
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
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_4);
x_8 = lean_hashset_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 1, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = lean_array_get_size(x_1);
x_15 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_12);
x_16 = lean_hashset_mk_idx(x_14, x_15);
x_17 = lean_array_uget(x_1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_uset(x_1, x_16, x_18);
x_1 = x_19;
x_2 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_List_foldl___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__5(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashSetImp_moveEntries___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_replace___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_name_eq(x_6, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_List_replace___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__6(x_7, x_2, x_3);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_name_eq(x_10, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_List_replace___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__6(x_11, x_2, x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
lean_inc(x_6);
x_8 = lean_hashset_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_5, x_8);
x_10 = l_List_elem___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__2(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_array_uset(x_5, x_8, x_13);
x_15 = lean_nat_dec_le(x_12, x_6);
lean_dec(x_6);
if (x_15 == 0)
{
lean_object* x_16; 
lean_free_object(x_1);
x_16 = l_Lean_HashSetImp_expand___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__3(x_12, x_14);
return x_16;
}
else
{
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_inc(x_2);
x_17 = l_List_replace___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__6(x_9, x_2, x_2);
lean_dec(x_2);
x_18 = lean_array_uset(x_5, x_8, x_17);
lean_ctor_set(x_1, 1, x_18);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_20);
x_22 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
lean_inc(x_21);
x_23 = lean_hashset_mk_idx(x_21, x_22);
x_24 = lean_array_uget(x_20, x_23);
x_25 = l_List_elem___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__2(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_19, x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_array_uset(x_20, x_23, x_28);
x_30 = lean_nat_dec_le(x_27, x_21);
lean_dec(x_21);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_HashSetImp_expand___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__3(x_27, x_29);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
lean_inc(x_2);
x_33 = l_List_replace___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__6(x_24, x_2, x_2);
lean_dec(x_2);
x_34 = lean_array_uset(x_20, x_23, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_HashSetImp_insert___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__1(x_6, x_2);
lean_ctor_set(x_1, 1, x_7);
x_8 = l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__1(x_4, x_3, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_HashSetImp_insert___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__1(x_10, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_HashMap_insert___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate___spec__1(x_4, x_3, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_11 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___lambda__1), 4, 3);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_2);
x_18 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_modifyCandidates(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
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
}
LEAN_EXPORT lean_object* l_List_elem___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_replace___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_replace___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency___spec__6(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_2);
x_15 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Compiler_LCNF_Arg_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__1(x_15, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_4 = x_17;
x_12 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_11 = lean_apply_8(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_9(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
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
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__3___rarg), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Compiler_LCNF_ScopeM_getScope(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ScopeM_clearScope(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_8(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__2___boxed), 10, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___closed__1;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__3___rarg), 10, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__4(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_forCodeM___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_9(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_apply_9(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointFinder_find_go), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_2);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__6___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Compiler_LCNF_AltCore_forCodeM___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__5(x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_4 = x_17;
x_12 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_find_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 5)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_inc(x_14);
x_19 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_19, 1);
x_25 = lean_ctor_get(x_19, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_ctor_get(x_11, 0);
lean_inc(x_27);
lean_dec(x_11);
x_28 = lean_name_eq(x_13, x_27);
lean_dec(x_27);
lean_dec(x_13);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_26);
lean_free_object(x_19);
lean_dec(x_16);
x_29 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_nat_dec_eq(x_16, x_30);
lean_dec(x_30);
lean_dec(x_16);
if (x_31 == 0)
{
lean_object* x_32; 
lean_free_object(x_19);
x_32 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_32;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_33; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_box(0);
lean_ctor_set(x_19, 0, x_33);
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_free_object(x_19);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = l_Lean_Compiler_LCNF_ScopeM_isInScope(x_14, x_4, x_5, x_6, x_7, x_8, x_24);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency(x_14, x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_34);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_35, 0, x_42);
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_dec(x_35);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_dec(x_19);
x_47 = lean_ctor_get(x_20, 0);
lean_inc(x_47);
lean_dec(x_20);
x_48 = lean_ctor_get(x_11, 0);
lean_inc(x_48);
lean_dec(x_11);
x_49 = lean_name_eq(x_13, x_48);
lean_dec(x_48);
lean_dec(x_13);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_47);
lean_dec(x_16);
x_50 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_nat_dec_eq(x_16, x_51);
lean_dec(x_51);
lean_dec(x_16);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
return x_53;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_46);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
x_57 = l_Lean_Compiler_LCNF_ScopeM_isInScope(x_14, x_4, x_5, x_6, x_7, x_8, x_46);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency(x_14, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_56);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_63 = x_57;
} else {
 lean_dec_ref(x_57);
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
}
}
}
}
else
{
uint8_t x_66; 
x_66 = lean_nat_dec_le(x_16, x_16);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_15);
lean_inc(x_14);
x_67 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
return x_70;
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_67);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_67, 1);
x_73 = lean_ctor_get(x_67, 0);
lean_dec(x_73);
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
lean_dec(x_68);
x_75 = lean_ctor_get(x_11, 0);
lean_inc(x_75);
lean_dec(x_11);
x_76 = lean_name_eq(x_13, x_75);
lean_dec(x_75);
lean_dec(x_13);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_74);
lean_free_object(x_67);
lean_dec(x_16);
x_77 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_72);
return x_77;
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_74, 0);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_nat_dec_eq(x_16, x_78);
lean_dec(x_78);
lean_dec(x_16);
if (x_79 == 0)
{
lean_object* x_80; 
lean_free_object(x_67);
x_80 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_72);
return x_80;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_81; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = lean_box(0);
lean_ctor_set(x_67, 0, x_81);
return x_67;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_free_object(x_67);
x_82 = lean_ctor_get(x_2, 0);
lean_inc(x_82);
x_83 = l_Lean_Compiler_LCNF_ScopeM_isInScope(x_14, x_4, x_5, x_6, x_7, x_8, x_72);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency(x_14, x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_86);
return x_87;
}
else
{
uint8_t x_88; 
lean_dec(x_82);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_83);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_83, 0);
lean_dec(x_89);
x_90 = lean_box(0);
lean_ctor_set(x_83, 0, x_90);
return x_83;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
lean_dec(x_83);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = lean_ctor_get(x_67, 1);
lean_inc(x_94);
lean_dec(x_67);
x_95 = lean_ctor_get(x_68, 0);
lean_inc(x_95);
lean_dec(x_68);
x_96 = lean_ctor_get(x_11, 0);
lean_inc(x_96);
lean_dec(x_11);
x_97 = lean_name_eq(x_13, x_96);
lean_dec(x_96);
lean_dec(x_13);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_95);
lean_dec(x_16);
x_98 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_94);
return x_98;
}
else
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_95, 0);
lean_inc(x_99);
lean_dec(x_95);
x_100 = lean_nat_dec_eq(x_16, x_99);
lean_dec(x_99);
lean_dec(x_16);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_94);
return x_101;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_94);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_ctor_get(x_2, 0);
lean_inc(x_104);
x_105 = l_Lean_Compiler_LCNF_ScopeM_isInScope(x_14, x_4, x_5, x_6, x_7, x_8, x_94);
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
x_109 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency(x_14, x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_108);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_104);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_111 = x_105;
} else {
 lean_dec_ref(x_105);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
}
}
}
}
}
}
else
{
size_t x_114; size_t x_115; lean_object* x_116; lean_object* x_117; 
x_114 = 0;
x_115 = lean_usize_of_nat(x_16);
x_116 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_117 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__1(x_15, x_114, x_115, x_116, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_15);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
lean_inc(x_14);
x_119 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_findCandidate_x3f(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_121);
return x_122;
}
else
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_119);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_124 = lean_ctor_get(x_119, 1);
x_125 = lean_ctor_get(x_119, 0);
lean_dec(x_125);
x_126 = lean_ctor_get(x_120, 0);
lean_inc(x_126);
lean_dec(x_120);
x_127 = lean_ctor_get(x_11, 0);
lean_inc(x_127);
lean_dec(x_11);
x_128 = lean_name_eq(x_13, x_127);
lean_dec(x_127);
lean_dec(x_13);
if (x_128 == 0)
{
lean_object* x_129; 
lean_dec(x_126);
lean_free_object(x_119);
lean_dec(x_16);
x_129 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_124);
return x_129;
}
else
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_126, 0);
lean_inc(x_130);
lean_dec(x_126);
x_131 = lean_nat_dec_eq(x_16, x_130);
lean_dec(x_130);
lean_dec(x_16);
if (x_131 == 0)
{
lean_object* x_132; 
lean_free_object(x_119);
x_132 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_124);
return x_132;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_119, 0, x_116);
return x_119;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_free_object(x_119);
x_133 = lean_ctor_get(x_2, 0);
lean_inc(x_133);
x_134 = l_Lean_Compiler_LCNF_ScopeM_isInScope(x_14, x_4, x_5, x_6, x_7, x_8, x_124);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency(x_14, x_133, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_137);
return x_138;
}
else
{
uint8_t x_139; 
lean_dec(x_133);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_139 = !lean_is_exclusive(x_134);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_134, 0);
lean_dec(x_140);
lean_ctor_set(x_134, 0, x_116);
return x_134;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_134, 1);
lean_inc(x_141);
lean_dec(x_134);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_116);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_143 = lean_ctor_get(x_119, 1);
lean_inc(x_143);
lean_dec(x_119);
x_144 = lean_ctor_get(x_120, 0);
lean_inc(x_144);
lean_dec(x_120);
x_145 = lean_ctor_get(x_11, 0);
lean_inc(x_145);
lean_dec(x_11);
x_146 = lean_name_eq(x_13, x_145);
lean_dec(x_145);
lean_dec(x_13);
if (x_146 == 0)
{
lean_object* x_147; 
lean_dec(x_144);
lean_dec(x_16);
x_147 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_143);
return x_147;
}
else
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_144, 0);
lean_inc(x_148);
lean_dec(x_144);
x_149 = lean_nat_dec_eq(x_16, x_148);
lean_dec(x_148);
lean_dec(x_16);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_143);
return x_150;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_151; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_116);
lean_ctor_set(x_151, 1, x_143);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_152 = lean_ctor_get(x_2, 0);
lean_inc(x_152);
x_153 = l_Lean_Compiler_LCNF_ScopeM_isInScope(x_14, x_4, x_5, x_6, x_7, x_8, x_143);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_unbox(x_154);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
x_157 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addDependency(x_14, x_152, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_156);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_152);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_158 = lean_ctor_get(x_153, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_159 = x_153;
} else {
 lean_dec_ref(x_153);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_116);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
}
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_161 = !lean_is_exclusive(x_117);
if (x_161 == 0)
{
return x_117;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_117, 0);
x_163 = lean_ctor_get(x_117, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_117);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_11);
x_165 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_166 = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__1(x_165, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_1 = x_10;
x_9 = x_167;
goto _start;
}
else
{
uint8_t x_169; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_169 = !lean_is_exclusive(x_166);
if (x_169 == 0)
{
return x_166;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_166, 0);
x_171 = lean_ctor_get(x_166, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_166);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_1, 0);
lean_inc(x_173);
lean_dec(x_1);
x_174 = lean_ctor_get(x_173, 3);
lean_inc(x_174);
lean_dec(x_173);
x_175 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_176 = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInLetValue___spec__1(x_175, x_174, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_1 = x_10;
x_9 = x_177;
goto _start;
}
else
{
uint8_t x_179; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_179 = !lean_is_exclusive(x_176);
if (x_179 == 0)
{
return x_176;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_176, 0);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_176);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
}
case 1:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_183 = lean_ctor_get(x_1, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_1, 1);
lean_inc(x_184);
lean_dec(x_1);
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 4);
lean_inc(x_186);
x_187 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointFinder_find_go), 9, 1);
lean_closure_set(x_187, 0, x_186);
lean_inc(x_185);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_185);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_189 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2(x_187, x_188, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_191 = l_Lean_Compiler_LCNF_FunDeclCore_getArity___rarg(x_183);
lean_dec(x_183);
lean_inc(x_185);
x_192 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_addCandidate(x_185, x_191, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_190);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_194 = l_Lean_Compiler_LCNF_ScopeM_addToScope(x_185, x_4, x_5, x_6, x_7, x_8, x_193);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_1 = x_184;
x_9 = x_195;
goto _start;
}
else
{
uint8_t x_197; 
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_197 = !lean_is_exclusive(x_189);
if (x_197 == 0)
{
return x_189;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_189, 0);
x_199 = lean_ctor_get(x_189, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_189);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
case 2:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_1, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_1, 1);
lean_inc(x_202);
lean_dec(x_1);
x_203 = lean_ctor_get(x_201, 4);
lean_inc(x_203);
lean_dec(x_201);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_204 = l_Lean_Compiler_LCNF_JoinPointFinder_find_go(x_203, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
x_1 = x_202;
x_9 = x_205;
goto _start;
}
else
{
uint8_t x_207; 
lean_dec(x_202);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_207 = !lean_is_exclusive(x_204);
if (x_207 == 0)
{
return x_204;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_204, 0);
x_209 = lean_ctor_get(x_204, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_204);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
case 3:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_211 = lean_ctor_get(x_1, 1);
lean_inc(x_211);
lean_dec(x_1);
x_212 = lean_array_get_size(x_211);
x_213 = lean_unsigned_to_nat(0u);
x_214 = lean_nat_dec_lt(x_213, x_212);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_215 = lean_box(0);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_9);
return x_216;
}
else
{
uint8_t x_217; 
x_217 = lean_nat_dec_le(x_212, x_212);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_218 = lean_box(0);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_9);
return x_219;
}
else
{
size_t x_220; size_t x_221; lean_object* x_222; lean_object* x_223; 
x_220 = 0;
x_221 = lean_usize_of_nat(x_212);
lean_dec(x_212);
x_222 = lean_box(0);
x_223 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__1(x_211, x_220, x_221, x_222, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_211);
return x_223;
}
}
}
case 4:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_224 = lean_ctor_get(x_1, 0);
lean_inc(x_224);
lean_dec(x_1);
x_225 = lean_ctor_get(x_224, 2);
lean_inc(x_225);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_226 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_225, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_227 = !lean_is_exclusive(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_228 = lean_ctor_get(x_226, 1);
x_229 = lean_ctor_get(x_226, 0);
lean_dec(x_229);
x_230 = lean_ctor_get(x_224, 3);
lean_inc(x_230);
lean_dec(x_224);
x_231 = lean_array_get_size(x_230);
x_232 = lean_unsigned_to_nat(0u);
x_233 = lean_nat_dec_lt(x_232, x_231);
if (x_233 == 0)
{
lean_object* x_234; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_234 = lean_box(0);
lean_ctor_set(x_226, 0, x_234);
return x_226;
}
else
{
uint8_t x_235; 
x_235 = lean_nat_dec_le(x_231, x_231);
if (x_235 == 0)
{
lean_object* x_236; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_236 = lean_box(0);
lean_ctor_set(x_226, 0, x_236);
return x_226;
}
else
{
size_t x_237; size_t x_238; lean_object* x_239; lean_object* x_240; 
lean_free_object(x_226);
x_237 = 0;
x_238 = lean_usize_of_nat(x_231);
lean_dec(x_231);
x_239 = lean_box(0);
x_240 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__6(x_230, x_237, x_238, x_239, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_228);
lean_dec(x_230);
return x_240;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_241 = lean_ctor_get(x_226, 1);
lean_inc(x_241);
lean_dec(x_226);
x_242 = lean_ctor_get(x_224, 3);
lean_inc(x_242);
lean_dec(x_224);
x_243 = lean_array_get_size(x_242);
x_244 = lean_unsigned_to_nat(0u);
x_245 = lean_nat_dec_lt(x_244, x_243);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_246 = lean_box(0);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_241);
return x_247;
}
else
{
uint8_t x_248; 
x_248 = lean_nat_dec_le(x_243, x_243);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_243);
lean_dec(x_242);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_249 = lean_box(0);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_241);
return x_250;
}
else
{
size_t x_251; size_t x_252; lean_object* x_253; lean_object* x_254; 
x_251 = 0;
x_252 = lean_usize_of_nat(x_243);
lean_dec(x_243);
x_253 = lean_box(0);
x_254 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__6(x_242, x_251, x_252, x_253, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_241);
lean_dec(x_242);
return x_254;
}
}
}
}
case 5:
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_1, 0);
lean_inc(x_255);
lean_dec(x_1);
x_256 = l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_eraseCandidate(x_255, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_256;
}
default: 
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_257 = lean_box(0);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_9);
return x_258;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__6(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__1;
x_2 = l_Lean_Compiler_LCNF_JoinPointFinder_FindState_scope___default___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_find(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = lean_st_mk_ref(x_9, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__2;
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_15);
x_17 = l_Lean_Compiler_LCNF_JoinPointFinder_find_go(x_7, x_8, x_15, x_11, x_2, x_3, x_4, x_5, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_15, x_18);
lean_dec(x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_11, x_21);
lean_dec(x_11);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_11);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_name_eq(x_4, x_1);
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
LEAN_EXPORT uint8_t l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__2(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_name_eq(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__4(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_mapCodeM___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Compiler_LCNF_AltCore_getCode(x_1);
x_10 = lean_apply_7(x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_12);
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
x_16 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointFinder_replace_go), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__6(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__6___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Compiler_LCNF_AltCore_mapCodeM___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__5(x_12, x_15, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_14, x_2, x_17);
x_2 = x_20;
x_3 = x_21;
x_9 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ptr_addr(x_8);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_8, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_8, 0);
lean_dec(x_16);
x_17 = lean_ptr_addr(x_12);
x_18 = lean_usize_dec_eq(x_13, x_17);
if (x_18 == 0)
{
lean_dec(x_1);
lean_ctor_set(x_8, 1, x_12);
lean_ctor_set(x_8, 0, x_9);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
size_t x_19; uint8_t x_20; 
x_19 = lean_ptr_addr(x_9);
x_20 = lean_usize_dec_eq(x_19, x_19);
if (x_20 == 0)
{
lean_dec(x_1);
lean_ctor_set(x_8, 1, x_12);
lean_ctor_set(x_8, 0, x_9);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_free_object(x_8);
lean_dec(x_12);
lean_dec(x_9);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
}
}
else
{
size_t x_21; uint8_t x_22; 
lean_dec(x_8);
x_21 = lean_ptr_addr(x_12);
x_22 = lean_usize_dec_eq(x_13, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_12);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
else
{
size_t x_24; uint8_t x_25; 
x_24 = lean_ptr_addr(x_9);
x_25 = lean_usize_dec_eq(x_24, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_12);
lean_ctor_set(x_10, 0, x_26);
return x_10;
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; size_t x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_ptr_addr(x_8);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_30 = x_8;
} else {
 lean_dec_ref(x_8);
 x_30 = lean_box(0);
}
x_31 = lean_ptr_addr(x_27);
x_32 = lean_usize_dec_eq(x_29, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
if (lean_is_scalar(x_30)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_30;
}
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
else
{
size_t x_35; uint8_t x_36; 
x_35 = lean_ptr_addr(x_9);
x_36 = lean_usize_dec_eq(x_35, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
if (lean_is_scalar(x_30)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_30;
}
lean_ctor_set(x_37, 0, x_9);
lean_ctor_set(x_37, 1, x_27);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_28);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_9);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_28);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
case 4:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_inc(x_8);
x_45 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; size_t x_48; size_t x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_49 = lean_ptr_addr(x_47);
x_50 = lean_usize_dec_eq(x_48, x_49);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_1);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_1, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_1, 0);
lean_dec(x_53);
lean_ctor_set(x_1, 1, x_47);
lean_ctor_set(x_45, 0, x_1);
return x_45;
}
else
{
lean_object* x_54; 
lean_dec(x_1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_47);
lean_ctor_set(x_45, 0, x_54);
return x_45;
}
}
else
{
size_t x_55; uint8_t x_56; 
x_55 = lean_ptr_addr(x_44);
x_56 = lean_usize_dec_eq(x_55, x_55);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_1);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_1, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_1, 0);
lean_dec(x_59);
lean_ctor_set(x_1, 1, x_47);
lean_ctor_set(x_45, 0, x_1);
return x_45;
}
else
{
lean_object* x_60; 
lean_dec(x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_47);
lean_ctor_set(x_45, 0, x_60);
return x_45;
}
}
else
{
lean_dec(x_47);
lean_dec(x_44);
lean_ctor_set(x_45, 0, x_1);
return x_45;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; size_t x_63; size_t x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_45, 0);
x_62 = lean_ctor_get(x_45, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_45);
x_63 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_64 = lean_ptr_addr(x_61);
x_65 = lean_usize_dec_eq(x_63, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_66 = x_1;
} else {
 lean_dec_ref(x_1);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_44);
lean_ctor_set(x_67, 1, x_61);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
return x_68;
}
else
{
size_t x_69; uint8_t x_70; 
x_69 = lean_ptr_addr(x_44);
x_70 = lean_usize_dec_eq(x_69, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_71 = x_1;
} else {
 lean_dec_ref(x_1);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_44);
lean_ctor_set(x_72, 1, x_61);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_62);
return x_73;
}
else
{
lean_object* x_74; 
lean_dec(x_61);
lean_dec(x_44);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_62);
return x_74;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_44);
lean_dec(x_8);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_45);
if (x_75 == 0)
{
return x_45;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_45, 0);
x_77 = lean_ctor_get(x_45, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_45);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
case 5:
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_1, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 3);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 4)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_81 = lean_ctor_get(x_8, 0);
lean_inc(x_81);
lean_dec(x_8);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
x_85 = lean_name_eq(x_81, x_84);
lean_dec(x_84);
lean_dec(x_81);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_7);
return x_86;
}
else
{
uint8_t x_87; 
lean_inc(x_82);
x_87 = l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__1(x_2, x_82);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_7);
return x_88;
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_1);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_1, 1);
lean_dec(x_90);
x_91 = lean_ctor_get(x_1, 0);
lean_dec(x_91);
x_92 = l_Lean_Compiler_LCNF_eraseLetDecl(x_79, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_79);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 1, x_83);
lean_ctor_set(x_1, 0, x_82);
lean_ctor_set(x_92, 0, x_1);
return x_92;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 1, x_83);
lean_ctor_set(x_1, 0, x_82);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_1);
x_97 = l_Lean_Compiler_LCNF_eraseLetDecl(x_79, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_79);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_100, 0, x_82);
lean_ctor_set(x_100, 1, x_83);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
}
}
}
else
{
lean_object* x_102; 
lean_dec(x_80);
lean_inc(x_8);
x_102 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; size_t x_105; size_t x_106; uint8_t x_107; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_106 = lean_ptr_addr(x_104);
x_107 = lean_usize_dec_eq(x_105, x_106);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_1);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_1, 1);
lean_dec(x_109);
x_110 = lean_ctor_get(x_1, 0);
lean_dec(x_110);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_102, 0, x_1);
return x_102;
}
else
{
lean_object* x_111; 
lean_dec(x_1);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_79);
lean_ctor_set(x_111, 1, x_104);
lean_ctor_set(x_102, 0, x_111);
return x_102;
}
}
else
{
size_t x_112; uint8_t x_113; 
x_112 = lean_ptr_addr(x_79);
x_113 = lean_usize_dec_eq(x_112, x_112);
if (x_113 == 0)
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_1);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_1, 1);
lean_dec(x_115);
x_116 = lean_ctor_get(x_1, 0);
lean_dec(x_116);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_102, 0, x_1);
return x_102;
}
else
{
lean_object* x_117; 
lean_dec(x_1);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_79);
lean_ctor_set(x_117, 1, x_104);
lean_ctor_set(x_102, 0, x_117);
return x_102;
}
}
else
{
lean_dec(x_104);
lean_dec(x_79);
lean_ctor_set(x_102, 0, x_1);
return x_102;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; size_t x_120; size_t x_121; uint8_t x_122; 
x_118 = lean_ctor_get(x_102, 0);
x_119 = lean_ctor_get(x_102, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_102);
x_120 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_121 = lean_ptr_addr(x_118);
x_122 = lean_usize_dec_eq(x_120, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_123 = x_1;
} else {
 lean_dec_ref(x_1);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_79);
lean_ctor_set(x_124, 1, x_118);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_119);
return x_125;
}
else
{
size_t x_126; uint8_t x_127; 
x_126 = lean_ptr_addr(x_79);
x_127 = lean_usize_dec_eq(x_126, x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_128 = x_1;
} else {
 lean_dec_ref(x_1);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_79);
lean_ctor_set(x_129, 1, x_118);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_119);
return x_130;
}
else
{
lean_object* x_131; 
lean_dec(x_118);
lean_dec(x_79);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_1);
lean_ctor_set(x_131, 1, x_119);
return x_131;
}
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_79);
lean_dec(x_8);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_102);
if (x_132 == 0)
{
return x_102;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_102, 0);
x_134 = lean_ctor_get(x_102, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_102);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
case 6:
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_1, 0);
lean_inc(x_136);
lean_inc(x_8);
x_137 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_137) == 0)
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; size_t x_140; size_t x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_141 = lean_ptr_addr(x_139);
x_142 = lean_usize_dec_eq(x_140, x_141);
if (x_142 == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_1);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_1, 1);
lean_dec(x_144);
x_145 = lean_ctor_get(x_1, 0);
lean_dec(x_145);
lean_ctor_set(x_1, 1, x_139);
lean_ctor_set(x_137, 0, x_1);
return x_137;
}
else
{
lean_object* x_146; 
lean_dec(x_1);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_136);
lean_ctor_set(x_146, 1, x_139);
lean_ctor_set(x_137, 0, x_146);
return x_137;
}
}
else
{
size_t x_147; uint8_t x_148; 
x_147 = lean_ptr_addr(x_136);
x_148 = lean_usize_dec_eq(x_147, x_147);
if (x_148 == 0)
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_1);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_1, 1);
lean_dec(x_150);
x_151 = lean_ctor_get(x_1, 0);
lean_dec(x_151);
lean_ctor_set(x_1, 1, x_139);
lean_ctor_set(x_137, 0, x_1);
return x_137;
}
else
{
lean_object* x_152; 
lean_dec(x_1);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_136);
lean_ctor_set(x_152, 1, x_139);
lean_ctor_set(x_137, 0, x_152);
return x_137;
}
}
else
{
lean_dec(x_139);
lean_dec(x_136);
lean_ctor_set(x_137, 0, x_1);
return x_137;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; size_t x_155; size_t x_156; uint8_t x_157; 
x_153 = lean_ctor_get(x_137, 0);
x_154 = lean_ctor_get(x_137, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_137);
x_155 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_156 = lean_ptr_addr(x_153);
x_157 = lean_usize_dec_eq(x_155, x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_158 = x_1;
} else {
 lean_dec_ref(x_1);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_136);
lean_ctor_set(x_159, 1, x_153);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_154);
return x_160;
}
else
{
size_t x_161; uint8_t x_162; 
x_161 = lean_ptr_addr(x_136);
x_162 = lean_usize_dec_eq(x_161, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_163 = x_1;
} else {
 lean_dec_ref(x_1);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_136);
lean_ctor_set(x_164, 1, x_153);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_154);
return x_165;
}
else
{
lean_object* x_166; 
lean_dec(x_153);
lean_dec(x_136);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_1);
lean_ctor_set(x_166, 1, x_154);
return x_166;
}
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_136);
lean_dec(x_8);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_137);
if (x_167 == 0)
{
return x_137;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_137, 0);
x_169 = lean_ctor_get(x_137, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_137);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
default: 
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_1, 0);
lean_inc(x_171);
lean_inc(x_8);
x_172 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_172) == 0)
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; size_t x_175; uint8_t x_176; 
x_174 = lean_ctor_get(x_172, 0);
x_175 = lean_ptr_addr(x_8);
x_176 = !lean_is_exclusive(x_8);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; size_t x_179; uint8_t x_180; 
x_177 = lean_ctor_get(x_8, 1);
lean_dec(x_177);
x_178 = lean_ctor_get(x_8, 0);
lean_dec(x_178);
x_179 = lean_ptr_addr(x_174);
x_180 = lean_usize_dec_eq(x_175, x_179);
if (x_180 == 0)
{
lean_dec(x_1);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 1, x_174);
lean_ctor_set(x_8, 0, x_171);
lean_ctor_set(x_172, 0, x_8);
return x_172;
}
else
{
size_t x_181; uint8_t x_182; 
x_181 = lean_ptr_addr(x_171);
x_182 = lean_usize_dec_eq(x_181, x_181);
if (x_182 == 0)
{
lean_dec(x_1);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 1, x_174);
lean_ctor_set(x_8, 0, x_171);
lean_ctor_set(x_172, 0, x_8);
return x_172;
}
else
{
lean_free_object(x_8);
lean_dec(x_174);
lean_dec(x_171);
lean_ctor_set(x_172, 0, x_1);
return x_172;
}
}
}
else
{
size_t x_183; uint8_t x_184; 
lean_dec(x_8);
x_183 = lean_ptr_addr(x_174);
x_184 = lean_usize_dec_eq(x_175, x_183);
if (x_184 == 0)
{
lean_object* x_185; 
lean_dec(x_1);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_171);
lean_ctor_set(x_185, 1, x_174);
lean_ctor_set(x_172, 0, x_185);
return x_172;
}
else
{
size_t x_186; uint8_t x_187; 
x_186 = lean_ptr_addr(x_171);
x_187 = lean_usize_dec_eq(x_186, x_186);
if (x_187 == 0)
{
lean_object* x_188; 
lean_dec(x_1);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_171);
lean_ctor_set(x_188, 1, x_174);
lean_ctor_set(x_172, 0, x_188);
return x_172;
}
else
{
lean_dec(x_174);
lean_dec(x_171);
lean_ctor_set(x_172, 0, x_1);
return x_172;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; size_t x_191; lean_object* x_192; size_t x_193; uint8_t x_194; 
x_189 = lean_ctor_get(x_172, 0);
x_190 = lean_ctor_get(x_172, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_172);
x_191 = lean_ptr_addr(x_8);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_192 = x_8;
} else {
 lean_dec_ref(x_8);
 x_192 = lean_box(0);
}
x_193 = lean_ptr_addr(x_189);
x_194 = lean_usize_dec_eq(x_191, x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_1);
if (lean_is_scalar(x_192)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_192;
 lean_ctor_set_tag(x_195, 0);
}
lean_ctor_set(x_195, 0, x_171);
lean_ctor_set(x_195, 1, x_189);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_190);
return x_196;
}
else
{
size_t x_197; uint8_t x_198; 
x_197 = lean_ptr_addr(x_171);
x_198 = lean_usize_dec_eq(x_197, x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_1);
if (lean_is_scalar(x_192)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_192;
 lean_ctor_set_tag(x_199, 0);
}
lean_ctor_set(x_199, 0, x_171);
lean_ctor_set(x_199, 1, x_189);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_190);
return x_200;
}
else
{
lean_object* x_201; 
lean_dec(x_192);
lean_dec(x_189);
lean_dec(x_171);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_1);
lean_ctor_set(x_201, 1, x_190);
return x_201;
}
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_171);
lean_dec(x_8);
lean_dec(x_1);
x_202 = !lean_is_exclusive(x_172);
if (x_202 == 0)
{
return x_172;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_172, 0);
x_204 = lean_ctor_get(x_172, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_172);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
}
}
case 1:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_206 = lean_ctor_get(x_1, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_1, 1);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_206, 2);
lean_inc(x_209);
x_210 = lean_ctor_get(x_206, 3);
lean_inc(x_210);
x_211 = lean_ctor_get(x_206, 4);
lean_inc(x_211);
lean_inc(x_208);
lean_inc(x_2);
x_212 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__3(x_2, x_208);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; 
lean_dec(x_208);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_213 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_211, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
lean_inc(x_206);
x_216 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_206, x_210, x_209, x_214, x_3, x_4, x_5, x_6, x_215);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
lean_inc(x_207);
x_219 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_207, x_2, x_3, x_4, x_5, x_6, x_218);
if (lean_obj_tag(x_219) == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
lean_object* x_221; size_t x_222; size_t x_223; uint8_t x_224; 
x_221 = lean_ctor_get(x_219, 0);
x_222 = lean_ptr_addr(x_207);
lean_dec(x_207);
x_223 = lean_ptr_addr(x_221);
x_224 = lean_usize_dec_eq(x_222, x_223);
if (x_224 == 0)
{
uint8_t x_225; 
lean_dec(x_206);
x_225 = !lean_is_exclusive(x_1);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_1, 1);
lean_dec(x_226);
x_227 = lean_ctor_get(x_1, 0);
lean_dec(x_227);
lean_ctor_set(x_1, 1, x_221);
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set(x_219, 0, x_1);
return x_219;
}
else
{
lean_object* x_228; 
lean_dec(x_1);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_217);
lean_ctor_set(x_228, 1, x_221);
lean_ctor_set(x_219, 0, x_228);
return x_219;
}
}
else
{
size_t x_229; size_t x_230; uint8_t x_231; 
x_229 = lean_ptr_addr(x_206);
lean_dec(x_206);
x_230 = lean_ptr_addr(x_217);
x_231 = lean_usize_dec_eq(x_229, x_230);
if (x_231 == 0)
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_1);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_1, 1);
lean_dec(x_233);
x_234 = lean_ctor_get(x_1, 0);
lean_dec(x_234);
lean_ctor_set(x_1, 1, x_221);
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set(x_219, 0, x_1);
return x_219;
}
else
{
lean_object* x_235; 
lean_dec(x_1);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_217);
lean_ctor_set(x_235, 1, x_221);
lean_ctor_set(x_219, 0, x_235);
return x_219;
}
}
else
{
lean_dec(x_221);
lean_dec(x_217);
lean_ctor_set(x_219, 0, x_1);
return x_219;
}
}
}
else
{
lean_object* x_236; lean_object* x_237; size_t x_238; size_t x_239; uint8_t x_240; 
x_236 = lean_ctor_get(x_219, 0);
x_237 = lean_ctor_get(x_219, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_219);
x_238 = lean_ptr_addr(x_207);
lean_dec(x_207);
x_239 = lean_ptr_addr(x_236);
x_240 = lean_usize_dec_eq(x_238, x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_206);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_241 = x_1;
} else {
 lean_dec_ref(x_1);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_217);
lean_ctor_set(x_242, 1, x_236);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_237);
return x_243;
}
else
{
size_t x_244; size_t x_245; uint8_t x_246; 
x_244 = lean_ptr_addr(x_206);
lean_dec(x_206);
x_245 = lean_ptr_addr(x_217);
x_246 = lean_usize_dec_eq(x_244, x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_247 = x_1;
} else {
 lean_dec_ref(x_1);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_217);
lean_ctor_set(x_248, 1, x_236);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_237);
return x_249;
}
else
{
lean_object* x_250; 
lean_dec(x_236);
lean_dec(x_217);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_1);
lean_ctor_set(x_250, 1, x_237);
return x_250;
}
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_217);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_1);
x_251 = !lean_is_exclusive(x_219);
if (x_251 == 0)
{
return x_219;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_219, 0);
x_253 = lean_ctor_get(x_219, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_219);
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
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_255 = !lean_is_exclusive(x_213);
if (x_255 == 0)
{
return x_213;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_213, 0);
x_257 = lean_ctor_get(x_213, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_213);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
else
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_1);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_260 = lean_ctor_get(x_1, 1);
lean_dec(x_260);
x_261 = lean_ctor_get(x_1, 0);
lean_dec(x_261);
x_262 = !lean_is_exclusive(x_206);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_263 = lean_ctor_get(x_206, 4);
lean_dec(x_263);
x_264 = lean_ctor_get(x_206, 3);
lean_dec(x_264);
x_265 = lean_ctor_get(x_206, 2);
lean_dec(x_265);
x_266 = lean_ctor_get(x_206, 1);
lean_dec(x_266);
x_267 = lean_ctor_get(x_206, 0);
lean_dec(x_267);
x_268 = lean_ctor_get(x_212, 0);
lean_inc(x_268);
lean_dec(x_212);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_269 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_211, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
lean_ctor_set(x_206, 4, x_270);
lean_ctor_set(x_206, 1, x_268);
x_272 = lean_st_ref_take(x_4, x_271);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
x_275 = !lean_is_exclusive(x_273);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_276 = lean_ctor_get(x_273, 0);
lean_inc(x_206);
x_277 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_276, x_206);
lean_ctor_set(x_273, 0, x_277);
x_278 = lean_st_ref_set(x_4, x_273, x_274);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
x_280 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_207, x_2, x_3, x_4, x_5, x_6, x_279);
if (lean_obj_tag(x_280) == 0)
{
uint8_t x_281; 
x_281 = !lean_is_exclusive(x_280);
if (x_281 == 0)
{
lean_object* x_282; 
x_282 = lean_ctor_get(x_280, 0);
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 1, x_282);
lean_ctor_set(x_280, 0, x_1);
return x_280;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_280, 0);
x_284 = lean_ctor_get(x_280, 1);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_280);
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 1, x_283);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_1);
lean_ctor_set(x_285, 1, x_284);
return x_285;
}
}
else
{
uint8_t x_286; 
lean_dec(x_206);
lean_free_object(x_1);
x_286 = !lean_is_exclusive(x_280);
if (x_286 == 0)
{
return x_280;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_280, 0);
x_288 = lean_ctor_get(x_280, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_280);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_290 = lean_ctor_get(x_273, 0);
x_291 = lean_ctor_get(x_273, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_273);
lean_inc(x_206);
x_292 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_290, x_206);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
x_294 = lean_st_ref_set(x_4, x_293, x_274);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_296 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_207, x_2, x_3, x_4, x_5, x_6, x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_299 = x_296;
} else {
 lean_dec_ref(x_296);
 x_299 = lean_box(0);
}
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 1, x_297);
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_1);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_206);
lean_free_object(x_1);
x_301 = lean_ctor_get(x_296, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_296, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_303 = x_296;
} else {
 lean_dec_ref(x_296);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_302);
return x_304;
}
}
}
else
{
uint8_t x_305; 
lean_dec(x_268);
lean_free_object(x_206);
lean_free_object(x_1);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_305 = !lean_is_exclusive(x_269);
if (x_305 == 0)
{
return x_269;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_269, 0);
x_307 = lean_ctor_get(x_269, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_269);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
else
{
lean_object* x_309; lean_object* x_310; 
lean_dec(x_206);
x_309 = lean_ctor_get(x_212, 0);
lean_inc(x_309);
lean_dec(x_212);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_310 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_211, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_313, 0, x_208);
lean_ctor_set(x_313, 1, x_309);
lean_ctor_set(x_313, 2, x_209);
lean_ctor_set(x_313, 3, x_210);
lean_ctor_set(x_313, 4, x_311);
x_314 = lean_st_ref_take(x_4, x_312);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = lean_ctor_get(x_315, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_315, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_319 = x_315;
} else {
 lean_dec_ref(x_315);
 x_319 = lean_box(0);
}
lean_inc(x_313);
x_320 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_317, x_313);
if (lean_is_scalar(x_319)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_319;
}
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_318);
x_322 = lean_st_ref_set(x_4, x_321, x_316);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
lean_dec(x_322);
x_324 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_207, x_2, x_3, x_4, x_5, x_6, x_323);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_327 = x_324;
} else {
 lean_dec_ref(x_324);
 x_327 = lean_box(0);
}
lean_ctor_set_tag(x_1, 2);
lean_ctor_set(x_1, 1, x_325);
lean_ctor_set(x_1, 0, x_313);
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_1);
lean_ctor_set(x_328, 1, x_326);
return x_328;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_313);
lean_free_object(x_1);
x_329 = lean_ctor_get(x_324, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_324, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_331 = x_324;
} else {
 lean_dec_ref(x_324);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(1, 2, 0);
} else {
 x_332 = x_331;
}
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_330);
return x_332;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_309);
lean_free_object(x_1);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_333 = lean_ctor_get(x_310, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_310, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_335 = x_310;
} else {
 lean_dec_ref(x_310);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_334);
return x_336;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_1);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 lean_ctor_release(x_206, 4);
 x_337 = x_206;
} else {
 lean_dec_ref(x_206);
 x_337 = lean_box(0);
}
x_338 = lean_ctor_get(x_212, 0);
lean_inc(x_338);
lean_dec(x_212);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_339 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_211, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
if (lean_is_scalar(x_337)) {
 x_342 = lean_alloc_ctor(0, 5, 0);
} else {
 x_342 = x_337;
}
lean_ctor_set(x_342, 0, x_208);
lean_ctor_set(x_342, 1, x_338);
lean_ctor_set(x_342, 2, x_209);
lean_ctor_set(x_342, 3, x_210);
lean_ctor_set(x_342, 4, x_340);
x_343 = lean_st_ref_take(x_4, x_341);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = lean_ctor_get(x_344, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_344, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_348 = x_344;
} else {
 lean_dec_ref(x_344);
 x_348 = lean_box(0);
}
lean_inc(x_342);
x_349 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_346, x_342);
if (lean_is_scalar(x_348)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_348;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_347);
x_351 = lean_st_ref_set(x_4, x_350, x_345);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec(x_351);
x_353 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_207, x_2, x_3, x_4, x_5, x_6, x_352);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_356 = x_353;
} else {
 lean_dec_ref(x_353);
 x_356 = lean_box(0);
}
x_357 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_357, 0, x_342);
lean_ctor_set(x_357, 1, x_354);
if (lean_is_scalar(x_356)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_356;
}
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_355);
return x_358;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_342);
x_359 = lean_ctor_get(x_353, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_353, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_361 = x_353;
} else {
 lean_dec_ref(x_353);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_360);
return x_362;
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_363 = lean_ctor_get(x_339, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_339, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 x_365 = x_339;
} else {
 lean_dec_ref(x_339);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_364);
return x_366;
}
}
}
}
case 2:
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_367 = lean_ctor_get(x_1, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_1, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 4);
lean_inc(x_369);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_370 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_369, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_373 = lean_ctor_get(x_367, 3);
lean_inc(x_373);
x_374 = lean_ctor_get(x_367, 2);
lean_inc(x_374);
lean_inc(x_367);
x_375 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_367, x_373, x_374, x_371, x_3, x_4, x_5, x_6, x_372);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
lean_inc(x_368);
x_378 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_368, x_2, x_3, x_4, x_5, x_6, x_377);
if (lean_obj_tag(x_378) == 0)
{
uint8_t x_379; 
x_379 = !lean_is_exclusive(x_378);
if (x_379 == 0)
{
lean_object* x_380; size_t x_381; size_t x_382; uint8_t x_383; 
x_380 = lean_ctor_get(x_378, 0);
x_381 = lean_ptr_addr(x_368);
lean_dec(x_368);
x_382 = lean_ptr_addr(x_380);
x_383 = lean_usize_dec_eq(x_381, x_382);
if (x_383 == 0)
{
uint8_t x_384; 
lean_dec(x_367);
x_384 = !lean_is_exclusive(x_1);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; 
x_385 = lean_ctor_get(x_1, 1);
lean_dec(x_385);
x_386 = lean_ctor_get(x_1, 0);
lean_dec(x_386);
lean_ctor_set(x_1, 1, x_380);
lean_ctor_set(x_1, 0, x_376);
lean_ctor_set(x_378, 0, x_1);
return x_378;
}
else
{
lean_object* x_387; 
lean_dec(x_1);
x_387 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_387, 0, x_376);
lean_ctor_set(x_387, 1, x_380);
lean_ctor_set(x_378, 0, x_387);
return x_378;
}
}
else
{
size_t x_388; size_t x_389; uint8_t x_390; 
x_388 = lean_ptr_addr(x_367);
lean_dec(x_367);
x_389 = lean_ptr_addr(x_376);
x_390 = lean_usize_dec_eq(x_388, x_389);
if (x_390 == 0)
{
uint8_t x_391; 
x_391 = !lean_is_exclusive(x_1);
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; 
x_392 = lean_ctor_get(x_1, 1);
lean_dec(x_392);
x_393 = lean_ctor_get(x_1, 0);
lean_dec(x_393);
lean_ctor_set(x_1, 1, x_380);
lean_ctor_set(x_1, 0, x_376);
lean_ctor_set(x_378, 0, x_1);
return x_378;
}
else
{
lean_object* x_394; 
lean_dec(x_1);
x_394 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_394, 0, x_376);
lean_ctor_set(x_394, 1, x_380);
lean_ctor_set(x_378, 0, x_394);
return x_378;
}
}
else
{
lean_dec(x_380);
lean_dec(x_376);
lean_ctor_set(x_378, 0, x_1);
return x_378;
}
}
}
else
{
lean_object* x_395; lean_object* x_396; size_t x_397; size_t x_398; uint8_t x_399; 
x_395 = lean_ctor_get(x_378, 0);
x_396 = lean_ctor_get(x_378, 1);
lean_inc(x_396);
lean_inc(x_395);
lean_dec(x_378);
x_397 = lean_ptr_addr(x_368);
lean_dec(x_368);
x_398 = lean_ptr_addr(x_395);
x_399 = lean_usize_dec_eq(x_397, x_398);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_367);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_400 = x_1;
} else {
 lean_dec_ref(x_1);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(2, 2, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_376);
lean_ctor_set(x_401, 1, x_395);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_396);
return x_402;
}
else
{
size_t x_403; size_t x_404; uint8_t x_405; 
x_403 = lean_ptr_addr(x_367);
lean_dec(x_367);
x_404 = lean_ptr_addr(x_376);
x_405 = lean_usize_dec_eq(x_403, x_404);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_406 = x_1;
} else {
 lean_dec_ref(x_1);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(2, 2, 0);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_376);
lean_ctor_set(x_407, 1, x_395);
x_408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_396);
return x_408;
}
else
{
lean_object* x_409; 
lean_dec(x_395);
lean_dec(x_376);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_1);
lean_ctor_set(x_409, 1, x_396);
return x_409;
}
}
}
}
else
{
uint8_t x_410; 
lean_dec(x_376);
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_1);
x_410 = !lean_is_exclusive(x_378);
if (x_410 == 0)
{
return x_378;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_378, 0);
x_412 = lean_ctor_get(x_378, 1);
lean_inc(x_412);
lean_inc(x_411);
lean_dec(x_378);
x_413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
return x_413;
}
}
}
else
{
uint8_t x_414; 
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_414 = !lean_is_exclusive(x_370);
if (x_414 == 0)
{
return x_370;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_370, 0);
x_416 = lean_ctor_get(x_370, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_370);
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
return x_417;
}
}
}
case 4:
{
lean_object* x_418; uint8_t x_419; 
x_418 = lean_ctor_get(x_1, 0);
lean_inc(x_418);
x_419 = !lean_is_exclusive(x_418);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; size_t x_425; size_t x_426; lean_object* x_427; 
x_420 = lean_ctor_get(x_418, 0);
x_421 = lean_ctor_get(x_418, 1);
x_422 = lean_ctor_get(x_418, 2);
x_423 = lean_ctor_get(x_418, 3);
x_424 = lean_array_get_size(x_423);
x_425 = lean_usize_of_nat(x_424);
lean_dec(x_424);
x_426 = 0;
lean_inc(x_423);
x_427 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__6(x_425, x_426, x_423, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_427) == 0)
{
uint8_t x_428; 
x_428 = !lean_is_exclusive(x_427);
if (x_428 == 0)
{
lean_object* x_429; size_t x_430; size_t x_431; uint8_t x_432; 
x_429 = lean_ctor_get(x_427, 0);
x_430 = lean_ptr_addr(x_423);
lean_dec(x_423);
x_431 = lean_ptr_addr(x_429);
x_432 = lean_usize_dec_eq(x_430, x_431);
if (x_432 == 0)
{
uint8_t x_433; 
x_433 = !lean_is_exclusive(x_1);
if (x_433 == 0)
{
lean_object* x_434; 
x_434 = lean_ctor_get(x_1, 0);
lean_dec(x_434);
lean_ctor_set(x_418, 3, x_429);
lean_ctor_set(x_427, 0, x_1);
return x_427;
}
else
{
lean_object* x_435; 
lean_dec(x_1);
lean_ctor_set(x_418, 3, x_429);
x_435 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_435, 0, x_418);
lean_ctor_set(x_427, 0, x_435);
return x_427;
}
}
else
{
size_t x_436; uint8_t x_437; 
x_436 = lean_ptr_addr(x_421);
x_437 = lean_usize_dec_eq(x_436, x_436);
if (x_437 == 0)
{
uint8_t x_438; 
x_438 = !lean_is_exclusive(x_1);
if (x_438 == 0)
{
lean_object* x_439; 
x_439 = lean_ctor_get(x_1, 0);
lean_dec(x_439);
lean_ctor_set(x_418, 3, x_429);
lean_ctor_set(x_427, 0, x_1);
return x_427;
}
else
{
lean_object* x_440; 
lean_dec(x_1);
lean_ctor_set(x_418, 3, x_429);
x_440 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_440, 0, x_418);
lean_ctor_set(x_427, 0, x_440);
return x_427;
}
}
else
{
uint8_t x_441; 
x_441 = lean_name_eq(x_422, x_422);
if (x_441 == 0)
{
uint8_t x_442; 
x_442 = !lean_is_exclusive(x_1);
if (x_442 == 0)
{
lean_object* x_443; 
x_443 = lean_ctor_get(x_1, 0);
lean_dec(x_443);
lean_ctor_set(x_418, 3, x_429);
lean_ctor_set(x_427, 0, x_1);
return x_427;
}
else
{
lean_object* x_444; 
lean_dec(x_1);
lean_ctor_set(x_418, 3, x_429);
x_444 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_444, 0, x_418);
lean_ctor_set(x_427, 0, x_444);
return x_427;
}
}
else
{
lean_dec(x_429);
lean_free_object(x_418);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_ctor_set(x_427, 0, x_1);
return x_427;
}
}
}
}
else
{
lean_object* x_445; lean_object* x_446; size_t x_447; size_t x_448; uint8_t x_449; 
x_445 = lean_ctor_get(x_427, 0);
x_446 = lean_ctor_get(x_427, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_427);
x_447 = lean_ptr_addr(x_423);
lean_dec(x_423);
x_448 = lean_ptr_addr(x_445);
x_449 = lean_usize_dec_eq(x_447, x_448);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_450 = x_1;
} else {
 lean_dec_ref(x_1);
 x_450 = lean_box(0);
}
lean_ctor_set(x_418, 3, x_445);
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(4, 1, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_418);
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_446);
return x_452;
}
else
{
size_t x_453; uint8_t x_454; 
x_453 = lean_ptr_addr(x_421);
x_454 = lean_usize_dec_eq(x_453, x_453);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_455 = x_1;
} else {
 lean_dec_ref(x_1);
 x_455 = lean_box(0);
}
lean_ctor_set(x_418, 3, x_445);
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(4, 1, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_418);
x_457 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set(x_457, 1, x_446);
return x_457;
}
else
{
uint8_t x_458; 
x_458 = lean_name_eq(x_422, x_422);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_459 = x_1;
} else {
 lean_dec_ref(x_1);
 x_459 = lean_box(0);
}
lean_ctor_set(x_418, 3, x_445);
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(4, 1, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_418);
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_446);
return x_461;
}
else
{
lean_object* x_462; 
lean_dec(x_445);
lean_free_object(x_418);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_420);
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_1);
lean_ctor_set(x_462, 1, x_446);
return x_462;
}
}
}
}
}
else
{
uint8_t x_463; 
lean_free_object(x_418);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_1);
x_463 = !lean_is_exclusive(x_427);
if (x_463 == 0)
{
return x_427;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_427, 0);
x_465 = lean_ctor_get(x_427, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_427);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; size_t x_472; size_t x_473; lean_object* x_474; 
x_467 = lean_ctor_get(x_418, 0);
x_468 = lean_ctor_get(x_418, 1);
x_469 = lean_ctor_get(x_418, 2);
x_470 = lean_ctor_get(x_418, 3);
lean_inc(x_470);
lean_inc(x_469);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_418);
x_471 = lean_array_get_size(x_470);
x_472 = lean_usize_of_nat(x_471);
lean_dec(x_471);
x_473 = 0;
lean_inc(x_470);
x_474 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__6(x_472, x_473, x_470, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; size_t x_478; size_t x_479; uint8_t x_480; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_477 = x_474;
} else {
 lean_dec_ref(x_474);
 x_477 = lean_box(0);
}
x_478 = lean_ptr_addr(x_470);
lean_dec(x_470);
x_479 = lean_ptr_addr(x_475);
x_480 = lean_usize_dec_eq(x_478, x_479);
if (x_480 == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_481 = x_1;
} else {
 lean_dec_ref(x_1);
 x_481 = lean_box(0);
}
x_482 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_482, 0, x_467);
lean_ctor_set(x_482, 1, x_468);
lean_ctor_set(x_482, 2, x_469);
lean_ctor_set(x_482, 3, x_475);
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(4, 1, 0);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_482);
if (lean_is_scalar(x_477)) {
 x_484 = lean_alloc_ctor(0, 2, 0);
} else {
 x_484 = x_477;
}
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_476);
return x_484;
}
else
{
size_t x_485; uint8_t x_486; 
x_485 = lean_ptr_addr(x_468);
x_486 = lean_usize_dec_eq(x_485, x_485);
if (x_486 == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_487 = x_1;
} else {
 lean_dec_ref(x_1);
 x_487 = lean_box(0);
}
x_488 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_488, 0, x_467);
lean_ctor_set(x_488, 1, x_468);
lean_ctor_set(x_488, 2, x_469);
lean_ctor_set(x_488, 3, x_475);
if (lean_is_scalar(x_487)) {
 x_489 = lean_alloc_ctor(4, 1, 0);
} else {
 x_489 = x_487;
}
lean_ctor_set(x_489, 0, x_488);
if (lean_is_scalar(x_477)) {
 x_490 = lean_alloc_ctor(0, 2, 0);
} else {
 x_490 = x_477;
}
lean_ctor_set(x_490, 0, x_489);
lean_ctor_set(x_490, 1, x_476);
return x_490;
}
else
{
uint8_t x_491; 
x_491 = lean_name_eq(x_469, x_469);
if (x_491 == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_492 = x_1;
} else {
 lean_dec_ref(x_1);
 x_492 = lean_box(0);
}
x_493 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_493, 0, x_467);
lean_ctor_set(x_493, 1, x_468);
lean_ctor_set(x_493, 2, x_469);
lean_ctor_set(x_493, 3, x_475);
if (lean_is_scalar(x_492)) {
 x_494 = lean_alloc_ctor(4, 1, 0);
} else {
 x_494 = x_492;
}
lean_ctor_set(x_494, 0, x_493);
if (lean_is_scalar(x_477)) {
 x_495 = lean_alloc_ctor(0, 2, 0);
} else {
 x_495 = x_477;
}
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_476);
return x_495;
}
else
{
lean_object* x_496; 
lean_dec(x_475);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_467);
if (lean_is_scalar(x_477)) {
 x_496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_496 = x_477;
}
lean_ctor_set(x_496, 0, x_1);
lean_ctor_set(x_496, 1, x_476);
return x_496;
}
}
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_1);
x_497 = lean_ctor_get(x_474, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_474, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_499 = x_474;
} else {
 lean_dec_ref(x_474);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_497);
lean_ctor_set(x_500, 1, x_498);
return x_500;
}
}
}
default: 
{
lean_object* x_501; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_501 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_501, 0, x_1);
lean_ctor_set(x_501, 1, x_7);
return x_501;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__6(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_4);
x_8 = lean_hashmap_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_12);
x_17 = lean_hashmap_mk_idx(x_15, x_16);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__4(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__3(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__5(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__5(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
lean_inc(x_7);
x_9 = lean_hashmap_mk_idx(x_7, x_8);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_17 = lean_nat_dec_le(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__2(x_13, x_15);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__5(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
lean_inc(x_23);
x_25 = lean_hashmap_mk_idx(x_23, x_24);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__2(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_22, x_25, x_30);
x_32 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_29);
x_33 = lean_nat_dec_le(x_32, x_23);
lean_dec(x_23);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__2(x_29, x_31);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__5(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Compiler_LCNF_mkFreshJpName(x_3, x_4, x_5, x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__1(x_1, x_9, x_12);
x_1 = x_14;
x_2 = x_10;
x_7 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__7(x_4, x_11, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_13;
x_9 = x_14;
goto _start;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_replace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_46 = lean_unsigned_to_nat(8u);
x_47 = l_Lean_mkHashMapImp___rarg(x_46);
x_48 = lean_ctor_get(x_2, 0);
x_49 = lean_ctor_get(x_48, 1);
x_50 = lean_array_get_size(x_49);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_lt(x_51, x_50);
if (x_52 == 0)
{
lean_dec(x_50);
x_8 = x_47;
x_9 = x_7;
goto block_45;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_50, x_50);
if (x_53 == 0)
{
lean_dec(x_50);
x_8 = x_47;
x_9 = x_7;
goto block_45;
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = 0;
x_55 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_56 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__8(x_49, x_54, x_55, x_47, x_3, x_4, x_5, x_6, x_7);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_8 = x_57;
x_9 = x_58;
goto block_45;
}
}
block_45:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 4);
x_16 = lean_ctor_get(x_1, 5);
x_17 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_15, x_8, x_3, x_4, x_5, x_6, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_1, 4, x_19);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_1, 4, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_1);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_1, 2);
x_30 = lean_ctor_get(x_1, 3);
x_31 = lean_ctor_get(x_1, 4);
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_33 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_34 = lean_ctor_get(x_1, 5);
lean_inc(x_34);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_35 = l_Lean_Compiler_LCNF_JoinPointFinder_replace_go(x_31, x_8, x_3, x_4, x_5, x_6, x_9);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
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
x_39 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_28);
lean_ctor_set(x_39, 2, x_29);
lean_ctor_set(x_39, 3, x_30);
lean_ctor_set(x_39, 4, x_36);
lean_ctor_set(x_39, 5, x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*6, x_32);
lean_ctor_set_uint8(x_39, sizeof(void*)*6 + 1, x_33);
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
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_43 = x_35;
} else {
 lean_dec_ref(x_35);
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
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__6(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_replace___spec__8(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointFinder_replace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_JoinPointFinder_replace(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendContext_currentJp_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendContext_candidates___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendState_fvarMap___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendState_fvarMap___default() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendState_fvarMap___default___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendState_fvarMap___default___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_name_eq(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__2(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Data.HashMap", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.HashMap.find!", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("key is not in the map", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__1;
x_2 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__2;
x_3 = lean_unsigned_to_nat(182u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_10, x_1);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_11);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_3, x_9);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__1(x_18, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__4;
x_21 = l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__3(x_20);
lean_inc(x_1);
x_22 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_getType___spec__3(x_21, x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
lean_inc(x_1);
x_26 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_getType___spec__3(x_25, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
lean_ctor_set(x_16, 0, x_28);
return x_16;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__1(x_29, x_15);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__4;
x_33 = l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__3(x_32);
lean_inc(x_1);
x_34 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_getType___spec__3(x_33, x_1);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_30);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
lean_inc(x_1);
x_40 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_getType___spec__3(x_39, x_1);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_30);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_30);
return x_44;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_11 = l_Lean_Compiler_LCNF_ScopeM_addToScope(x_1, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 0);
lean_dec(x_18);
x_19 = lean_box(0);
x_20 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_17, x_1, x_19);
lean_ctor_set(x_3, 1, x_20);
x_21 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_22, x_1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_apply_8(x_2, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_14 = lean_array_uget(x_1, x_2);
lean_inc(x_14);
x_15 = l_Lean_Compiler_LCNF_ScopeM_addToScope(x_14, x_7, x_8, x_9, x_10, x_11, x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_4, x_14, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_4 = x_18;
x_12 = x_16;
goto _start;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_3, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_3, 0);
lean_dec(x_19);
x_20 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_13);
x_22 = lean_apply_8(x_2, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_14, x_14);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_14);
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_3, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_3, 0);
lean_dec(x_26);
x_27 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_13);
x_29 = lean_apply_8(x_2, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_29;
}
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; uint8_t x_33; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___spec__1(x_1, x_30, x_31, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_3, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_3, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
lean_ctor_set(x_3, 1, x_36);
x_38 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_3);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_11);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_apply_8(x_2, x_41, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_LCtx_addParam___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_name_eq(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_4);
x_8 = lean_hashmap_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_12);
x_17 = lean_hashmap_mk_idx(x_15, x_16);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__6(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__7(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__7(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
lean_inc(x_7);
x_9 = lean_hashmap_mk_idx(x_7, x_8);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__3(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_17 = lean_nat_dec_le(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__4(x_13, x_15);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__7(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
lean_inc(x_23);
x_25 = lean_hashmap_mk_idx(x_23, x_24);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__3(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_22, x_25, x_30);
x_32 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_29);
x_33 = lean_nat_dec_le(x_32, x_23);
lean_dec(x_23);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_HashMapImp_expand___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__4(x_29, x_31);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Lean_AssocList_replace___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__7(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_55; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_st_ref_get(x_3, x_9);
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
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l_Lean_Compiler_LCNF_ScopeM_isInScope(x_1, x_4, x_5, x_6, x_7, x_8, x_16);
lean_inc(x_13);
x_55 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__1(x_15, x_13);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_19, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
lean_dec(x_19);
x_58 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__4;
x_59 = l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__3(x_58);
x_60 = lean_unbox(x_56);
lean_dec(x_56);
x_20 = x_59;
x_21 = x_60;
x_22 = x_57;
goto block_54;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
lean_dec(x_55);
x_62 = lean_ctor_get(x_19, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_19, 1);
lean_inc(x_63);
lean_dec(x_19);
x_64 = lean_unbox(x_62);
lean_dec(x_62);
x_20 = x_61;
x_21 = x_64;
x_22 = x_63;
goto block_54;
}
block_54:
{
if (x_21 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__1(x_20, x_1);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_18, x_1);
lean_dec(x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_1);
x_25 = lean_box(0);
if (lean_is_scalar(x_17)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_17;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_17);
lean_inc(x_1);
x_27 = l_Lean_Compiler_LCNF_getType(x_1, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 0;
x_31 = l_Lean_Compiler_LCNF_mkAuxParam(x_28, x_30, x_5, x_6, x_7, x_8, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_LCtx_addParam___spec__1(x_20, x_1, x_32);
x_35 = lean_st_ref_take(x_3, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__2(x_36, x_13, x_34);
x_39 = lean_st_ref_set(x_3, x_38, x_37);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_27);
if (x_46 == 0)
{
return x_27;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_27, 0);
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_27);
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
lean_object* x_50; lean_object* x_51; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_1);
x_50 = lean_box(0);
if (lean_is_scalar(x_17)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_17;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_22);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_1);
x_52 = lean_box(0);
if (lean_is_scalar(x_17)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_17;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_22);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_15 = lean_array_uget(x_1, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_5);
x_17 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_box(0);
x_3 = x_20;
x_4 = x_21;
x_12 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; 
lean_dec(x_10);
x_13 = lean_st_ref_get(x_3, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
x_17 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__1(x_14, x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_18 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__4;
x_19 = l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__3(x_18);
x_20 = l_Lean_HashMap_toArray___at_Lean_Compiler_LCNF_LCtx_toLocalContext___spec__1(x_19);
x_21 = lean_array_get_size(x_20);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary___spec__1(x_20, x_22, x_16, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = l_Lean_HashMap_toArray___at_Lean_Compiler_LCNF_LCtx_toLocalContext___spec__1(x_33);
x_35 = lean_array_get_size(x_34);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary___spec__1(x_34, x_36, x_16, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_34);
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
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary___spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_11 = lean_apply_8(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_9(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
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
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__2___rarg), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Compiler_LCNF_ScopeM_getScope(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__3___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__2___boxed), 10, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___closed__1;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__2___rarg), 10, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__3___rarg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__1___rarg), 9, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___rarg___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___rarg___closed__1;
x_11 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__1___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___rarg), 9, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Compiler_LCNF_ScopeM_getScope(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__3___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__2___boxed), 10, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___closed__1;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__2___rarg), 10, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__3___rarg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__2___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
lean_inc(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_3, 0);
lean_dec(x_15);
lean_ctor_set(x_3, 0, x_13);
x_16 = lean_st_ref_take(x_4, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__1;
x_20 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__2(x_17, x_11, x_19);
x_21 = lean_st_ref_set(x_4, x_20, x_18);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_array_get_size(x_12);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__1(x_24, x_25, x_12);
x_27 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___rarg___boxed), 10, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_2);
x_28 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__2___rarg(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_dec(x_3);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_st_ref_take(x_4, x_10);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__1;
x_35 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary___spec__2(x_32, x_11, x_34);
x_36 = lean_st_ref_set(x_4, x_35, x_33);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_array_get_size(x_12);
x_39 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_40 = 0;
x_41 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__1(x_39, x_40, x_12);
x_42 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___rarg___boxed), 10, 2);
lean_closure_set(x_42, 0, x_41);
lean_closure_set(x_42, 1, x_2);
x_43 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__2___rarg(x_42, x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Compiler_LCNF_ScopeM_getScope(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___spec__1___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l_Lean_Compiler_LCNF_AltCore_getParams(x_1);
lean_dec(x_1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___spec__1(x_13, x_14, x_11);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidates___rarg___boxed), 10, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_2);
x_17 = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___spec__1___rarg(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_goFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_12;
}
else
{
uint8_t x_13; 
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_goFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_goFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__3;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__4___closed__1;
x_11 = lean_panic_fn(x_10, x_1);
x_12 = lean_apply_8(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Expr.mapFVarM", 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__1;
x_2 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3___closed__1;
x_3 = lean_unsigned_to_nat(26u);
x_4 = lean_unsigned_to_nat(39u);
x_5 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_inc(x_11);
x_12 = lean_apply_9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_name_eq(x_11, x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = l_Lean_Expr_fvar___override(x_14);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_name_eq(x_11, x_17);
lean_dec(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_20 = l_Lean_Expr_fvar___override(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_2);
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
case 2:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3___closed__2;
x_28 = l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__4(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_29);
lean_inc(x_1);
x_31 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3(x_1, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_30);
x_34 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3(x_1, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; size_t x_37; size_t x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ptr_addr(x_29);
lean_dec(x_29);
x_38 = lean_ptr_addr(x_32);
x_39 = lean_usize_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_30);
lean_dec(x_2);
x_40 = l_Lean_Expr_app___override(x_32, x_36);
lean_ctor_set(x_34, 0, x_40);
return x_34;
}
else
{
size_t x_41; size_t x_42; uint8_t x_43; 
x_41 = lean_ptr_addr(x_30);
lean_dec(x_30);
x_42 = lean_ptr_addr(x_36);
x_43 = lean_usize_dec_eq(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_2);
x_44 = l_Lean_Expr_app___override(x_32, x_36);
lean_ctor_set(x_34, 0, x_44);
return x_34;
}
else
{
lean_dec(x_36);
lean_dec(x_32);
lean_ctor_set(x_34, 0, x_2);
return x_34;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_34, 0);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_34);
x_47 = lean_ptr_addr(x_29);
lean_dec(x_29);
x_48 = lean_ptr_addr(x_32);
x_49 = lean_usize_dec_eq(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_30);
lean_dec(x_2);
x_50 = l_Lean_Expr_app___override(x_32, x_45);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
return x_51;
}
else
{
size_t x_52; size_t x_53; uint8_t x_54; 
x_52 = lean_ptr_addr(x_30);
lean_dec(x_30);
x_53 = lean_ptr_addr(x_45);
x_54 = lean_usize_dec_eq(x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_2);
x_55 = l_Lean_Expr_app___override(x_32, x_45);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_46);
return x_56;
}
else
{
lean_object* x_57; 
lean_dec(x_45);
lean_dec(x_32);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_46);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_34);
if (x_58 == 0)
{
return x_34;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_34, 0);
x_60 = lean_ctor_get(x_34, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_34);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_31);
if (x_62 == 0)
{
return x_31;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_31, 0);
x_64 = lean_ctor_get(x_31, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_31);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
case 6:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_2, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_2, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_2, 2);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_67);
lean_inc(x_1);
x_70 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3(x_1, x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_68);
x_73 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3(x_1, x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_72);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
x_76 = l_Lean_Expr_lam___override(x_66, x_67, x_68, x_69);
x_77 = lean_ptr_addr(x_67);
lean_dec(x_67);
x_78 = lean_ptr_addr(x_71);
x_79 = lean_usize_dec_eq(x_77, x_78);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_76);
lean_dec(x_68);
x_80 = l_Lean_Expr_lam___override(x_66, x_71, x_75, x_69);
lean_ctor_set(x_73, 0, x_80);
return x_73;
}
else
{
size_t x_81; size_t x_82; uint8_t x_83; 
x_81 = lean_ptr_addr(x_68);
lean_dec(x_68);
x_82 = lean_ptr_addr(x_75);
x_83 = lean_usize_dec_eq(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_76);
x_84 = l_Lean_Expr_lam___override(x_66, x_71, x_75, x_69);
lean_ctor_set(x_73, 0, x_84);
return x_73;
}
else
{
uint8_t x_85; 
x_85 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_69, x_69);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_76);
x_86 = l_Lean_Expr_lam___override(x_66, x_71, x_75, x_69);
lean_ctor_set(x_73, 0, x_86);
return x_73;
}
else
{
lean_dec(x_75);
lean_dec(x_71);
lean_dec(x_66);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; size_t x_90; size_t x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_73, 0);
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_73);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
x_89 = l_Lean_Expr_lam___override(x_66, x_67, x_68, x_69);
x_90 = lean_ptr_addr(x_67);
lean_dec(x_67);
x_91 = lean_ptr_addr(x_71);
x_92 = lean_usize_dec_eq(x_90, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_89);
lean_dec(x_68);
x_93 = l_Lean_Expr_lam___override(x_66, x_71, x_87, x_69);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_88);
return x_94;
}
else
{
size_t x_95; size_t x_96; uint8_t x_97; 
x_95 = lean_ptr_addr(x_68);
lean_dec(x_68);
x_96 = lean_ptr_addr(x_87);
x_97 = lean_usize_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_89);
x_98 = l_Lean_Expr_lam___override(x_66, x_71, x_87, x_69);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_88);
return x_99;
}
else
{
uint8_t x_100; 
x_100 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_69, x_69);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_89);
x_101 = l_Lean_Expr_lam___override(x_66, x_71, x_87, x_69);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_88);
return x_102;
}
else
{
lean_object* x_103; 
lean_dec(x_87);
lean_dec(x_71);
lean_dec(x_66);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_89);
lean_ctor_set(x_103, 1, x_88);
return x_103;
}
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
x_104 = !lean_is_exclusive(x_73);
if (x_104 == 0)
{
return x_73;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_73, 0);
x_106 = lean_ctor_get(x_73, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_73);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_70);
if (x_108 == 0)
{
return x_70;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_70, 0);
x_110 = lean_ctor_get(x_70, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_70);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
case 7:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_2, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_2, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_2, 2);
lean_inc(x_114);
x_115 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_113);
lean_inc(x_1);
x_116 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3(x_1, x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_114);
x_119 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3(x_1, x_114, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_118);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; size_t x_123; size_t x_124; uint8_t x_125; 
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
x_122 = l_Lean_Expr_forallE___override(x_112, x_113, x_114, x_115);
x_123 = lean_ptr_addr(x_113);
lean_dec(x_113);
x_124 = lean_ptr_addr(x_117);
x_125 = lean_usize_dec_eq(x_123, x_124);
if (x_125 == 0)
{
lean_object* x_126; 
lean_dec(x_122);
lean_dec(x_114);
x_126 = l_Lean_Expr_forallE___override(x_112, x_117, x_121, x_115);
lean_ctor_set(x_119, 0, x_126);
return x_119;
}
else
{
size_t x_127; size_t x_128; uint8_t x_129; 
x_127 = lean_ptr_addr(x_114);
lean_dec(x_114);
x_128 = lean_ptr_addr(x_121);
x_129 = lean_usize_dec_eq(x_127, x_128);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec(x_122);
x_130 = l_Lean_Expr_forallE___override(x_112, x_117, x_121, x_115);
lean_ctor_set(x_119, 0, x_130);
return x_119;
}
else
{
uint8_t x_131; 
x_131 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_115, x_115);
if (x_131 == 0)
{
lean_object* x_132; 
lean_dec(x_122);
x_132 = l_Lean_Expr_forallE___override(x_112, x_117, x_121, x_115);
lean_ctor_set(x_119, 0, x_132);
return x_119;
}
else
{
lean_dec(x_121);
lean_dec(x_117);
lean_dec(x_112);
lean_ctor_set(x_119, 0, x_122);
return x_119;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; size_t x_136; size_t x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_119, 0);
x_134 = lean_ctor_get(x_119, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_119);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
x_135 = l_Lean_Expr_forallE___override(x_112, x_113, x_114, x_115);
x_136 = lean_ptr_addr(x_113);
lean_dec(x_113);
x_137 = lean_ptr_addr(x_117);
x_138 = lean_usize_dec_eq(x_136, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_135);
lean_dec(x_114);
x_139 = l_Lean_Expr_forallE___override(x_112, x_117, x_133, x_115);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_134);
return x_140;
}
else
{
size_t x_141; size_t x_142; uint8_t x_143; 
x_141 = lean_ptr_addr(x_114);
lean_dec(x_114);
x_142 = lean_ptr_addr(x_133);
x_143 = lean_usize_dec_eq(x_141, x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_135);
x_144 = l_Lean_Expr_forallE___override(x_112, x_117, x_133, x_115);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_134);
return x_145;
}
else
{
uint8_t x_146; 
x_146 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_399_(x_115, x_115);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_135);
x_147 = l_Lean_Expr_forallE___override(x_112, x_117, x_133, x_115);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_134);
return x_148;
}
else
{
lean_object* x_149; 
lean_dec(x_133);
lean_dec(x_117);
lean_dec(x_112);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_135);
lean_ctor_set(x_149, 1, x_134);
return x_149;
}
}
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_117);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
x_150 = !lean_is_exclusive(x_119);
if (x_150 == 0)
{
return x_119;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_119, 0);
x_152 = lean_ctor_get(x_119, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_119);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_116);
if (x_154 == 0)
{
return x_116;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_116, 0);
x_156 = lean_ctor_get(x_116, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_116);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
case 8:
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_2);
lean_dec(x_1);
x_158 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3___closed__2;
x_159 = l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__4(x_158, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_159;
}
case 11:
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_2);
lean_dec(x_1);
x_160 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3___closed__2;
x_161 = l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__4(x_160, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_161;
}
default: 
{
lean_object* x_162; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_2);
lean_ctor_set(x_162, 1, x_10);
return x_162;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
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
case 1:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_apply_9(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp(x_2, x_16);
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
x_20 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateFVarImp(x_2, x_18);
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
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
default: 
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3(x_1, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(x_2, x_29);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_Arg_updateTypeImp(x_2, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
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
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_uget(x_4, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l_Lean_Compiler_LCNF_Arg_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__2(x_1, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_23 = lean_array_uset(x_17, x_3, x_19);
x_3 = x_22;
x_4 = x_23;
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
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
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_uget(x_4, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l_Lean_Compiler_LCNF_Arg_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__2(x_1, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_23 = lean_array_uset(x_17, x_3, x_19);
x_3 = x_22;
x_4 = x_23;
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
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_apply_9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(x_2, x_14);
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
x_18 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateProjImp(x_2, x_16);
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
case 3:
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
x_25 = lean_array_get_size(x_24);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__5(x_1, x_26, x_27, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_2, x_30);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateArgsImp(x_2, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
case 4:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = lean_apply_9(x_1, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_array_get_size(x_41);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = 0;
x_48 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__6(x_1, x_46, x_47, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(x_2, x_43, x_50);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
x_54 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_LetValue_updateFVarImp(x_2, x_43, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_43);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
return x_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
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
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_42);
if (x_60 == 0)
{
return x_42;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_42, 0);
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_42);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
default: 
{
lean_object* x_64; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_2);
lean_ctor_set(x_64, 1, x_10);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__7(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 0;
x_12 = l_Lean_Expr_forallE___override(x_9, x_10, x_4, x_11);
x_2 = x_7;
x_4 = x_12;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_goFVar___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__9(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_2, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__9___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Compiler_LCNF_Arg_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__2(x_17, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_23 = lean_array_uset(x_16, x_2, x_19);
x_2 = x_22;
x_3 = x_23;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_16);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__10(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__11(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__12(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_2, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
lean_inc(x_4);
x_17 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_goFVar(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_16, x_2, x_20);
x_2 = x_22;
x_3 = x_23;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_mapCodeM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Compiler_LCNF_AltCore_getCode(x_1);
x_12 = lean_apply_9(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_14);
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
x_18 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__14___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__14(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_2, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__14___closed__1;
lean_inc(x_14);
x_18 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_AltCore_mapCodeM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__13), 10, 2);
lean_closure_set(x_18, 0, x_14);
lean_closure_set(x_18, 1, x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewAltScope___rarg(x_14, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_24 = lean_array_uset(x_16, x_2, x_20);
x_2 = x_23;
x_3 = x_24;
x_11 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = lean_ptr_addr(x_1);
x_15 = lean_ptr_addr(x_5);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_3);
x_20 = lean_ptr_addr(x_2);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_13);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_11, x_12, x_2, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = lean_ptr_addr(x_1);
x_15 = lean_ptr_addr(x_5);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_3);
x_20 = lean_ptr_addr(x_2);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_13);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_32; 
x_11 = lean_st_ref_get(x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = 0;
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_32 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__1(x_12, x_14);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__4;
x_34 = l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__3(x_33);
x_18 = x_34;
goto block_31;
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
x_18 = x_35;
goto block_31;
}
block_31:
{
lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = l_Lean_HashMap_toArray___at_Lean_Compiler_LCNF_LCtx_toLocalContext___spec__1(x_18);
x_20 = lean_array_get_size(x_19);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__7(x_21, x_15, x_19);
x_23 = lean_array_get_size(x_22);
lean_inc(x_22);
x_24 = l_Array_append___rarg(x_22, x_17);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_23);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_22);
x_27 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_16, x_24, x_2, x_6, x_7, x_8, x_9, x_13);
return x_27;
}
else
{
size_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_29 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__8(x_22, x_28, x_15, x_16);
lean_dec(x_22);
x_30 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_1, x_29, x_24, x_2, x_6, x_7, x_8, x_9, x_13);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = lean_ptr_addr(x_1);
x_15 = lean_ptr_addr(x_5);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_3);
x_20 = lean_ptr_addr(x_2);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_13);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_name_eq(x_1, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = lean_ptr_addr(x_2);
x_18 = lean_ptr_addr(x_4);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
x_20 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_4);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__9___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Compiler_LCNF_LetValue_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__1(x_13, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_10);
x_17 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_10, x_15, x_5, x_6, x_7, x_8, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_inc(x_11);
x_21 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go), 9, 1);
lean_closure_set(x_21, 0, x_11);
x_22 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__1___boxed), 13, 4);
lean_closure_set(x_22, 0, x_11);
lean_closure_set(x_22, 1, x_18);
lean_closure_set(x_22, 2, x_10);
lean_closure_set(x_22, 3, x_1);
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__2___rarg), 10, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate___rarg(x_20, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 4);
lean_inc(x_31);
x_32 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go), 9, 1);
lean_closure_set(x_32, 0, x_31);
lean_inc(x_29);
x_33 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__2___boxed), 10, 1);
lean_closure_set(x_33, 0, x_29);
x_34 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__2___rarg), 10, 2);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_33);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_35 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___rarg(x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_inc(x_30);
x_39 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go), 9, 1);
lean_closure_set(x_39, 0, x_30);
x_40 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__3___boxed), 13, 4);
lean_closure_set(x_40, 0, x_30);
lean_closure_set(x_40, 1, x_36);
lean_closure_set(x_40, 2, x_29);
lean_closure_set(x_40, 3, x_1);
x_41 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__2___rarg), 10, 2);
lean_closure_set(x_41, 0, x_39);
lean_closure_set(x_41, 1, x_40);
x_42 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate___rarg(x_38, x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_35);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 2:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 4);
lean_inc(x_49);
x_50 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go), 9, 1);
lean_closure_set(x_50, 0, x_49);
lean_inc(x_47);
x_51 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__4___boxed), 10, 1);
lean_closure_set(x_51, 0, x_47);
x_52 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__2___rarg), 10, 2);
lean_closure_set(x_52, 0, x_50);
lean_closure_set(x_52, 1, x_51);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_47);
x_53 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewJpScope___rarg(x_47, x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_inc(x_2);
lean_inc(x_56);
x_57 = l_Lean_Compiler_LCNF_JoinPointContextExtender_mergeJpContextIfNecessary(x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
lean_inc(x_48);
x_59 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go), 9, 1);
lean_closure_set(x_59, 0, x_48);
x_60 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__5___boxed), 13, 4);
lean_closure_set(x_60, 0, x_48);
lean_closure_set(x_60, 1, x_54);
lean_closure_set(x_60, 2, x_47);
lean_closure_set(x_60, 3, x_1);
x_61 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___spec__2___rarg), 10, 2);
lean_closure_set(x_61, 0, x_59);
lean_closure_set(x_61, 1, x_60);
x_62 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewCandidate___rarg(x_56, x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_58);
return x_62;
}
else
{
uint8_t x_63; 
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_57);
if (x_63 == 0)
{
return x_57;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_57, 0);
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_57);
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
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_53);
if (x_67 == 0)
{
return x_53;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_53, 0);
x_69 = lean_ctor_get(x_53, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
case 3:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 1);
lean_inc(x_72);
x_73 = lean_array_get_size(x_72);
x_74 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_75 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_72);
x_76 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__9(x_74, x_75, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_107; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_st_ref_get(x_3, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_2, 0);
lean_inc(x_82);
lean_inc(x_71);
x_107 = l_Lean_HashMapImp_find_x3f___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__1(x_80, x_71);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__4;
x_109 = l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___spec__3(x_108);
x_83 = x_109;
goto block_106;
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
lean_dec(x_107);
x_83 = x_110;
goto block_106;
}
block_106:
{
lean_object* x_84; lean_object* x_85; size_t x_86; lean_object* x_87; 
x_84 = l_Lean_HashMap_toArray___at_Lean_Compiler_LCNF_LCtx_toLocalContext___spec__1(x_83);
x_85 = lean_array_get_size(x_84);
x_86 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_87 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__10(x_86, x_75, x_84);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_88; size_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_array_get_size(x_87);
x_89 = lean_usize_of_nat(x_88);
lean_dec(x_88);
x_90 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__11(x_89, x_75, x_87);
x_91 = l_Array_append___rarg(x_90, x_77);
x_92 = lean_box(0);
x_93 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__6(x_71, x_72, x_1, x_91, x_92, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_81);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_72);
return x_93;
}
else
{
lean_object* x_94; size_t x_95; lean_object* x_96; 
lean_dec(x_82);
x_94 = lean_array_get_size(x_87);
x_95 = lean_usize_of_nat(x_94);
lean_dec(x_94);
lean_inc(x_2);
x_96 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__12(x_95, x_75, x_87, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_81);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Array_append___rarg(x_97, x_77);
x_100 = lean_box(0);
x_101 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__6(x_71, x_72, x_1, x_99, x_100, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_98);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_72);
return x_101;
}
else
{
uint8_t x_102; 
lean_dec(x_77);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_96);
if (x_102 == 0)
{
return x_96;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_96, 0);
x_104 = lean_ctor_get(x_96, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_96);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_76);
if (x_111 == 0)
{
return x_76;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_76, 0);
x_113 = lean_ctor_get(x_76, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_76);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
case 4:
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_1, 0);
lean_inc(x_115);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = lean_ctor_get(x_115, 2);
x_120 = lean_ctor_get(x_115, 3);
lean_inc(x_2);
lean_inc(x_119);
x_121 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary(x_119, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; size_t x_127; size_t x_128; lean_object* x_129; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
lean_inc(x_2);
lean_inc(x_119);
x_123 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar(x_119, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_array_get_size(x_120);
x_127 = lean_usize_of_nat(x_126);
lean_dec(x_126);
x_128 = 0;
lean_inc(x_120);
x_129 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__14(x_127, x_128, x_120, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_125);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; size_t x_132; size_t x_133; uint8_t x_134; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_ptr_addr(x_120);
lean_dec(x_120);
x_133 = lean_ptr_addr(x_131);
x_134 = lean_usize_dec_eq(x_132, x_133);
if (x_134 == 0)
{
uint8_t x_135; 
lean_dec(x_119);
x_135 = !lean_is_exclusive(x_1);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_1, 0);
lean_dec(x_136);
lean_ctor_set(x_115, 3, x_131);
lean_ctor_set(x_115, 2, x_124);
lean_ctor_set(x_129, 0, x_1);
return x_129;
}
else
{
lean_object* x_137; 
lean_dec(x_1);
lean_ctor_set(x_115, 3, x_131);
lean_ctor_set(x_115, 2, x_124);
x_137 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_137, 0, x_115);
lean_ctor_set(x_129, 0, x_137);
return x_129;
}
}
else
{
size_t x_138; uint8_t x_139; 
x_138 = lean_ptr_addr(x_118);
x_139 = lean_usize_dec_eq(x_138, x_138);
if (x_139 == 0)
{
uint8_t x_140; 
lean_dec(x_119);
x_140 = !lean_is_exclusive(x_1);
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_1, 0);
lean_dec(x_141);
lean_ctor_set(x_115, 3, x_131);
lean_ctor_set(x_115, 2, x_124);
lean_ctor_set(x_129, 0, x_1);
return x_129;
}
else
{
lean_object* x_142; 
lean_dec(x_1);
lean_ctor_set(x_115, 3, x_131);
lean_ctor_set(x_115, 2, x_124);
x_142 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_142, 0, x_115);
lean_ctor_set(x_129, 0, x_142);
return x_129;
}
}
else
{
uint8_t x_143; 
x_143 = lean_name_eq(x_119, x_124);
lean_dec(x_119);
if (x_143 == 0)
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_1);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_1, 0);
lean_dec(x_145);
lean_ctor_set(x_115, 3, x_131);
lean_ctor_set(x_115, 2, x_124);
lean_ctor_set(x_129, 0, x_1);
return x_129;
}
else
{
lean_object* x_146; 
lean_dec(x_1);
lean_ctor_set(x_115, 3, x_131);
lean_ctor_set(x_115, 2, x_124);
x_146 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_146, 0, x_115);
lean_ctor_set(x_129, 0, x_146);
return x_129;
}
}
else
{
lean_dec(x_131);
lean_dec(x_124);
lean_free_object(x_115);
lean_dec(x_118);
lean_dec(x_117);
lean_ctor_set(x_129, 0, x_1);
return x_129;
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; size_t x_149; size_t x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_129, 0);
x_148 = lean_ctor_get(x_129, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_129);
x_149 = lean_ptr_addr(x_120);
lean_dec(x_120);
x_150 = lean_ptr_addr(x_147);
x_151 = lean_usize_dec_eq(x_149, x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_119);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_152 = x_1;
} else {
 lean_dec_ref(x_1);
 x_152 = lean_box(0);
}
lean_ctor_set(x_115, 3, x_147);
lean_ctor_set(x_115, 2, x_124);
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(4, 1, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_115);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_148);
return x_154;
}
else
{
size_t x_155; uint8_t x_156; 
x_155 = lean_ptr_addr(x_118);
x_156 = lean_usize_dec_eq(x_155, x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_119);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_157 = x_1;
} else {
 lean_dec_ref(x_1);
 x_157 = lean_box(0);
}
lean_ctor_set(x_115, 3, x_147);
lean_ctor_set(x_115, 2, x_124);
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(4, 1, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_115);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_148);
return x_159;
}
else
{
uint8_t x_160; 
x_160 = lean_name_eq(x_119, x_124);
lean_dec(x_119);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_161 = x_1;
} else {
 lean_dec_ref(x_1);
 x_161 = lean_box(0);
}
lean_ctor_set(x_115, 3, x_147);
lean_ctor_set(x_115, 2, x_124);
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(4, 1, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_115);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_148);
return x_163;
}
else
{
lean_object* x_164; 
lean_dec(x_147);
lean_dec(x_124);
lean_free_object(x_115);
lean_dec(x_118);
lean_dec(x_117);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_1);
lean_ctor_set(x_164, 1, x_148);
return x_164;
}
}
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_124);
lean_free_object(x_115);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_129);
if (x_165 == 0)
{
return x_129;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_129, 0);
x_167 = lean_ctor_get(x_129, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_129);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_free_object(x_115);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_121);
if (x_169 == 0)
{
return x_121;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_121, 0);
x_171 = lean_ctor_get(x_121, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_121);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_173 = lean_ctor_get(x_115, 0);
x_174 = lean_ctor_get(x_115, 1);
x_175 = lean_ctor_get(x_115, 2);
x_176 = lean_ctor_get(x_115, 3);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_115);
lean_inc(x_2);
lean_inc(x_175);
x_177 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary(x_175, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; size_t x_183; size_t x_184; lean_object* x_185; 
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
lean_inc(x_2);
lean_inc(x_175);
x_179 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar(x_175, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_array_get_size(x_176);
x_183 = lean_usize_of_nat(x_182);
lean_dec(x_182);
x_184 = 0;
lean_inc(x_176);
x_185 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__14(x_183, x_184, x_176, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_181);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; size_t x_189; size_t x_190; uint8_t x_191; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
x_189 = lean_ptr_addr(x_176);
lean_dec(x_176);
x_190 = lean_ptr_addr(x_186);
x_191 = lean_usize_dec_eq(x_189, x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_175);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_192 = x_1;
} else {
 lean_dec_ref(x_1);
 x_192 = lean_box(0);
}
x_193 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_193, 0, x_173);
lean_ctor_set(x_193, 1, x_174);
lean_ctor_set(x_193, 2, x_180);
lean_ctor_set(x_193, 3, x_186);
if (lean_is_scalar(x_192)) {
 x_194 = lean_alloc_ctor(4, 1, 0);
} else {
 x_194 = x_192;
}
lean_ctor_set(x_194, 0, x_193);
if (lean_is_scalar(x_188)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_188;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_187);
return x_195;
}
else
{
size_t x_196; uint8_t x_197; 
x_196 = lean_ptr_addr(x_174);
x_197 = lean_usize_dec_eq(x_196, x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_175);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_198 = x_1;
} else {
 lean_dec_ref(x_1);
 x_198 = lean_box(0);
}
x_199 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_199, 0, x_173);
lean_ctor_set(x_199, 1, x_174);
lean_ctor_set(x_199, 2, x_180);
lean_ctor_set(x_199, 3, x_186);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(4, 1, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_199);
if (lean_is_scalar(x_188)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_188;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_187);
return x_201;
}
else
{
uint8_t x_202; 
x_202 = lean_name_eq(x_175, x_180);
lean_dec(x_175);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_203 = x_1;
} else {
 lean_dec_ref(x_1);
 x_203 = lean_box(0);
}
x_204 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_204, 0, x_173);
lean_ctor_set(x_204, 1, x_174);
lean_ctor_set(x_204, 2, x_180);
lean_ctor_set(x_204, 3, x_186);
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(4, 1, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_204);
if (lean_is_scalar(x_188)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_188;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_187);
return x_206;
}
else
{
lean_object* x_207; 
lean_dec(x_186);
lean_dec(x_180);
lean_dec(x_174);
lean_dec(x_173);
if (lean_is_scalar(x_188)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_188;
}
lean_ctor_set(x_207, 0, x_1);
lean_ctor_set(x_207, 1, x_187);
return x_207;
}
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_180);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_1);
x_208 = lean_ctor_get(x_185, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_185, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_210 = x_185;
} else {
 lean_dec_ref(x_185);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_212 = lean_ctor_get(x_177, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_177, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_214 = x_177;
} else {
 lean_dec_ref(x_177);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
}
case 5:
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_1, 0);
lean_inc(x_216);
lean_inc(x_2);
lean_inc(x_216);
x_217 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extendByIfNecessary(x_216, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
lean_inc(x_216);
x_219 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar(x_216, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_218);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
lean_object* x_221; uint8_t x_222; 
x_221 = lean_ctor_get(x_219, 0);
x_222 = lean_name_eq(x_216, x_221);
lean_dec(x_216);
if (x_222 == 0)
{
uint8_t x_223; 
x_223 = !lean_is_exclusive(x_1);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_1, 0);
lean_dec(x_224);
lean_ctor_set(x_1, 0, x_221);
lean_ctor_set(x_219, 0, x_1);
return x_219;
}
else
{
lean_object* x_225; 
lean_dec(x_1);
x_225 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_225, 0, x_221);
lean_ctor_set(x_219, 0, x_225);
return x_219;
}
}
else
{
lean_dec(x_221);
lean_ctor_set(x_219, 0, x_1);
return x_219;
}
}
else
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_226 = lean_ctor_get(x_219, 0);
x_227 = lean_ctor_get(x_219, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_219);
x_228 = lean_name_eq(x_216, x_226);
lean_dec(x_216);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_229 = x_1;
} else {
 lean_dec_ref(x_1);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(5, 1, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_226);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_227);
return x_231;
}
else
{
lean_object* x_232; 
lean_dec(x_226);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_1);
lean_ctor_set(x_232, 1, x_227);
return x_232;
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_216);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_233 = !lean_is_exclusive(x_217);
if (x_233 == 0)
{
return x_217;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_217, 0);
x_235 = lean_ctor_get(x_217, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_217);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
default: 
{
lean_object* x_237; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_1);
lean_ctor_set(x_237, 1, x_9);
return x_237;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__5(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__6(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__7(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__8(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__9(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__10(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__11(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__12(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__14(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointContextExtender_extend(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_ctor_get(x_1, 5);
x_14 = lean_box(0);
x_15 = lean_st_mk_ref(x_14, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__1;
x_19 = lean_st_mk_ref(x_18, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___rarg___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_16);
lean_inc(x_20);
x_23 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go(x_12, x_22, x_20, x_16, x_2, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_20, x_25);
lean_dec(x_20);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_get(x_16, x_27);
lean_dec(x_16);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_ctor_set(x_1, 4, x_24);
x_30 = l_Lean_Compiler_LCNF_Decl_pullFunDecls(x_1, x_2, x_3, x_4, x_5, x_29);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_20);
lean_dec(x_16);
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_ctor_get(x_1, 4);
x_40 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_41 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_42 = lean_ctor_get(x_1, 5);
lean_inc(x_42);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_1);
x_43 = lean_box(0);
x_44 = lean_st_mk_ref(x_43, x_6);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__1;
x_48 = lean_st_mk_ref(x_47, x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___rarg___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_45);
lean_inc(x_49);
x_52 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go(x_39, x_51, x_49, x_45, x_2, x_3, x_4, x_5, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_st_ref_get(x_49, x_54);
lean_dec(x_49);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_get(x_45, x_56);
lean_dec(x_45);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_59, 0, x_35);
lean_ctor_set(x_59, 1, x_36);
lean_ctor_set(x_59, 2, x_37);
lean_ctor_set(x_59, 3, x_38);
lean_ctor_set(x_59, 4, x_53);
lean_ctor_set(x_59, 5, x_42);
lean_ctor_set_uint8(x_59, sizeof(void*)*6, x_40);
lean_ctor_set_uint8(x_59, sizeof(void*)*6 + 1, x_41);
x_60 = l_Lean_Compiler_LCNF_Decl_pullFunDecls(x_59, x_2, x_3, x_4, x_5, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_49);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_ctor_get(x_52, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_63 = x_52;
} else {
 lean_dec_ref(x_52);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_AnalysisCtx_jpScopes___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_AnalysisState_jpJmpArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instFVarIdSetInhabited;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Data.RBMap", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.RBMap.find!", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__1;
x_2 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__2;
x_3 = lean_unsigned_to_nat(373u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___spec__1(x_3, x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__3;
x_13 = l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___spec__2(x_12);
x_14 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_13, x_2);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_21, x_2);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_11 = lean_apply_8(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_9(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
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
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__2___rarg), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Compiler_LCNF_ScopeM_getScope(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__2___boxed), 10, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___closed__1;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__2___rarg), 10, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__4(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_2);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Compiler_LCNF_ScopeM_addToScope(x_15, x_7, x_8, x_9, x_10, x_11, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_2 = x_20;
x_4 = x_17;
x_12 = x_18;
goto _start;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___lambda__1), 10, 1);
lean_closure_set(x_14, 0, x_1);
if (x_13 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__1___rarg___boxed), 9, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__2___rarg), 10, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_14);
x_18 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__3(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_11, x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__1___rarg___boxed), 9, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__2___rarg), 10, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_14);
x_23 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__3(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_23;
}
else
{
size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_25 = lean_box(0);
x_26 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___boxed__const__1;
x_27 = lean_box_usize(x_24);
x_28 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__5___boxed), 12, 4);
lean_closure_set(x_28, 0, x_10);
lean_closure_set(x_28, 1, x_26);
lean_closure_set(x_28, 2, x_27);
lean_closure_set(x_28, 3, x_25);
x_29 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__2___rarg), 10, 2);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_14);
x_30 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__3(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
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
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 0);
lean_dec(x_21);
x_22 = l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__3___closed__1;
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__3___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
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
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__3;
x_2 = l_OptionT_instMonadOptionT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6___closed__1;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6___closed__2;
x_11 = lean_panic_fn(x_10, x_1);
x_12 = lean_apply_8(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__4;
x_14 = l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
case 5:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_17 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__5(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_18);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_2 = x_16;
x_10 = x_25;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
case 6:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 2);
lean_inc(x_32);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_33 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__5(x_1, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_34);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_dec(x_33);
x_2 = x_32;
x_10 = x_41;
goto _start;
}
}
else
{
uint8_t x_43; 
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_33);
if (x_43 == 0)
{
return x_33;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_33, 0);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_33);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 7:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_49 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__5(x_1, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
lean_dec(x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_49, 0, x_53);
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_dec(x_49);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; 
lean_dec(x_50);
x_57 = lean_ctor_get(x_49, 1);
lean_inc(x_57);
lean_dec(x_49);
x_2 = x_48;
x_10 = x_57;
goto _start;
}
}
else
{
uint8_t x_59; 
lean_dec(x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_49);
if (x_59 == 0)
{
return x_49;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_49, 0);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_49);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
case 8:
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_2);
lean_dec(x_1);
x_63 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__4;
x_64 = l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6(x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_64;
}
case 11:
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_2);
lean_dec(x_1);
x_65 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__4;
x_66 = l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_66;
}
default: 
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__3___closed__1;
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_10);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__3___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_9(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lean_Compiler_LCNF_Expr_forFVarM___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__5(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__3), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Compiler_LCNF_Arg_forFVarM___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__4(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = 0;
x_17 = lean_box(x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_13);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
lean_dec(x_23);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_dec(x_12);
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
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
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_3, x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_2, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___boxed), 10, 1);
lean_closure_set(x_18, 0, x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_17);
x_19 = l_Lean_Compiler_LCNF_allFVarM___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__2(x_18, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; size_t x_23; size_t x_24; 
lean_dec(x_17);
lean_dec(x_16);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_3 = x_24;
x_13 = x_22;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = l_Lean_Compiler_LCNF_Arg_toExpr(x_17);
x_29 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_5, x_27, x_28);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_3 = x_31;
x_5 = x_29;
x_13 = x_26;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_13);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__10(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_AssocList_erase___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__10(x_1, x_7);
lean_ctor_set(x_2, 2, x_9);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_AssocList_erase___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__10(x_1, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_erase___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
x_7 = lean_hashmap_mk_idx(x_5, x_6);
x_8 = lean_array_uget(x_4, x_7);
x_9 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_2, x_8);
if (x_9 == 0)
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_3, x_13);
lean_dec(x_3);
x_15 = l_Lean_AssocList_erase___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__10(x_2, x_8);
x_16 = lean_array_uset(x_4, x_7, x_15);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_3, x_17);
lean_dec(x_3);
x_19 = l_Lean_AssocList_erase___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__10(x_2, x_8);
x_20 = lean_array_uset(x_4, x_7, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_1, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_18);
lean_inc(x_4);
x_19 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go___spec__1(x_4, x_18);
if (lean_obj_tag(x_19) == 0)
{
size_t x_20; size_t x_21; 
lean_dec(x_18);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_Compiler_LCNF_Arg_toExpr(x_17);
x_25 = lean_expr_eqv(x_24, x_23);
lean_dec(x_23);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; size_t x_27; size_t x_28; 
x_26 = l_Lean_HashMapImp_erase___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__9(x_4, x_18);
lean_dec(x_18);
x_27 = 1;
x_28 = lean_usize_add(x_3, x_27);
x_3 = x_28;
x_4 = x_26;
goto _start;
}
else
{
size_t x_30; size_t x_31; 
lean_dec(x_18);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_3 = x_31;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Compiler_LCNF_ScopeM_getScope(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_Compiler_LCNF_ScopeM_setScope(x_11, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___lambda__2___boxed), 10, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___closed__1;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__2___rarg), 10, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = l_Lean_Compiler_LCNF_ScopeM_withBackTrackingScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__13(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__14___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = l_Lean_Compiler_LCNF_AltCore_getCode(x_1);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__14___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_2);
x_15 = l_Lean_Compiler_LCNF_AltCore_getParams(x_14);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
x_19 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__14___lambda__1), 10, 1);
lean_closure_set(x_19, 0, x_14);
if (x_18 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__1___rarg___boxed), 9, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__2___rarg), 10, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__12(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 1;
x_27 = lean_usize_add(x_2, x_26);
x_2 = x_27;
x_4 = x_24;
x_12 = x_25;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
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
x_33 = lean_nat_dec_le(x_16, x_16);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_16);
lean_dec(x_15);
x_34 = lean_box(0);
x_35 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__1___rarg___boxed), 9, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__2___rarg), 10, 2);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_37 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__12(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = 1;
x_41 = lean_usize_add(x_2, x_40);
x_2 = x_41;
x_4 = x_38;
x_12 = x_39;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 0);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_37);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_48 = lean_box(0);
x_49 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__14___boxed__const__1;
x_50 = lean_box_usize(x_47);
x_51 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__5___boxed), 12, 4);
lean_closure_set(x_51, 0, x_15);
lean_closure_set(x_51, 1, x_49);
lean_closure_set(x_51, 2, x_50);
lean_closure_set(x_51, 3, x_48);
x_52 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__2___rarg), 10, 2);
lean_closure_set(x_52, 0, x_51);
lean_closure_set(x_52, 1, x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_53 = l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__12(x_52, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = 1;
x_57 = lean_usize_add(x_2, x_56);
x_2 = x_57;
x_4 = x_54;
x_12 = x_55;
goto _start;
}
else
{
uint8_t x_59; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_59 = !lean_is_exclusive(x_53);
if (x_59 == 0)
{
return x_53;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_53, 0);
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_53);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
else
{
lean_object* x_63; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_4);
lean_ctor_set(x_63, 1, x_12);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_LCNF_ScopeM_addToScope(x_12, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_1 = x_11;
x_9 = x_14;
goto _start;
}
case 1:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_16);
x_18 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Lean_Compiler_LCNF_ScopeM_addToScope(x_20, x_4, x_5, x_6, x_7, x_8, x_19);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_1 = x_17;
x_9 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
case 2:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_28);
x_30 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Compiler_LCNF_ScopeM_getScope(x_4, x_5, x_6, x_7, x_8, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
lean_inc(x_35);
x_36 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_2, x_35, x_33);
x_37 = l_Lean_Compiler_LCNF_ScopeM_addToScope(x_35, x_4, x_5, x_6, x_7, x_8, x_34);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_1 = x_29;
x_2 = x_36;
x_9 = x_38;
goto _start;
}
else
{
uint8_t x_40; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
return x_30;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_30);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
case 3:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
lean_inc(x_44);
x_46 = l_Lean_Compiler_LCNF_getFunDecl(x_44, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_st_ref_get(x_3, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__1(x_50, x_44);
lean_dec(x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_53 = lean_unsigned_to_nat(8u);
x_54 = l_Lean_mkHashMapImp___rarg(x_53);
x_55 = lean_ctor_get(x_47, 2);
lean_inc(x_55);
lean_dec(x_47);
x_56 = l_Array_zip___rarg(x_55, x_45);
lean_dec(x_45);
lean_dec(x_55);
x_57 = lean_array_get_size(x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_lt(x_58, x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_60 = lean_st_ref_take(x_3, x_51);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_61, x_44, x_54);
x_64 = lean_st_ref_set(x_3, x_63, x_62);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
x_67 = lean_box(0);
lean_ctor_set(x_64, 0, x_67);
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = lean_nat_dec_le(x_57, x_57);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_72 = lean_st_ref_take(x_3, x_51);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_73, x_44, x_54);
x_76 = lean_st_ref_set(x_3, x_75, x_74);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
x_79 = lean_box(0);
lean_ctor_set(x_76, 0, x_79);
return x_76;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
size_t x_83; size_t x_84; lean_object* x_85; 
x_83 = 0;
x_84 = lean_usize_of_nat(x_57);
lean_dec(x_57);
lean_inc(x_3);
lean_inc(x_44);
x_85 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__8(x_44, x_56, x_83, x_84, x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
lean_dec(x_56);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_st_ref_take(x_3, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_89, x_44, x_86);
x_92 = lean_st_ref_set(x_3, x_91, x_90);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
x_95 = lean_box(0);
lean_ctor_set(x_92, 0, x_95);
return x_92;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_44);
lean_dec(x_3);
x_99 = !lean_is_exclusive(x_85);
if (x_99 == 0)
{
return x_85;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_85, 0);
x_101 = lean_ctor_get(x_85, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_85);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; size_t x_107; size_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_103 = lean_ctor_get(x_52, 0);
lean_inc(x_103);
lean_dec(x_52);
x_104 = lean_ctor_get(x_47, 2);
lean_inc(x_104);
lean_dec(x_47);
x_105 = l_Array_zip___rarg(x_104, x_45);
lean_dec(x_45);
lean_dec(x_104);
x_106 = lean_array_get_size(x_105);
x_107 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_108 = 0;
x_109 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__11(x_105, x_107, x_108, x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_105);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_st_ref_take(x_3, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_RBNode_insert___at_Lean_FVarIdMap_insert___spec__1___rarg(x_113, x_44, x_110);
x_116 = lean_st_ref_set(x_3, x_115, x_114);
lean_dec(x_3);
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_116, 0);
lean_dec(x_118);
x_119 = lean_box(0);
lean_ctor_set(x_116, 0, x_119);
return x_116;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_116, 1);
lean_inc(x_120);
lean_dec(x_116);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_46);
if (x_123 == 0)
{
return x_46;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_46, 0);
x_125 = lean_ctor_get(x_46, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_46);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
case 4:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_127 = lean_ctor_get(x_1, 0);
lean_inc(x_127);
lean_dec(x_1);
x_128 = lean_ctor_get(x_127, 3);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_array_get_size(x_128);
x_130 = lean_unsigned_to_nat(0u);
x_131 = lean_nat_dec_lt(x_130, x_129);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_9);
return x_133;
}
else
{
uint8_t x_134; 
x_134 = lean_nat_dec_le(x_129, x_129);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_9);
return x_136;
}
else
{
size_t x_137; size_t x_138; lean_object* x_139; lean_object* x_140; 
x_137 = 0;
x_138 = lean_usize_of_nat(x_129);
lean_dec(x_129);
x_139 = lean_box(0);
x_140 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__14(x_128, x_137, x_138, x_139, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_128);
return x_140;
}
}
}
default: 
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_9);
return x_142;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_ReaderT_pure___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___spec__5(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__7(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__8(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_erase___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_erase___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__10(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_erase___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_HashMapImp_erase___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__9(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__11(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__14(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT uint8_t l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1674_(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Lean_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__2___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_uget(x_2, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__1(x_1, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_box(0);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__2___lambda__1(x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; size_t x_21; size_t x_22; 
lean_dec(x_13);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_11 = x_20;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_array_push(x_5, x_13);
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
x_5 = x_25;
x_11 = x_24;
goto _start;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = l_Lean_Compiler_LCNF_eraseParam(x_13, x_7, x_8, x_9, x_10, x_11);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__2___lambda__1(x_15, x_30, x_6, x_7, x_8, x_9, x_10, x_31);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; 
lean_dec(x_13);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = 1;
x_37 = lean_usize_add(x_3, x_36);
x_3 = x_37;
x_11 = x_35;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; 
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_array_push(x_5, x_13);
x_41 = 1;
x_42 = lean_usize_add(x_3, x_41);
x_3 = x_42;
x_5 = x_40;
x_11 = x_39;
goto _start;
}
}
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_11);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; uint8_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__1(x_1, x_9);
lean_dec(x_9);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_7);
x_3 = x_11;
x_5 = x_13;
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_mapCodeM___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Compiler_LCNF_AltCore_getCode(x_1);
x_10 = lean_apply_7(x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_12);
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
x_16 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__7(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__7___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Compiler_LCNF_AltCore_mapCodeM___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__6(x_12, x_15, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_14, x_2, x_17);
x_2 = x_20;
x_3 = x_21;
x_9 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_1, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_2);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_2, x_6, x_3, x_4, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; size_t x_19; size_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_20 = lean_ptr_addr(x_14);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_2);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_24 = lean_ptr_addr(x_18);
x_25 = lean_usize_dec_eq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_5);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_14);
lean_ctor_set(x_16, 0, x_26);
return x_16;
}
else
{
lean_dec(x_18);
lean_dec(x_14);
lean_ctor_set(x_16, 0, x_5);
return x_16;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_30 = lean_ptr_addr(x_14);
x_31 = lean_usize_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_dec(x_2);
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_14);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
else
{
size_t x_34; size_t x_35; uint8_t x_36; 
x_34 = lean_ptr_addr(x_2);
lean_dec(x_2);
x_35 = lean_ptr_addr(x_27);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_5);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_14);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_28);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_27);
lean_dec(x_14);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_28);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
return x_13;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Basic", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateJmpImp", 67);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__3;
x_2 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__4;
x_3 = lean_unsigned_to_nat(316u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_9);
x_10 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_14 = lean_ptr_addr(x_12);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
}
else
{
size_t x_20; uint8_t x_21; 
x_20 = lean_ptr_addr(x_8);
x_21 = lean_usize_dec_eq(x_20, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_10, 0, x_25);
return x_10;
}
}
else
{
lean_dec(x_12);
lean_dec(x_8);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_29 = lean_ptr_addr(x_26);
x_30 = lean_usize_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_31 = x_1;
} else {
 lean_dec_ref(x_1);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
else
{
size_t x_34; uint8_t x_35; 
x_34 = lean_ptr_addr(x_8);
x_35 = lean_usize_dec_eq(x_34, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_36 = x_1;
} else {
 lean_dec_ref(x_1);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_26);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_27);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_26);
lean_dec(x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
case 1:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 4);
lean_inc(x_46);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_47 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_46, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_44, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 2);
lean_inc(x_51);
lean_inc(x_44);
x_52 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(x_44, x_50, x_51, x_48, x_3, x_4, x_5, x_6, x_49);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_45);
x_55 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_45, x_2, x_3, x_4, x_5, x_6, x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; size_t x_58; size_t x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ptr_addr(x_45);
lean_dec(x_45);
x_59 = lean_ptr_addr(x_57);
x_60 = lean_usize_dec_eq(x_58, x_59);
if (x_60 == 0)
{
uint8_t x_61; 
lean_dec(x_44);
x_61 = !lean_is_exclusive(x_1);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_1, 1);
lean_dec(x_62);
x_63 = lean_ctor_get(x_1, 0);
lean_dec(x_63);
lean_ctor_set(x_1, 1, x_57);
lean_ctor_set(x_1, 0, x_53);
lean_ctor_set(x_55, 0, x_1);
return x_55;
}
else
{
lean_object* x_64; 
lean_dec(x_1);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_57);
lean_ctor_set(x_55, 0, x_64);
return x_55;
}
}
else
{
size_t x_65; size_t x_66; uint8_t x_67; 
x_65 = lean_ptr_addr(x_44);
lean_dec(x_44);
x_66 = lean_ptr_addr(x_53);
x_67 = lean_usize_dec_eq(x_65, x_66);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_1);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_1, 1);
lean_dec(x_69);
x_70 = lean_ctor_get(x_1, 0);
lean_dec(x_70);
lean_ctor_set(x_1, 1, x_57);
lean_ctor_set(x_1, 0, x_53);
lean_ctor_set(x_55, 0, x_1);
return x_55;
}
else
{
lean_object* x_71; 
lean_dec(x_1);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_53);
lean_ctor_set(x_71, 1, x_57);
lean_ctor_set(x_55, 0, x_71);
return x_55;
}
}
else
{
lean_dec(x_57);
lean_dec(x_53);
lean_ctor_set(x_55, 0, x_1);
return x_55;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_55, 0);
x_73 = lean_ctor_get(x_55, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_55);
x_74 = lean_ptr_addr(x_45);
lean_dec(x_45);
x_75 = lean_ptr_addr(x_72);
x_76 = lean_usize_dec_eq(x_74, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_44);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_77 = x_1;
} else {
 lean_dec_ref(x_1);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_53);
lean_ctor_set(x_78, 1, x_72);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_73);
return x_79;
}
else
{
size_t x_80; size_t x_81; uint8_t x_82; 
x_80 = lean_ptr_addr(x_44);
lean_dec(x_44);
x_81 = lean_ptr_addr(x_53);
x_82 = lean_usize_dec_eq(x_80, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_83 = x_1;
} else {
 lean_dec_ref(x_1);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_53);
lean_ctor_set(x_84, 1, x_72);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_73);
return x_85;
}
else
{
lean_object* x_86; 
lean_dec(x_72);
lean_dec(x_53);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_73);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_53);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_55);
if (x_87 == 0)
{
return x_55;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_55, 0);
x_89 = lean_ctor_get(x_55, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_55);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_47);
if (x_91 == 0)
{
return x_47;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_47, 0);
x_93 = lean_ctor_get(x_47, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_47);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
case 2:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_1, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__1(x_2, x_97);
lean_dec(x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
lean_inc(x_96);
x_99 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_96, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; size_t x_102; size_t x_103; uint8_t x_104; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ptr_addr(x_96);
lean_dec(x_96);
x_103 = lean_ptr_addr(x_101);
x_104 = lean_usize_dec_eq(x_102, x_103);
if (x_104 == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_1);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_1, 1);
lean_dec(x_106);
x_107 = lean_ctor_get(x_1, 0);
lean_dec(x_107);
lean_ctor_set(x_1, 1, x_101);
lean_ctor_set(x_99, 0, x_1);
return x_99;
}
else
{
lean_object* x_108; 
lean_dec(x_1);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_95);
lean_ctor_set(x_108, 1, x_101);
lean_ctor_set(x_99, 0, x_108);
return x_99;
}
}
else
{
size_t x_109; uint8_t x_110; 
x_109 = lean_ptr_addr(x_95);
x_110 = lean_usize_dec_eq(x_109, x_109);
if (x_110 == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_1);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_1, 1);
lean_dec(x_112);
x_113 = lean_ctor_get(x_1, 0);
lean_dec(x_113);
lean_ctor_set(x_1, 1, x_101);
lean_ctor_set(x_99, 0, x_1);
return x_99;
}
else
{
lean_object* x_114; 
lean_dec(x_1);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_95);
lean_ctor_set(x_114, 1, x_101);
lean_ctor_set(x_99, 0, x_114);
return x_99;
}
}
else
{
lean_dec(x_101);
lean_dec(x_95);
lean_ctor_set(x_99, 0, x_1);
return x_99;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; size_t x_117; size_t x_118; uint8_t x_119; 
x_115 = lean_ctor_get(x_99, 0);
x_116 = lean_ctor_get(x_99, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_99);
x_117 = lean_ptr_addr(x_96);
lean_dec(x_96);
x_118 = lean_ptr_addr(x_115);
x_119 = lean_usize_dec_eq(x_117, x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_120 = x_1;
} else {
 lean_dec_ref(x_1);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(2, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_95);
lean_ctor_set(x_121, 1, x_115);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_116);
return x_122;
}
else
{
size_t x_123; uint8_t x_124; 
x_123 = lean_ptr_addr(x_95);
x_124 = lean_usize_dec_eq(x_123, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_125 = x_1;
} else {
 lean_dec_ref(x_1);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(2, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_95);
lean_ctor_set(x_126, 1, x_115);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_116);
return x_127;
}
else
{
lean_object* x_128; 
lean_dec(x_115);
lean_dec(x_95);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_1);
lean_ctor_set(x_128, 1, x_116);
return x_128;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_99);
if (x_129 == 0)
{
return x_99;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_99, 0);
x_131 = lean_ctor_get(x_99, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_99);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_133 = lean_ctor_get(x_98, 0);
lean_inc(x_133);
lean_dec(x_98);
x_134 = lean_ctor_get(x_95, 2);
lean_inc(x_134);
x_135 = lean_array_get_size(x_134);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_nat_dec_lt(x_136, x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_134);
x_138 = lean_ctor_get(x_95, 4);
lean_inc(x_138);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_139 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_138, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_143 = l_Lean_Compiler_LCNF_normCodeImp(x_142, x_140, x_133, x_3, x_4, x_5, x_6, x_141);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__2;
x_147 = lean_nat_dec_eq(x_146, x_135);
lean_dec(x_135);
if (x_147 == 0)
{
lean_object* x_148; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_144);
x_148 = l_Lean_Compiler_LCNF_Code_inferType(x_144, x_3, x_4, x_5, x_6, x_145);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_152 = l_Lean_Compiler_LCNF_mkForallParams(x_151, x_149, x_3, x_4, x_5, x_6, x_150);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___lambda__1(x_96, x_95, x_151, x_144, x_1, x_153, x_2, x_3, x_4, x_5, x_6, x_154);
return x_155;
}
else
{
uint8_t x_156; 
lean_dec(x_144);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_152);
if (x_156 == 0)
{
return x_152;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_152, 0);
x_158 = lean_ctor_get(x_152, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_152);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_144);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = !lean_is_exclusive(x_148);
if (x_160 == 0)
{
return x_148;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_148, 0);
x_162 = lean_ctor_get(x_148, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_148);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_95, 3);
lean_inc(x_164);
x_165 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
x_166 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___lambda__1(x_96, x_95, x_165, x_144, x_1, x_164, x_2, x_3, x_4, x_5, x_6, x_145);
return x_166;
}
}
else
{
uint8_t x_167; 
lean_dec(x_135);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_143);
if (x_167 == 0)
{
return x_143;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_143, 0);
x_169 = lean_ctor_get(x_143, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_143);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_139);
if (x_171 == 0)
{
return x_139;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_139, 0);
x_173 = lean_ctor_get(x_139, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_139);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
else
{
uint8_t x_175; 
x_175 = lean_nat_dec_le(x_135, x_135);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_134);
x_176 = lean_ctor_get(x_95, 4);
lean_inc(x_176);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_177 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_176, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_181 = l_Lean_Compiler_LCNF_normCodeImp(x_180, x_178, x_133, x_3, x_4, x_5, x_6, x_179);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__2;
x_185 = lean_nat_dec_eq(x_184, x_135);
lean_dec(x_135);
if (x_185 == 0)
{
lean_object* x_186; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_182);
x_186 = l_Lean_Compiler_LCNF_Code_inferType(x_182, x_3, x_4, x_5, x_6, x_183);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_190 = l_Lean_Compiler_LCNF_mkForallParams(x_189, x_187, x_3, x_4, x_5, x_6, x_188);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___lambda__1(x_96, x_95, x_189, x_182, x_1, x_191, x_2, x_3, x_4, x_5, x_6, x_192);
return x_193;
}
else
{
uint8_t x_194; 
lean_dec(x_182);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = !lean_is_exclusive(x_190);
if (x_194 == 0)
{
return x_190;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_190, 0);
x_196 = lean_ctor_get(x_190, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_190);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_182);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_186);
if (x_198 == 0)
{
return x_186;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_186, 0);
x_200 = lean_ctor_get(x_186, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_186);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_95, 3);
lean_inc(x_202);
x_203 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
x_204 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___lambda__1(x_96, x_95, x_203, x_182, x_1, x_202, x_2, x_3, x_4, x_5, x_6, x_183);
return x_204;
}
}
else
{
uint8_t x_205; 
lean_dec(x_135);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_205 = !lean_is_exclusive(x_181);
if (x_205 == 0)
{
return x_181;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_181, 0);
x_207 = lean_ctor_get(x_181, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_181);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = !lean_is_exclusive(x_177);
if (x_209 == 0)
{
return x_177;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_177, 0);
x_211 = lean_ctor_get(x_177, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_177);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
else
{
size_t x_213; size_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_213 = 0;
x_214 = lean_usize_of_nat(x_135);
x_215 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
x_216 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__2(x_133, x_134, x_213, x_214, x_215, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_134);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_ctor_get(x_95, 4);
lean_inc(x_219);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_220 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_219, x_2, x_3, x_4, x_5, x_6, x_218);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_224 = l_Lean_Compiler_LCNF_normCodeImp(x_223, x_221, x_133, x_3, x_4, x_5, x_6, x_222);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_array_get_size(x_217);
x_228 = lean_nat_dec_eq(x_227, x_135);
lean_dec(x_135);
lean_dec(x_227);
if (x_228 == 0)
{
lean_object* x_229; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_225);
x_229 = l_Lean_Compiler_LCNF_Code_inferType(x_225, x_3, x_4, x_5, x_6, x_226);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_217);
x_232 = l_Lean_Compiler_LCNF_mkForallParams(x_217, x_230, x_3, x_4, x_5, x_6, x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___lambda__1(x_96, x_95, x_217, x_225, x_1, x_233, x_2, x_3, x_4, x_5, x_6, x_234);
return x_235;
}
else
{
uint8_t x_236; 
lean_dec(x_225);
lean_dec(x_217);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_236 = !lean_is_exclusive(x_232);
if (x_236 == 0)
{
return x_232;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_232, 0);
x_238 = lean_ctor_get(x_232, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_232);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
else
{
uint8_t x_240; 
lean_dec(x_225);
lean_dec(x_217);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_240 = !lean_is_exclusive(x_229);
if (x_240 == 0)
{
return x_229;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_229, 0);
x_242 = lean_ctor_get(x_229, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_229);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_95, 3);
lean_inc(x_244);
x_245 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___lambda__1(x_96, x_95, x_217, x_225, x_1, x_244, x_2, x_3, x_4, x_5, x_6, x_226);
return x_245;
}
}
else
{
uint8_t x_246; 
lean_dec(x_217);
lean_dec(x_135);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_246 = !lean_is_exclusive(x_224);
if (x_246 == 0)
{
return x_224;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_224, 0);
x_248 = lean_ctor_get(x_224, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_224);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_217);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_220);
if (x_250 == 0)
{
return x_220;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_220, 0);
x_252 = lean_ctor_get(x_220, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_220);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
}
}
}
case 3:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_300; lean_object* x_301; 
x_254 = lean_ctor_get(x_1, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_1, 1);
lean_inc(x_255);
lean_inc(x_254);
x_300 = l_Lean_Compiler_LCNF_getFunDecl(x_254, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_301 = l_Lean_RBNode_find___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__1(x_2, x_254);
lean_dec(x_2);
if (lean_obj_tag(x_301) == 0)
{
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_302 = lean_ctor_get(x_300, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_300, 1);
lean_inc(x_303);
lean_dec(x_300);
x_304 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__3;
x_305 = l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__5(x_304);
x_256 = x_305;
x_257 = x_302;
x_258 = x_303;
goto block_299;
}
else
{
uint8_t x_306; 
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_300);
if (x_306 == 0)
{
return x_300;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_300, 0);
x_308 = lean_ctor_get(x_300, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_300);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
else
{
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_301, 0);
lean_inc(x_310);
lean_dec(x_301);
x_311 = lean_ctor_get(x_300, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_300, 1);
lean_inc(x_312);
lean_dec(x_300);
x_256 = x_310;
x_257 = x_311;
x_258 = x_312;
goto block_299;
}
else
{
uint8_t x_313; 
lean_dec(x_301);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_1);
x_313 = !lean_is_exclusive(x_300);
if (x_313 == 0)
{
return x_300;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_300, 0);
x_315 = lean_ctor_get(x_300, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_300);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
}
}
block_299:
{
lean_object* x_259; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_287 = lean_ctor_get(x_257, 2);
lean_inc(x_287);
lean_dec(x_257);
x_288 = l_Array_zip___rarg(x_287, x_255);
lean_dec(x_255);
lean_dec(x_287);
x_289 = lean_array_get_size(x_288);
x_290 = lean_unsigned_to_nat(0u);
x_291 = lean_nat_dec_lt(x_290, x_289);
if (x_291 == 0)
{
lean_object* x_292; 
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_256);
x_292 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
x_259 = x_292;
goto block_286;
}
else
{
uint8_t x_293; 
x_293 = lean_nat_dec_le(x_289, x_289);
if (x_293 == 0)
{
lean_object* x_294; 
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_256);
x_294 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
x_259 = x_294;
goto block_286;
}
else
{
size_t x_295; size_t x_296; lean_object* x_297; lean_object* x_298; 
x_295 = 0;
x_296 = lean_usize_of_nat(x_289);
lean_dec(x_289);
x_297 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
x_298 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__4(x_256, x_288, x_295, x_296, x_297);
lean_dec(x_288);
lean_dec(x_256);
x_259 = x_298;
goto block_286;
}
}
block_286:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; size_t x_263; size_t x_264; lean_object* x_265; uint8_t x_266; 
x_260 = lean_ctor_get(x_1, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_1, 1);
lean_inc(x_261);
x_262 = lean_array_get_size(x_259);
x_263 = lean_usize_of_nat(x_262);
lean_dec(x_262);
x_264 = 0;
x_265 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__3(x_263, x_264, x_259);
x_266 = lean_name_eq(x_260, x_254);
lean_dec(x_260);
if (x_266 == 0)
{
uint8_t x_267; 
lean_dec(x_261);
x_267 = !lean_is_exclusive(x_1);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_1, 1);
lean_dec(x_268);
x_269 = lean_ctor_get(x_1, 0);
lean_dec(x_269);
lean_ctor_set(x_1, 1, x_265);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_1);
lean_ctor_set(x_270, 1, x_258);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_1);
x_271 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_271, 0, x_254);
lean_ctor_set(x_271, 1, x_265);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_258);
return x_272;
}
}
else
{
size_t x_273; size_t x_274; uint8_t x_275; 
x_273 = lean_ptr_addr(x_261);
lean_dec(x_261);
x_274 = lean_ptr_addr(x_265);
x_275 = lean_usize_dec_eq(x_273, x_274);
if (x_275 == 0)
{
uint8_t x_276; 
x_276 = !lean_is_exclusive(x_1);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_1, 1);
lean_dec(x_277);
x_278 = lean_ctor_get(x_1, 0);
lean_dec(x_278);
lean_ctor_set(x_1, 1, x_265);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_1);
lean_ctor_set(x_279, 1, x_258);
return x_279;
}
else
{
lean_object* x_280; lean_object* x_281; 
lean_dec(x_1);
x_280 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_280, 0, x_254);
lean_ctor_set(x_280, 1, x_265);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_258);
return x_281;
}
}
else
{
lean_object* x_282; 
lean_dec(x_265);
lean_dec(x_254);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_1);
lean_ctor_set(x_282, 1, x_258);
return x_282;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_259);
lean_dec(x_254);
lean_dec(x_1);
x_283 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__5;
x_284 = l_panic___at___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltsImp___spec__1(x_283);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_258);
return x_285;
}
}
}
}
case 4:
{
lean_object* x_317; uint8_t x_318; 
x_317 = lean_ctor_get(x_1, 0);
lean_inc(x_317);
x_318 = !lean_is_exclusive(x_317);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; size_t x_324; size_t x_325; lean_object* x_326; 
x_319 = lean_ctor_get(x_317, 0);
x_320 = lean_ctor_get(x_317, 1);
x_321 = lean_ctor_get(x_317, 2);
x_322 = lean_ctor_get(x_317, 3);
x_323 = lean_array_get_size(x_322);
x_324 = lean_usize_of_nat(x_323);
lean_dec(x_323);
x_325 = 0;
lean_inc(x_322);
x_326 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__7(x_324, x_325, x_322, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_326) == 0)
{
uint8_t x_327; 
x_327 = !lean_is_exclusive(x_326);
if (x_327 == 0)
{
lean_object* x_328; size_t x_329; size_t x_330; uint8_t x_331; 
x_328 = lean_ctor_get(x_326, 0);
x_329 = lean_ptr_addr(x_322);
lean_dec(x_322);
x_330 = lean_ptr_addr(x_328);
x_331 = lean_usize_dec_eq(x_329, x_330);
if (x_331 == 0)
{
uint8_t x_332; 
x_332 = !lean_is_exclusive(x_1);
if (x_332 == 0)
{
lean_object* x_333; 
x_333 = lean_ctor_get(x_1, 0);
lean_dec(x_333);
lean_ctor_set(x_317, 3, x_328);
lean_ctor_set(x_326, 0, x_1);
return x_326;
}
else
{
lean_object* x_334; 
lean_dec(x_1);
lean_ctor_set(x_317, 3, x_328);
x_334 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_334, 0, x_317);
lean_ctor_set(x_326, 0, x_334);
return x_326;
}
}
else
{
size_t x_335; uint8_t x_336; 
x_335 = lean_ptr_addr(x_320);
x_336 = lean_usize_dec_eq(x_335, x_335);
if (x_336 == 0)
{
uint8_t x_337; 
x_337 = !lean_is_exclusive(x_1);
if (x_337 == 0)
{
lean_object* x_338; 
x_338 = lean_ctor_get(x_1, 0);
lean_dec(x_338);
lean_ctor_set(x_317, 3, x_328);
lean_ctor_set(x_326, 0, x_1);
return x_326;
}
else
{
lean_object* x_339; 
lean_dec(x_1);
lean_ctor_set(x_317, 3, x_328);
x_339 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_339, 0, x_317);
lean_ctor_set(x_326, 0, x_339);
return x_326;
}
}
else
{
uint8_t x_340; 
x_340 = lean_name_eq(x_321, x_321);
if (x_340 == 0)
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_1);
if (x_341 == 0)
{
lean_object* x_342; 
x_342 = lean_ctor_get(x_1, 0);
lean_dec(x_342);
lean_ctor_set(x_317, 3, x_328);
lean_ctor_set(x_326, 0, x_1);
return x_326;
}
else
{
lean_object* x_343; 
lean_dec(x_1);
lean_ctor_set(x_317, 3, x_328);
x_343 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_343, 0, x_317);
lean_ctor_set(x_326, 0, x_343);
return x_326;
}
}
else
{
lean_dec(x_328);
lean_free_object(x_317);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_ctor_set(x_326, 0, x_1);
return x_326;
}
}
}
}
else
{
lean_object* x_344; lean_object* x_345; size_t x_346; size_t x_347; uint8_t x_348; 
x_344 = lean_ctor_get(x_326, 0);
x_345 = lean_ctor_get(x_326, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_326);
x_346 = lean_ptr_addr(x_322);
lean_dec(x_322);
x_347 = lean_ptr_addr(x_344);
x_348 = lean_usize_dec_eq(x_346, x_347);
if (x_348 == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_349 = x_1;
} else {
 lean_dec_ref(x_1);
 x_349 = lean_box(0);
}
lean_ctor_set(x_317, 3, x_344);
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(4, 1, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_317);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_345);
return x_351;
}
else
{
size_t x_352; uint8_t x_353; 
x_352 = lean_ptr_addr(x_320);
x_353 = lean_usize_dec_eq(x_352, x_352);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_354 = x_1;
} else {
 lean_dec_ref(x_1);
 x_354 = lean_box(0);
}
lean_ctor_set(x_317, 3, x_344);
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(4, 1, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_317);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_345);
return x_356;
}
else
{
uint8_t x_357; 
x_357 = lean_name_eq(x_321, x_321);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_358 = x_1;
} else {
 lean_dec_ref(x_1);
 x_358 = lean_box(0);
}
lean_ctor_set(x_317, 3, x_344);
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(4, 1, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_317);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_345);
return x_360;
}
else
{
lean_object* x_361; 
lean_dec(x_344);
lean_free_object(x_317);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_1);
lean_ctor_set(x_361, 1, x_345);
return x_361;
}
}
}
}
}
else
{
uint8_t x_362; 
lean_free_object(x_317);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_1);
x_362 = !lean_is_exclusive(x_326);
if (x_362 == 0)
{
return x_326;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_326, 0);
x_364 = lean_ctor_get(x_326, 1);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_326);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
return x_365;
}
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; size_t x_371; size_t x_372; lean_object* x_373; 
x_366 = lean_ctor_get(x_317, 0);
x_367 = lean_ctor_get(x_317, 1);
x_368 = lean_ctor_get(x_317, 2);
x_369 = lean_ctor_get(x_317, 3);
lean_inc(x_369);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_317);
x_370 = lean_array_get_size(x_369);
x_371 = lean_usize_of_nat(x_370);
lean_dec(x_370);
x_372 = 0;
lean_inc(x_369);
x_373 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__7(x_371, x_372, x_369, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; size_t x_377; size_t x_378; uint8_t x_379; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_376 = x_373;
} else {
 lean_dec_ref(x_373);
 x_376 = lean_box(0);
}
x_377 = lean_ptr_addr(x_369);
lean_dec(x_369);
x_378 = lean_ptr_addr(x_374);
x_379 = lean_usize_dec_eq(x_377, x_378);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_380 = x_1;
} else {
 lean_dec_ref(x_1);
 x_380 = lean_box(0);
}
x_381 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_381, 0, x_366);
lean_ctor_set(x_381, 1, x_367);
lean_ctor_set(x_381, 2, x_368);
lean_ctor_set(x_381, 3, x_374);
if (lean_is_scalar(x_380)) {
 x_382 = lean_alloc_ctor(4, 1, 0);
} else {
 x_382 = x_380;
}
lean_ctor_set(x_382, 0, x_381);
if (lean_is_scalar(x_376)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_376;
}
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_375);
return x_383;
}
else
{
size_t x_384; uint8_t x_385; 
x_384 = lean_ptr_addr(x_367);
x_385 = lean_usize_dec_eq(x_384, x_384);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_386 = x_1;
} else {
 lean_dec_ref(x_1);
 x_386 = lean_box(0);
}
x_387 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_387, 0, x_366);
lean_ctor_set(x_387, 1, x_367);
lean_ctor_set(x_387, 2, x_368);
lean_ctor_set(x_387, 3, x_374);
if (lean_is_scalar(x_386)) {
 x_388 = lean_alloc_ctor(4, 1, 0);
} else {
 x_388 = x_386;
}
lean_ctor_set(x_388, 0, x_387);
if (lean_is_scalar(x_376)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_376;
}
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_375);
return x_389;
}
else
{
uint8_t x_390; 
x_390 = lean_name_eq(x_368, x_368);
if (x_390 == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_391 = x_1;
} else {
 lean_dec_ref(x_1);
 x_391 = lean_box(0);
}
x_392 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_392, 0, x_366);
lean_ctor_set(x_392, 1, x_367);
lean_ctor_set(x_392, 2, x_368);
lean_ctor_set(x_392, 3, x_374);
if (lean_is_scalar(x_391)) {
 x_393 = lean_alloc_ctor(4, 1, 0);
} else {
 x_393 = x_391;
}
lean_ctor_set(x_393, 0, x_392);
if (lean_is_scalar(x_376)) {
 x_394 = lean_alloc_ctor(0, 2, 0);
} else {
 x_394 = x_376;
}
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_375);
return x_394;
}
else
{
lean_object* x_395; 
lean_dec(x_374);
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_366);
if (lean_is_scalar(x_376)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_376;
}
lean_ctor_set(x_395, 0, x_1);
lean_ctor_set(x_395, 1, x_375);
return x_395;
}
}
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_1);
x_396 = lean_ctor_get(x_373, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_373, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_398 = x_373;
} else {
 lean_dec_ref(x_373);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
}
}
default: 
{
lean_object* x_400; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_1);
lean_ctor_set(x_400, 1, x_7);
return x_400;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_HashMapImp_contains___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__2___lambda__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__2(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__4(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__7(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_ctor_get(x_1, 5);
x_14 = lean_box(0);
x_15 = lean_st_mk_ref(x_14, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_mk_ref(x_14, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_16);
lean_inc(x_19);
lean_inc(x_12);
x_21 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze(x_12, x_14, x_19, x_16, x_2, x_3, x_4, x_5, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_19, x_22);
lean_dec(x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_16, x_25);
lean_dec(x_16);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_12, x_24, x_2, x_3, x_4, x_5, x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_ctor_set(x_1, 4, x_30);
lean_ctor_set(x_28, 0, x_1);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set(x_1, 4, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
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
lean_dec(x_19);
lean_dec(x_16);
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
return x_21;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_21, 0);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_21);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_ctor_get(x_1, 2);
x_45 = lean_ctor_get(x_1, 3);
x_46 = lean_ctor_get(x_1, 4);
x_47 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_48 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_49 = lean_ctor_get(x_1, 5);
lean_inc(x_49);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_st_mk_ref(x_50, x_6);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_st_mk_ref(x_50, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_52);
lean_inc(x_55);
lean_inc(x_46);
x_57 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze(x_46, x_50, x_55, x_52, x_2, x_3, x_4, x_5, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_st_ref_get(x_55, x_58);
lean_dec(x_55);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_st_ref_get(x_52, x_61);
lean_dec(x_52);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce(x_46, x_60, x_2, x_3, x_4, x_5, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_68, 0, x_42);
lean_ctor_set(x_68, 1, x_43);
lean_ctor_set(x_68, 2, x_44);
lean_ctor_set(x_68, 3, x_45);
lean_ctor_set(x_68, 4, x_65);
lean_ctor_set(x_68, 5, x_49);
lean_ctor_set_uint8(x_68, sizeof(void*)*6, x_47);
lean_ctor_set_uint8(x_68, sizeof(void*)*6 + 1, x_48);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_49);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_72 = x_64;
} else {
 lean_dec_ref(x_64);
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
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_ctor_get(x_57, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_57, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_76 = x_57;
} else {
 lean_dec_ref(x_57);
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
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__1___closed__1;
x_8 = lean_st_ref_get(x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_4, 2);
x_12 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_10, x_11, x_1);
lean_dec(x_10);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_ctor_get(x_4, 2);
x_17 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_14, x_16, x_1);
lean_dec(x_14);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__3;
x_3 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__4;
x_4 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__5;
x_5 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_2);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_4, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16);
x_18 = lean_ctor_get(x_5, 2);
x_19 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__6;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_2);
x_22 = lean_st_ref_take(x_6, x_15);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_26 = lean_ctor_get(x_23, 3);
x_27 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
x_28 = 0;
x_29 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_28);
lean_inc(x_8);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_PersistentArray_push___rarg(x_26, x_30);
lean_ctor_set(x_23, 3, x_31);
x_32 = lean_st_ref_set(x_6, x_23, x_24);
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
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
x_41 = lean_ctor_get(x_23, 2);
x_42 = lean_ctor_get(x_23, 3);
x_43 = lean_ctor_get(x_23, 4);
x_44 = lean_ctor_get(x_23, 5);
x_45 = lean_ctor_get(x_23, 6);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
x_46 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
x_47 = 0;
x_48 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_21);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_47);
lean_inc(x_8);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_8);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_PersistentArray_push___rarg(x_42, x_49);
x_51 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_40);
lean_ctor_set(x_51, 2, x_41);
lean_ctor_set(x_51, 3, x_50);
lean_ctor_set(x_51, 4, x_43);
lean_ctor_set(x_51, 5, x_44);
lean_ctor_set(x_51, 6, x_45);
x_52 = lean_st_ref_set(x_6, x_51, x_24);
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
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_findJoinPoints___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_JoinPointFinder_replace(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("findJoinPoints", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__1;
x_2 = l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Found: ", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" jp candidates", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_findJoinPoints(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_JoinPointFinder_find(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__3;
x_11 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__1(x_10, x_2, x_3, x_4, x_5, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Compiler_LCNF_JoinPointFinder_replace(x_1, x_8, x_2, x_3, x_4, x_5, x_14);
lean_dec(x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Nat_repr(x_18);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__5;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__7;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2(x_10, x_25, x_2, x_3, x_4, x_5, x_17);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Compiler_LCNF_JoinPointFinder_replace(x_1, x_8, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_8);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_7);
if (x_29 == 0)
{
return x_7;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_7, 0);
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_7);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_findJoinPoints___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Decl_findJoinPoints___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_findJoinPoints___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_findJoinPoints___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_findJoinPoints), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_findJoinPoints___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_findJoinPoints___closed__1;
x_2 = l_Lean_Compiler_LCNF_findJoinPoints___closed__2;
x_3 = 0;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_findJoinPoints() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_findJoinPoints___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__2;
x_2 = l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LCNF", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__3;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__5;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__7;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__9;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__10;
x_2 = l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__11;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("JoinPoints", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__12;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__14;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__16;
x_2 = lean_unsigned_to_nat(4913u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__3;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__17;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_extendJoinPointContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_JoinPointContextExtender_extend(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticSeq", 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__1;
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__1;
x_3 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__2;
x_4 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticSeq1Indented", 18);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__1;
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__1;
x_3 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__2;
x_4 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__1;
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__1;
x_3 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__2;
x_4 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__9;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__9;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__8;
x_3 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__12;
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__14;
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__15;
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__16;
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__17;
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__10;
x_3 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__18;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__19;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__8;
x_3 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__20;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__21;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__6;
x_3 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__22;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1;
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__23;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__4;
x_3 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__24;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__25;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extendJoinPointContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("extendJoinPointContext", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extendJoinPointContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_extendJoinPointContext___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_extendJoinPointContext___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_extendJoinPointContext), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Compiler_LCNF_extendJoinPointContext___closed__2;
x_5 = l_Lean_Compiler_LCNF_extendJoinPointContext___closed__3;
x_6 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_4, x_5, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_extendJoinPointContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Compiler_LCNF_extendJoinPointContext(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5041____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__1;
x_2 = l_Lean_Compiler_LCNF_extendJoinPointContext___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5041____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__16;
x_2 = lean_unsigned_to_nat(5041u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5041_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5041____closed__1;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5041____closed__2;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_commonJoinPointArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("commonJoinPointArgs", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_commonJoinPointArgs), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__2;
x_2 = l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__3;
x_3 = 1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_commonJoinPointArgs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5107____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__1;
x_2 = l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5107____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__16;
x_2 = lean_unsigned_to_nat(5107u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5107_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5107____closed__1;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5107____closed__2;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PullFunDecls(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ScopeM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_JoinPoints(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PullFunDecls(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_FVarUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ScopeM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_JoinPointFinder_instInhabitedCandidateInfo = _init_l_Lean_Compiler_LCNF_JoinPointFinder_instInhabitedCandidateInfo();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointFinder_instInhabitedCandidateInfo);
l_Lean_Compiler_LCNF_JoinPointFinder_FindState_candidates___default = _init_l_Lean_Compiler_LCNF_JoinPointFinder_FindState_candidates___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointFinder_FindState_candidates___default);
l_Lean_Compiler_LCNF_JoinPointFinder_FindState_scope___default___closed__1 = _init_l_Lean_Compiler_LCNF_JoinPointFinder_FindState_scope___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointFinder_FindState_scope___default___closed__1);
l_Lean_Compiler_LCNF_JoinPointFinder_FindState_scope___default = _init_l_Lean_Compiler_LCNF_JoinPointFinder_FindState_scope___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointFinder_FindState_scope___default);
l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__1 = _init_l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__1);
l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__2 = _init_l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__2();
lean_mark_persistent(l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__2);
l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__3 = _init_l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__3();
lean_mark_persistent(l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__3);
l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__4 = _init_l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__4();
lean_mark_persistent(l_panic___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__3___closed__4);
l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__1 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__1);
l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__2 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__2);
l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__3 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__3);
l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__4 = _init_l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_forFVarM___at___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___spec__2___closed__4);
l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___closed__1 = _init_l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_JoinPoints_0__Lean_Compiler_LCNF_JoinPointFinder_removeCandidatesInArg___closed__1);
l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___closed__1 = _init_l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_ScopeM_withNewScope___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__2___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__6___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__6___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointFinder_find_go___spec__6___closed__1);
l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__1 = _init_l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__1);
l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__2 = _init_l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointFinder_find___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__6___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__6___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointFinder_replace_go___spec__6___closed__1);
l_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendContext_currentJp_x3f___default = _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendContext_currentJp_x3f___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendContext_currentJp_x3f___default);
l_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendContext_candidates___default = _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendContext_candidates___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendContext_candidates___default);
l_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendState_fvarMap___default = _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendState_fvarMap___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointContextExtender_ExtendState_fvarMap___default);
l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__1 = _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__1);
l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__2 = _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__2);
l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__3 = _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__3);
l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__4 = _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointContextExtender_replaceFVar___closed__4);
l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___rarg___closed__1 = _init_l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___rarg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointContextExtender_withNewFunScope___rarg___closed__1);
l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__4___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__4___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__4___closed__1);
l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3___closed__1 = _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3___closed__1);
l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3___closed__2 = _init_l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Expr_mapFVarM___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__3___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__9___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__9___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__9___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__14___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__14___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointContextExtender_extend_go___spec__14___closed__1);
l_Lean_Compiler_LCNF_JoinPointCommonArgs_AnalysisCtx_jpScopes___default = _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_AnalysisCtx_jpScopes___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointCommonArgs_AnalysisCtx_jpScopes___default);
l_Lean_Compiler_LCNF_JoinPointCommonArgs_AnalysisState_jpJmpArgs___default = _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_AnalysisState_jpJmpArgs___default();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointCommonArgs_AnalysisState_jpJmpArgs___default);
l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__1 = _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__1);
l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__2 = _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__2);
l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__3 = _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointCommonArgs_isInJpScope___closed__3);
l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___boxed__const__1 = _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___boxed__const__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyzeFunDecl___boxed__const__1);
l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__3___closed__1 = _init_l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__3___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_allFVarM_go___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__3___closed__1);
l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6___closed__1);
l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__6___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__14___boxed__const__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__14___boxed__const__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goAnalyze___spec__14___boxed__const__1);
l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__7___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__7___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___spec__7___closed__1);
l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1 = _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__1);
l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__2 = _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__2);
l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__3 = _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__3);
l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__4 = _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__4);
l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__5 = _init_l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_JoinPointCommonArgs_reduce_goReduce___closed__5);
l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__1___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__1___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__1___closed__1);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__1 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__1);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__2 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__2);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__3 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__3);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__4 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__4();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__4);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__5 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__5();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__5);
l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__6 = _init_l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__6();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Compiler_LCNF_Decl_findJoinPoints___spec__2___closed__6);
l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__1 = _init_l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__1);
l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__2 = _init_l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__2);
l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__3 = _init_l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__3);
l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__4 = _init_l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__4);
l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__5 = _init_l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__5);
l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__6 = _init_l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__6);
l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__7 = _init_l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_findJoinPoints___closed__7);
l_Lean_Compiler_LCNF_findJoinPoints___closed__1 = _init_l_Lean_Compiler_LCNF_findJoinPoints___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_findJoinPoints___closed__1);
l_Lean_Compiler_LCNF_findJoinPoints___closed__2 = _init_l_Lean_Compiler_LCNF_findJoinPoints___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_findJoinPoints___closed__2);
l_Lean_Compiler_LCNF_findJoinPoints___closed__3 = _init_l_Lean_Compiler_LCNF_findJoinPoints___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_findJoinPoints___closed__3);
l_Lean_Compiler_LCNF_findJoinPoints = _init_l_Lean_Compiler_LCNF_findJoinPoints();
lean_mark_persistent(l_Lean_Compiler_LCNF_findJoinPoints);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__4);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__5 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__5);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__6 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__6);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__7 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__7);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__8 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__8);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__9 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__10 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__10);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__11 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__11);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__12 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__12);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__13 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__13);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__14 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__14);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__15 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__15);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__16 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__16);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__17 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913____closed__17);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4913_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__1 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__1();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__1);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__2 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__2();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__2);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__3 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__3();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__3);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__4 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__4();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__4);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__5 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__5();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__5);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__6 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__6();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__6);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__7 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__7();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__7);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__8 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__8();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__8);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__9 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__9();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__9);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__10 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__10();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__10);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__11 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__11();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__11);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__12 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__12();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__12);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__13 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__13();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__13);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__14 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__14();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__14);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__15 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__15();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__15);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__16 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__16();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__16);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__17 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__17();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__17);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__18 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__18();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__18);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__19 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__19();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__19);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__20 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__20();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__20);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__21 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__21();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__21);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__22 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__22();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__22);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__23 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__23();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__23);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__24 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__24();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__24);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__25 = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__25();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979____closed__25);
l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979_ = _init_l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979_();
lean_mark_persistent(l___auto____x40_Lean_Compiler_LCNF_JoinPoints___hyg_4979_);
l_Lean_Compiler_LCNF_extendJoinPointContext___closed__1 = _init_l_Lean_Compiler_LCNF_extendJoinPointContext___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_extendJoinPointContext___closed__1);
l_Lean_Compiler_LCNF_extendJoinPointContext___closed__2 = _init_l_Lean_Compiler_LCNF_extendJoinPointContext___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_extendJoinPointContext___closed__2);
l_Lean_Compiler_LCNF_extendJoinPointContext___closed__3 = _init_l_Lean_Compiler_LCNF_extendJoinPointContext___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_extendJoinPointContext___closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5041____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5041____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5041____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5041____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5041____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5041____closed__2);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5041_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__1 = _init_l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__1);
l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__2 = _init_l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__2);
l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__3 = _init_l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__3);
l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__4 = _init_l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_commonJoinPointArgs___closed__4);
l_Lean_Compiler_LCNF_commonJoinPointArgs = _init_l_Lean_Compiler_LCNF_commonJoinPointArgs();
lean_mark_persistent(l_Lean_Compiler_LCNF_commonJoinPointArgs);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5107____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5107____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5107____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5107____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5107____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5107____closed__2);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_JoinPoints___hyg_5107_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
