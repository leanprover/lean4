// Lean compiler output
// Module: Lean.Meta.Tactic.Rewrites
// Imports: Lean.Meta.LazyDiscrTree Lean.Meta.Tactic.Assumption Lean.Meta.Tactic.Rewrite Lean.Meta.Tactic.Refl Lean.Meta.Tactic.SolveByElim Lean.Meta.Tactic.TryThis Lean.Util.Heartbeats
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__4;
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_paren(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_findRewrites___closed__0;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites___hyg_46_;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__3;
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_toCtorIdx___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__17____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_localHypotheses___closed__0;
static lean_object* l_Lean_Meta_Rewrites_findRewrites___closed__3;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg(uint8_t, uint8_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__15____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__8____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1;
static lean_object* l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__5;
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getLocalHyps___at___Lean_MVarId_symmSaturate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default;
uint64_t lean_string_hash(lean_object*);
lean_object* l_Option_toLOption___redArg(lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_solveByElim___closed__1;
static lean_object* l_Lean_Meta_Rewrites_solveByElim___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2;
lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma___boxed(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites___hyg_46_;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__11____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__9____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__4;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___Lean_Meta_Rewrites_localHypotheses_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_localHypotheses_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__7;
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5;
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0;
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__6____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5;
lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5_(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__16____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__1;
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t, size_t, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_localHypotheses_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn___lam__0____x40_Lean_Meta_Tactic_Rewrites___hyg_1250_(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__13____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_findRewrites___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg___closed__0;
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__19____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isMetaprogramming(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwFindDecls___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0;
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__18____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46_(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_findRewrites___closed__4;
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7;
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static uint64_t l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__14____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
static lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0;
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__2;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_incPrio(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__0;
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__6;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__12____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
static lean_object* l_Lean_Meta_Rewrites_takeListAux___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeartbeats___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__3;
LEAN_EXPORT lean_object* l_List_elem___at___Lean_Meta_Rewrites_localHypotheses_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1;
lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__0;
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__7____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Rewrites_rwLemma_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites___hyg_46_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_backwardWeight;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__4;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_forwardWeight;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object*);
static lean_object* l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_1250_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx___boxed(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__5;
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__1;
lean_object* l_Lean_Expr_getAppFnArgs(lean_object*);
lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0;
lean_object* l_Lean_getRemainingHeartbeats___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__0;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState;
uint8_t lean_usize_dec_lt(size_t, size_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwFindDecls___closed__1;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__7;
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_droppedKeys;
static lean_object* l_Lean_Meta_Rewrites_initFn___closed__10____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
static lean_object* l_Lean_Meta_Rewrites_findRewrites___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_1190_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_toCtorIdx(uint8_t);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__6;
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rewrites", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_2 = l_Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__6____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_2 = l_Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__7____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Rewrites", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__8____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn___closed__7____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_2 = l_Lean_Meta_Rewrites_initFn___closed__6____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__9____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__10____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn___closed__9____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_2 = l_Lean_Meta_Rewrites_initFn___closed__8____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__11____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__12____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn___closed__11____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_2 = l_Lean_Meta_Rewrites_initFn___closed__10____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__13____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_2 = l_Lean_Meta_Rewrites_initFn___closed__12____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__14____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_2 = l_Lean_Meta_Rewrites_initFn___closed__13____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__15____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_2 = l_Lean_Meta_Rewrites_initFn___closed__14____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__16____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn___closed__7____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_2 = l_Lean_Meta_Rewrites_initFn___closed__15____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__17____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__18____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn___closed__17____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_2 = l_Lean_Meta_Rewrites_initFn___closed__16____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__19____x40_Lean_Meta_Tactic_Rewrites___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = l_Lean_Meta_Rewrites_initFn___closed__18____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_3 = lean_box(0);
x_4 = l_Lean_Meta_Rewrites_initFn___closed__19____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites___hyg_46_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lemmas", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites___hyg_46_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites___hyg_46_;
x_2 = l_Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_3 = l_Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites___hyg_46_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(46u);
x_2 = l_Lean_Meta_Rewrites_initFn___closed__18____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites___hyg_46_;
x_3 = lean_box(0);
x_4 = l_Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites___hyg_46_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteResultLemma___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrArg", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Rewrites_rewriteResultLemma___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1;
x_4 = lean_unsigned_to_nat(6u);
x_5 = l_Lean_Expr_isAppOfArity(x_2, x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_unsigned_to_nat(5u);
x_8 = l_Lean_Expr_getAppNumArgs(x_2);
x_9 = lean_nat_sub(x_8, x_7);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_9, x_10);
lean_dec(x_9);
x_12 = l_Lean_Expr_getRevArg_x21(x_2, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Rewrites_rewriteResultLemma(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_forwardWeight() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_backwardWeight() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_toCtorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Rewrites_RwDirection_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Meta_Rewrites_RwDirection_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Iff", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_getAppFnArgs(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
x_23 = lean_string_dec_eq(x_19, x_22);
lean_dec(x_19);
if (x_23 == 0)
{
lean_free_object(x_13);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = x_8;
goto block_12;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_array_get_size(x_17);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_free_object(x_13);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = x_8;
goto block_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_fget(x_17, x_27);
x_29 = lean_box(0);
lean_inc(x_1);
lean_ctor_set(x_13, 1, x_29);
lean_ctor_set(x_13, 0, x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_30 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_28, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_array_fget(x_17, x_33);
lean_dec(x_17);
x_35 = lean_box(1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_34, x_36, x_4, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3;
x_41 = lean_array_push(x_40, x_31);
x_42 = lean_array_push(x_41, x_39);
lean_ctor_set(x_37, 0, x_42);
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3;
x_46 = lean_array_push(x_45, x_31);
x_47 = lean_array_push(x_46, x_43);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_31);
x_49 = !lean_is_exclusive(x_37);
if (x_49 == 0)
{
return x_37;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_37, 0);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_37);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_30);
if (x_53 == 0)
{
return x_30;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_30, 0);
x_55 = lean_ctor_get(x_30, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_30);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_19);
x_57 = lean_array_get_size(x_17);
x_58 = lean_unsigned_to_nat(3u);
x_59 = lean_nat_dec_eq(x_57, x_58);
lean_dec(x_57);
if (x_59 == 0)
{
lean_free_object(x_13);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = x_8;
goto block_12;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_array_fget(x_17, x_60);
x_62 = lean_box(0);
lean_inc(x_1);
lean_ctor_set(x_13, 1, x_62);
lean_ctor_set(x_13, 0, x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_63 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_61, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_unsigned_to_nat(2u);
x_67 = lean_array_fget(x_17, x_66);
lean_dec(x_17);
x_68 = lean_box(1);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_67, x_69, x_4, x_5, x_6, x_7, x_65);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3;
x_74 = lean_array_push(x_73, x_64);
x_75 = lean_array_push(x_74, x_72);
lean_ctor_set(x_70, 0, x_75);
return x_70;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_70, 0);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_70);
x_78 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3;
x_79 = lean_array_push(x_78, x_64);
x_80 = lean_array_push(x_79, x_76);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_64);
x_82 = !lean_is_exclusive(x_70);
if (x_82 == 0)
{
return x_70;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_70, 0);
x_84 = lean_ctor_get(x_70, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_70);
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
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_63);
if (x_86 == 0)
{
return x_63;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_63, 0);
x_88 = lean_ctor_get(x_63, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_63);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_13, 1);
lean_inc(x_90);
lean_dec(x_13);
x_91 = lean_ctor_get(x_14, 1);
lean_inc(x_91);
lean_dec(x_14);
x_92 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
x_93 = lean_string_dec_eq(x_91, x_92);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
x_95 = lean_string_dec_eq(x_91, x_94);
lean_dec(x_91);
if (x_95 == 0)
{
lean_dec(x_90);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = x_8;
goto block_12;
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_array_get_size(x_90);
x_97 = lean_unsigned_to_nat(2u);
x_98 = lean_nat_dec_eq(x_96, x_97);
lean_dec(x_96);
if (x_98 == 0)
{
lean_dec(x_90);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = x_8;
goto block_12;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_unsigned_to_nat(0u);
x_100 = lean_array_fget(x_90, x_99);
x_101 = lean_box(0);
lean_inc(x_1);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_1);
lean_ctor_set(x_102, 1, x_101);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_103 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_100, x_102, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_array_fget(x_90, x_106);
lean_dec(x_90);
x_108 = lean_box(1);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_107, x_109, x_4, x_5, x_6, x_7, x_105);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_114 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3;
x_115 = lean_array_push(x_114, x_104);
x_116 = lean_array_push(x_115, x_111);
if (lean_is_scalar(x_113)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_113;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_112);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_104);
x_118 = lean_ctor_get(x_110, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_110, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_120 = x_110;
} else {
 lean_dec_ref(x_110);
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
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_90);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_122 = lean_ctor_get(x_103, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_103, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_124 = x_103;
} else {
 lean_dec_ref(x_103);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_91);
x_126 = lean_array_get_size(x_90);
x_127 = lean_unsigned_to_nat(3u);
x_128 = lean_nat_dec_eq(x_126, x_127);
lean_dec(x_126);
if (x_128 == 0)
{
lean_dec(x_90);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = x_8;
goto block_12;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_unsigned_to_nat(1u);
x_130 = lean_array_fget(x_90, x_129);
x_131 = lean_box(0);
lean_inc(x_1);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_1);
lean_ctor_set(x_132, 1, x_131);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_133 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_130, x_132, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_unsigned_to_nat(2u);
x_137 = lean_array_fget(x_90, x_136);
lean_dec(x_90);
x_138 = lean_box(1);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_1);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_137, x_139, x_4, x_5, x_6, x_7, x_135);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
 x_143 = lean_box(0);
}
x_144 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3;
x_145 = lean_array_push(x_144, x_134);
x_146 = lean_array_push(x_145, x_141);
if (lean_is_scalar(x_143)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_143;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_142);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_134);
x_148 = lean_ctor_get(x_140, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_140, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_150 = x_140;
} else {
 lean_dec_ref(x_140);
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
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_90);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = x_8;
goto block_12;
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = x_8;
goto block_12;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
lean_ctor_set_uint8(x_11, 9, x_1);
x_14 = 2;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_shift_left(x_15, x_14);
x_17 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_18 = lean_uint64_lor(x_16, x_17);
lean_ctor_set_uint64(x_5, sizeof(void*)*7, x_18);
x_19 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
else
{
uint64_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; lean_object* x_44; 
x_20 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
x_21 = lean_ctor_get_uint8(x_11, 0);
x_22 = lean_ctor_get_uint8(x_11, 1);
x_23 = lean_ctor_get_uint8(x_11, 2);
x_24 = lean_ctor_get_uint8(x_11, 3);
x_25 = lean_ctor_get_uint8(x_11, 4);
x_26 = lean_ctor_get_uint8(x_11, 5);
x_27 = lean_ctor_get_uint8(x_11, 6);
x_28 = lean_ctor_get_uint8(x_11, 7);
x_29 = lean_ctor_get_uint8(x_11, 8);
x_30 = lean_ctor_get_uint8(x_11, 10);
x_31 = lean_ctor_get_uint8(x_11, 11);
x_32 = lean_ctor_get_uint8(x_11, 12);
x_33 = lean_ctor_get_uint8(x_11, 13);
x_34 = lean_ctor_get_uint8(x_11, 14);
x_35 = lean_ctor_get_uint8(x_11, 15);
x_36 = lean_ctor_get_uint8(x_11, 16);
x_37 = lean_ctor_get_uint8(x_11, 17);
lean_dec(x_11);
x_38 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_38, 0, x_21);
lean_ctor_set_uint8(x_38, 1, x_22);
lean_ctor_set_uint8(x_38, 2, x_23);
lean_ctor_set_uint8(x_38, 3, x_24);
lean_ctor_set_uint8(x_38, 4, x_25);
lean_ctor_set_uint8(x_38, 5, x_26);
lean_ctor_set_uint8(x_38, 6, x_27);
lean_ctor_set_uint8(x_38, 7, x_28);
lean_ctor_set_uint8(x_38, 8, x_29);
lean_ctor_set_uint8(x_38, 9, x_1);
lean_ctor_set_uint8(x_38, 10, x_30);
lean_ctor_set_uint8(x_38, 11, x_31);
lean_ctor_set_uint8(x_38, 12, x_32);
lean_ctor_set_uint8(x_38, 13, x_33);
lean_ctor_set_uint8(x_38, 14, x_34);
lean_ctor_set_uint8(x_38, 15, x_35);
lean_ctor_set_uint8(x_38, 16, x_36);
lean_ctor_set_uint8(x_38, 17, x_37);
x_39 = 2;
x_40 = lean_uint64_shift_right(x_20, x_39);
x_41 = lean_uint64_shift_left(x_40, x_39);
x_42 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_43 = lean_uint64_lor(x_41, x_42);
lean_ctor_set(x_5, 0, x_38);
lean_ctor_set_uint64(x_5, sizeof(void*)*7, x_43);
x_44 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_44;
}
}
else
{
lean_object* x_45; uint64_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; lean_object* x_80; lean_object* x_81; 
x_45 = lean_ctor_get(x_5, 0);
x_46 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
x_47 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_48 = lean_ctor_get(x_5, 1);
x_49 = lean_ctor_get(x_5, 2);
x_50 = lean_ctor_get(x_5, 3);
x_51 = lean_ctor_get(x_5, 4);
x_52 = lean_ctor_get(x_5, 5);
x_53 = lean_ctor_get(x_5, 6);
x_54 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_55 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_45);
lean_dec(x_5);
x_56 = lean_ctor_get_uint8(x_45, 0);
x_57 = lean_ctor_get_uint8(x_45, 1);
x_58 = lean_ctor_get_uint8(x_45, 2);
x_59 = lean_ctor_get_uint8(x_45, 3);
x_60 = lean_ctor_get_uint8(x_45, 4);
x_61 = lean_ctor_get_uint8(x_45, 5);
x_62 = lean_ctor_get_uint8(x_45, 6);
x_63 = lean_ctor_get_uint8(x_45, 7);
x_64 = lean_ctor_get_uint8(x_45, 8);
x_65 = lean_ctor_get_uint8(x_45, 10);
x_66 = lean_ctor_get_uint8(x_45, 11);
x_67 = lean_ctor_get_uint8(x_45, 12);
x_68 = lean_ctor_get_uint8(x_45, 13);
x_69 = lean_ctor_get_uint8(x_45, 14);
x_70 = lean_ctor_get_uint8(x_45, 15);
x_71 = lean_ctor_get_uint8(x_45, 16);
x_72 = lean_ctor_get_uint8(x_45, 17);
if (lean_is_exclusive(x_45)) {
 x_73 = x_45;
} else {
 lean_dec_ref(x_45);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 0, 18);
} else {
 x_74 = x_73;
}
lean_ctor_set_uint8(x_74, 0, x_56);
lean_ctor_set_uint8(x_74, 1, x_57);
lean_ctor_set_uint8(x_74, 2, x_58);
lean_ctor_set_uint8(x_74, 3, x_59);
lean_ctor_set_uint8(x_74, 4, x_60);
lean_ctor_set_uint8(x_74, 5, x_61);
lean_ctor_set_uint8(x_74, 6, x_62);
lean_ctor_set_uint8(x_74, 7, x_63);
lean_ctor_set_uint8(x_74, 8, x_64);
lean_ctor_set_uint8(x_74, 9, x_1);
lean_ctor_set_uint8(x_74, 10, x_65);
lean_ctor_set_uint8(x_74, 11, x_66);
lean_ctor_set_uint8(x_74, 12, x_67);
lean_ctor_set_uint8(x_74, 13, x_68);
lean_ctor_set_uint8(x_74, 14, x_69);
lean_ctor_set_uint8(x_74, 15, x_70);
lean_ctor_set_uint8(x_74, 16, x_71);
lean_ctor_set_uint8(x_74, 17, x_72);
x_75 = 2;
x_76 = lean_uint64_shift_right(x_46, x_75);
x_77 = lean_uint64_shift_left(x_76, x_75);
x_78 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_79 = lean_uint64_lor(x_77, x_78);
x_80 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_48);
lean_ctor_set(x_80, 2, x_49);
lean_ctor_set(x_80, 3, x_50);
lean_ctor_set(x_80, 4, x_51);
lean_ctor_set(x_80, 5, x_52);
lean_ctor_set(x_80, 6, x_53);
lean_ctor_set_uint64(x_80, sizeof(void*)*7, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 8, x_47);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 9, x_54);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 10, x_55);
x_81 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_2, x_3, x_4, x_80, x_6, x_7, x_8, x_9);
return x_81;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("injEq", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sizeOf_spec", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inj", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inj'", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_ConstantInfo_isUnsafe(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_19; uint8_t x_20; 
x_9 = lean_st_ref_get(x_6, x_7);
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
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
lean_inc(x_1);
x_20 = l_Lean_Meta_allowCompletion(x_19, x_1);
if (x_20 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
goto block_15;
}
else
{
if (x_8 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed), 8, 1);
lean_closure_set(x_21, 0, x_1);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0;
x_38 = lean_string_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1;
x_40 = lean_string_dec_eq(x_36, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_string_utf8_byte_size(x_36);
lean_inc(x_42);
lean_inc(x_36);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_unsigned_to_nat(4u);
lean_inc(x_42);
x_45 = l_Substring_prevn(x_43, x_44, x_42);
lean_inc(x_42);
lean_inc(x_36);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_42);
x_47 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4;
x_48 = l_Substring_beq(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_unsigned_to_nat(5u);
lean_inc(x_42);
x_50 = l_Substring_prevn(x_43, x_49, x_42);
lean_dec(x_43);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_36);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_42);
x_52 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__7;
x_53 = l_Substring_beq(x_51, x_52);
if (x_53 == 0)
{
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_11;
goto block_35;
}
else
{
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
goto block_18;
}
}
else
{
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
goto block_18;
}
}
else
{
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
goto block_18;
}
}
else
{
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
goto block_18;
}
}
else
{
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_11;
goto block_35;
}
block_35:
{
uint8_t x_27; 
x_27 = l_Lean_Name_isMetaprogramming(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = l_Lean_ConstantInfo_type(x_2);
x_29 = lean_box(2);
x_30 = lean_box(x_27);
x_31 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed), 9, 4);
lean_closure_set(x_31, 0, x_29);
lean_closure_set(x_31, 1, x_28);
lean_closure_set(x_31, 2, x_21);
lean_closure_set(x_31, 3, x_30);
x_32 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_31, x_27, x_22, x_23, x_24, x_25, x_26);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
x_33 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
goto block_15;
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0;
if (lean_is_scalar(x_12)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_12;
}
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_7);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(x_10, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___Lean_Meta_Rewrites_localHypotheses_spec__0(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_name_eq(x_1, x_5);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_localHypotheses_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_4, x_3);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_array_uget(x_2, x_4);
x_20 = l_Lean_Expr_fvarId_x21(x_19);
x_21 = l_List_elem___at___Lean_Meta_Rewrites_localHypotheses_spec__0(x_20, x_1);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_19);
x_22 = lean_infer_type(x_19, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_28 = l_Lean_Meta_forallMetaTelescopeReducing(x_23, x_25, x_27, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_29, 1);
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
x_36 = lean_ctor_get(x_31, 0);
lean_dec(x_36);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_37 = l_Lean_Meta_whnfR(x_35, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Expr_getAppFnArgs(x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 1)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_40, 1);
x_45 = lean_ctor_get(x_40, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
x_48 = lean_string_dec_eq(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
x_50 = lean_string_dec_eq(x_46, x_49);
lean_dec(x_46);
if (x_50 == 0)
{
lean_free_object(x_40);
lean_dec(x_44);
lean_free_object(x_31);
lean_free_object(x_29);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_39;
goto block_16;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_array_get_size(x_44);
lean_dec(x_44);
x_52 = lean_unsigned_to_nat(2u);
x_53 = lean_nat_dec_eq(x_51, x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_free_object(x_40);
lean_free_object(x_31);
lean_free_object(x_29);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_39;
goto block_16;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_box(x_21);
lean_ctor_set(x_40, 1, x_52);
lean_ctor_set(x_40, 0, x_54);
lean_inc(x_19);
lean_ctor_set(x_31, 1, x_40);
lean_ctor_set(x_31, 0, x_19);
x_55 = lean_array_push(x_5, x_31);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_box(x_53);
lean_ctor_set(x_29, 1, x_56);
lean_ctor_set(x_29, 0, x_57);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_19);
lean_ctor_set(x_58, 1, x_29);
x_59 = lean_array_push(x_55, x_58);
x_11 = x_59;
x_12 = x_39;
goto block_16;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_46);
x_60 = lean_array_get_size(x_44);
lean_dec(x_44);
x_61 = lean_unsigned_to_nat(3u);
x_62 = lean_nat_dec_eq(x_60, x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_free_object(x_40);
lean_free_object(x_31);
lean_free_object(x_29);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_39;
goto block_16;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_unsigned_to_nat(2u);
x_64 = lean_box(x_21);
lean_ctor_set(x_40, 1, x_63);
lean_ctor_set(x_40, 0, x_64);
lean_inc(x_19);
lean_ctor_set(x_31, 1, x_40);
lean_ctor_set(x_31, 0, x_19);
x_65 = lean_array_push(x_5, x_31);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_box(x_62);
lean_ctor_set(x_29, 1, x_66);
lean_ctor_set(x_29, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_19);
lean_ctor_set(x_68, 1, x_29);
x_69 = lean_array_push(x_65, x_68);
x_11 = x_69;
x_12 = x_39;
goto block_16;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_40, 1);
lean_inc(x_70);
lean_dec(x_40);
x_71 = lean_ctor_get(x_41, 1);
lean_inc(x_71);
lean_dec(x_41);
x_72 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
x_73 = lean_string_dec_eq(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
x_75 = lean_string_dec_eq(x_71, x_74);
lean_dec(x_71);
if (x_75 == 0)
{
lean_dec(x_70);
lean_free_object(x_31);
lean_free_object(x_29);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_39;
goto block_16;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_array_get_size(x_70);
lean_dec(x_70);
x_77 = lean_unsigned_to_nat(2u);
x_78 = lean_nat_dec_eq(x_76, x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_free_object(x_31);
lean_free_object(x_29);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_39;
goto block_16;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_box(x_21);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
lean_inc(x_19);
lean_ctor_set(x_31, 1, x_80);
lean_ctor_set(x_31, 0, x_19);
x_81 = lean_array_push(x_5, x_31);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_box(x_78);
lean_ctor_set(x_29, 1, x_82);
lean_ctor_set(x_29, 0, x_83);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_19);
lean_ctor_set(x_84, 1, x_29);
x_85 = lean_array_push(x_81, x_84);
x_11 = x_85;
x_12 = x_39;
goto block_16;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_71);
x_86 = lean_array_get_size(x_70);
lean_dec(x_70);
x_87 = lean_unsigned_to_nat(3u);
x_88 = lean_nat_dec_eq(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_free_object(x_31);
lean_free_object(x_29);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_39;
goto block_16;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_89 = lean_unsigned_to_nat(2u);
x_90 = lean_box(x_21);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
lean_inc(x_19);
lean_ctor_set(x_31, 1, x_91);
lean_ctor_set(x_31, 0, x_19);
x_92 = lean_array_push(x_5, x_31);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_box(x_88);
lean_ctor_set(x_29, 1, x_93);
lean_ctor_set(x_29, 0, x_94);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_19);
lean_ctor_set(x_95, 1, x_29);
x_96 = lean_array_push(x_92, x_95);
x_11 = x_96;
x_12 = x_39;
goto block_16;
}
}
}
}
else
{
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_31);
lean_free_object(x_29);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_39;
goto block_16;
}
}
else
{
lean_dec(x_41);
lean_dec(x_40);
lean_free_object(x_31);
lean_free_object(x_29);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_39;
goto block_16;
}
}
else
{
uint8_t x_97; 
lean_free_object(x_31);
lean_free_object(x_29);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_97 = !lean_is_exclusive(x_37);
if (x_97 == 0)
{
return x_37;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_37, 0);
x_99 = lean_ctor_get(x_37, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_37);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_31, 1);
lean_inc(x_101);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_102 = l_Lean_Meta_whnfR(x_101, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Lean_Expr_getAppFnArgs(x_103);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 1)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_109 = x_105;
} else {
 lean_dec_ref(x_105);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
lean_dec(x_106);
x_111 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
x_112 = lean_string_dec_eq(x_110, x_111);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
x_114 = lean_string_dec_eq(x_110, x_113);
lean_dec(x_110);
if (x_114 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
lean_free_object(x_29);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_104;
goto block_16;
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_array_get_size(x_108);
lean_dec(x_108);
x_116 = lean_unsigned_to_nat(2u);
x_117 = lean_nat_dec_eq(x_115, x_116);
lean_dec(x_115);
if (x_117 == 0)
{
lean_dec(x_109);
lean_free_object(x_29);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_104;
goto block_16;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_box(x_21);
if (lean_is_scalar(x_109)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_109;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
lean_inc(x_19);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_19);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_array_push(x_5, x_120);
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_box(x_117);
lean_ctor_set(x_29, 1, x_122);
lean_ctor_set(x_29, 0, x_123);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_19);
lean_ctor_set(x_124, 1, x_29);
x_125 = lean_array_push(x_121, x_124);
x_11 = x_125;
x_12 = x_104;
goto block_16;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_110);
x_126 = lean_array_get_size(x_108);
lean_dec(x_108);
x_127 = lean_unsigned_to_nat(3u);
x_128 = lean_nat_dec_eq(x_126, x_127);
lean_dec(x_126);
if (x_128 == 0)
{
lean_dec(x_109);
lean_free_object(x_29);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_104;
goto block_16;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_129 = lean_unsigned_to_nat(2u);
x_130 = lean_box(x_21);
if (lean_is_scalar(x_109)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_109;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
lean_inc(x_19);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_19);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_array_push(x_5, x_132);
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_box(x_128);
lean_ctor_set(x_29, 1, x_134);
lean_ctor_set(x_29, 0, x_135);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_19);
lean_ctor_set(x_136, 1, x_29);
x_137 = lean_array_push(x_133, x_136);
x_11 = x_137;
x_12 = x_104;
goto block_16;
}
}
}
else
{
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_free_object(x_29);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_104;
goto block_16;
}
}
else
{
lean_dec(x_106);
lean_dec(x_105);
lean_free_object(x_29);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_104;
goto block_16;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_free_object(x_29);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_138 = lean_ctor_get(x_102, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_102, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_140 = x_102;
} else {
 lean_dec_ref(x_102);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_29, 1);
lean_inc(x_142);
lean_dec(x_29);
x_143 = lean_ctor_get(x_28, 1);
lean_inc(x_143);
lean_dec(x_28);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_146 = l_Lean_Meta_whnfR(x_144, x_6, x_7, x_8, x_9, x_143);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_Expr_getAppFnArgs(x_147);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 1)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_153 = x_149;
} else {
 lean_dec_ref(x_149);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
lean_dec(x_150);
x_155 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
x_156 = lean_string_dec_eq(x_154, x_155);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
x_158 = lean_string_dec_eq(x_154, x_157);
lean_dec(x_154);
if (x_158 == 0)
{
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_145);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_148;
goto block_16;
}
else
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_159 = lean_array_get_size(x_152);
lean_dec(x_152);
x_160 = lean_unsigned_to_nat(2u);
x_161 = lean_nat_dec_eq(x_159, x_160);
lean_dec(x_159);
if (x_161 == 0)
{
lean_dec(x_153);
lean_dec(x_145);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_148;
goto block_16;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_162 = lean_box(x_21);
if (lean_is_scalar(x_153)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_153;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_160);
lean_inc(x_19);
if (lean_is_scalar(x_145)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_145;
}
lean_ctor_set(x_164, 0, x_19);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_array_push(x_5, x_164);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_box(x_161);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_19);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_array_push(x_165, x_169);
x_11 = x_170;
x_12 = x_148;
goto block_16;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
lean_dec(x_154);
x_171 = lean_array_get_size(x_152);
lean_dec(x_152);
x_172 = lean_unsigned_to_nat(3u);
x_173 = lean_nat_dec_eq(x_171, x_172);
lean_dec(x_171);
if (x_173 == 0)
{
lean_dec(x_153);
lean_dec(x_145);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_148;
goto block_16;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_174 = lean_unsigned_to_nat(2u);
x_175 = lean_box(x_21);
if (lean_is_scalar(x_153)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_153;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_174);
lean_inc(x_19);
if (lean_is_scalar(x_145)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_145;
}
lean_ctor_set(x_177, 0, x_19);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_array_push(x_5, x_177);
x_179 = lean_unsigned_to_nat(1u);
x_180 = lean_box(x_173);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_19);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_array_push(x_178, x_182);
x_11 = x_183;
x_12 = x_148;
goto block_16;
}
}
}
else
{
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_145);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_148;
goto block_16;
}
}
else
{
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_145);
lean_dec(x_19);
x_11 = x_5;
x_12 = x_148;
goto block_16;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_145);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_184 = lean_ctor_get(x_146, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_146, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_186 = x_146;
} else {
 lean_dec_ref(x_146);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_188 = !lean_is_exclusive(x_28);
if (x_188 == 0)
{
return x_28;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_28, 0);
x_190 = lean_ctor_get(x_28, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_28);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_192 = !lean_is_exclusive(x_22);
if (x_192 == 0)
{
return x_22;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_22, 0);
x_194 = lean_ctor_get(x_22, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_22);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
lean_dec(x_19);
x_11 = x_5;
x_12 = x_10;
goto block_16;
}
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
x_4 = x_14;
x_5 = x_11;
x_10 = x_12;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_localHypotheses___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_getLocalHyps___at___Lean_MVarId_symmSaturate_spec__0(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_Rewrites_localHypotheses___closed__0;
x_11 = lean_array_size(x_8);
x_12 = 0;
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_localHypotheses_spec__1(x_1, x_8, x_11, x_12, x_10, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_8);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___Lean_Meta_Rewrites_localHypotheses_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___Lean_Meta_Rewrites_localHypotheses_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_localHypotheses_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_localHypotheses_spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Rewrites_localHypotheses(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_Rewrites_droppedKeys___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_droppedKeys___closed__0;
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_droppedKeys___closed__3;
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_droppedKeys___closed__4;
x_2 = l_Lean_Meta_Rewrites_droppedKeys___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Rewrites_droppedKeys___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_droppedKeys___closed__6;
x_2 = l_Lean_Meta_Rewrites_droppedKeys___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Rewrites_droppedKeys___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0;
x_7 = l_Lean_Meta_Rewrites_droppedKeys;
x_8 = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_1190_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn___lam__0____x40_Lean_Meta_Tactic_Rewrites___hyg_1250_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_1250_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = lean_box(0);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_initFn___lam__0____x40_Lean_Meta_Tactic_Rewrites___hyg_1250_), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_box(0);
x_5 = lean_box(2);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_registerEnvExtension___redArg(x_3, x_4, x_6, x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(6500u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_incPrio(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_unbox(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_dec(x_7);
x_8 = lean_box(0);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_mul(x_9, x_1);
lean_dec(x_1);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_2, 0, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_mul(x_14, x_1);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
lean_dec(x_20);
x_21 = lean_box(1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_2);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwFindDecls___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwFindDecls___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_incPrio), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_Meta_Rewrites_rwFindDecls___closed__0;
x_9 = l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0;
x_10 = l_Lean_Meta_Rewrites_droppedKeys;
x_11 = lean_unsigned_to_nat(6500u);
x_12 = l_Lean_Meta_Rewrites_rwFindDecls___closed__1;
x_13 = l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(x_1, x_8, x_9, x_10, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
static uint64_t _init_l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; uint64_t x_3; 
x_1 = lean_box(2);
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_4);
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
uint64_t x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; lean_object* x_25; 
x_17 = l_Lean_Expr_mvarId_x21(x_11);
lean_dec(x_11);
x_18 = lean_box(2);
x_19 = lean_unbox(x_18);
lean_ctor_set_uint8(x_10, 9, x_19);
x_20 = 2;
x_21 = lean_uint64_shift_right(x_14, x_20);
x_22 = lean_uint64_shift_left(x_21, x_20);
x_23 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0;
x_24 = lean_uint64_lor(x_22, x_23);
lean_ctor_set_uint64(x_4, sizeof(void*)*7, x_24);
x_25 = l_Lean_MVarId_refl(x_17, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(1);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
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
uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; lean_object* x_62; 
x_36 = lean_ctor_get_uint8(x_10, 0);
x_37 = lean_ctor_get_uint8(x_10, 1);
x_38 = lean_ctor_get_uint8(x_10, 2);
x_39 = lean_ctor_get_uint8(x_10, 3);
x_40 = lean_ctor_get_uint8(x_10, 4);
x_41 = lean_ctor_get_uint8(x_10, 5);
x_42 = lean_ctor_get_uint8(x_10, 6);
x_43 = lean_ctor_get_uint8(x_10, 7);
x_44 = lean_ctor_get_uint8(x_10, 8);
x_45 = lean_ctor_get_uint8(x_10, 10);
x_46 = lean_ctor_get_uint8(x_10, 11);
x_47 = lean_ctor_get_uint8(x_10, 12);
x_48 = lean_ctor_get_uint8(x_10, 13);
x_49 = lean_ctor_get_uint8(x_10, 14);
x_50 = lean_ctor_get_uint8(x_10, 15);
x_51 = lean_ctor_get_uint8(x_10, 16);
x_52 = lean_ctor_get_uint8(x_10, 17);
lean_dec(x_10);
x_53 = l_Lean_Expr_mvarId_x21(x_11);
lean_dec(x_11);
x_54 = lean_box(2);
x_55 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_55, 0, x_36);
lean_ctor_set_uint8(x_55, 1, x_37);
lean_ctor_set_uint8(x_55, 2, x_38);
lean_ctor_set_uint8(x_55, 3, x_39);
lean_ctor_set_uint8(x_55, 4, x_40);
lean_ctor_set_uint8(x_55, 5, x_41);
lean_ctor_set_uint8(x_55, 6, x_42);
lean_ctor_set_uint8(x_55, 7, x_43);
lean_ctor_set_uint8(x_55, 8, x_44);
x_56 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, 9, x_56);
lean_ctor_set_uint8(x_55, 10, x_45);
lean_ctor_set_uint8(x_55, 11, x_46);
lean_ctor_set_uint8(x_55, 12, x_47);
lean_ctor_set_uint8(x_55, 13, x_48);
lean_ctor_set_uint8(x_55, 14, x_49);
lean_ctor_set_uint8(x_55, 15, x_50);
lean_ctor_set_uint8(x_55, 16, x_51);
lean_ctor_set_uint8(x_55, 17, x_52);
x_57 = 2;
x_58 = lean_uint64_shift_right(x_14, x_57);
x_59 = lean_uint64_shift_left(x_58, x_57);
x_60 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0;
x_61 = lean_uint64_lor(x_59, x_60);
lean_ctor_set(x_4, 0, x_55);
lean_ctor_set_uint64(x_4, sizeof(void*)*7, x_61);
x_62 = l_Lean_MVarId_refl(x_53, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(1);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_62, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_69 = x_62;
} else {
 lean_dec_ref(x_62);
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
else
{
uint64_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; lean_object* x_108; lean_object* x_109; 
x_71 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_72 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_73 = lean_ctor_get(x_4, 1);
x_74 = lean_ctor_get(x_4, 2);
x_75 = lean_ctor_get(x_4, 3);
x_76 = lean_ctor_get(x_4, 4);
x_77 = lean_ctor_get(x_4, 5);
x_78 = lean_ctor_get(x_4, 6);
x_79 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_80 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_4);
x_81 = lean_ctor_get_uint8(x_10, 0);
x_82 = lean_ctor_get_uint8(x_10, 1);
x_83 = lean_ctor_get_uint8(x_10, 2);
x_84 = lean_ctor_get_uint8(x_10, 3);
x_85 = lean_ctor_get_uint8(x_10, 4);
x_86 = lean_ctor_get_uint8(x_10, 5);
x_87 = lean_ctor_get_uint8(x_10, 6);
x_88 = lean_ctor_get_uint8(x_10, 7);
x_89 = lean_ctor_get_uint8(x_10, 8);
x_90 = lean_ctor_get_uint8(x_10, 10);
x_91 = lean_ctor_get_uint8(x_10, 11);
x_92 = lean_ctor_get_uint8(x_10, 12);
x_93 = lean_ctor_get_uint8(x_10, 13);
x_94 = lean_ctor_get_uint8(x_10, 14);
x_95 = lean_ctor_get_uint8(x_10, 15);
x_96 = lean_ctor_get_uint8(x_10, 16);
x_97 = lean_ctor_get_uint8(x_10, 17);
if (lean_is_exclusive(x_10)) {
 x_98 = x_10;
} else {
 lean_dec_ref(x_10);
 x_98 = lean_box(0);
}
x_99 = l_Lean_Expr_mvarId_x21(x_11);
lean_dec(x_11);
x_100 = lean_box(2);
if (lean_is_scalar(x_98)) {
 x_101 = lean_alloc_ctor(0, 0, 18);
} else {
 x_101 = x_98;
}
lean_ctor_set_uint8(x_101, 0, x_81);
lean_ctor_set_uint8(x_101, 1, x_82);
lean_ctor_set_uint8(x_101, 2, x_83);
lean_ctor_set_uint8(x_101, 3, x_84);
lean_ctor_set_uint8(x_101, 4, x_85);
lean_ctor_set_uint8(x_101, 5, x_86);
lean_ctor_set_uint8(x_101, 6, x_87);
lean_ctor_set_uint8(x_101, 7, x_88);
lean_ctor_set_uint8(x_101, 8, x_89);
x_102 = lean_unbox(x_100);
lean_ctor_set_uint8(x_101, 9, x_102);
lean_ctor_set_uint8(x_101, 10, x_90);
lean_ctor_set_uint8(x_101, 11, x_91);
lean_ctor_set_uint8(x_101, 12, x_92);
lean_ctor_set_uint8(x_101, 13, x_93);
lean_ctor_set_uint8(x_101, 14, x_94);
lean_ctor_set_uint8(x_101, 15, x_95);
lean_ctor_set_uint8(x_101, 16, x_96);
lean_ctor_set_uint8(x_101, 17, x_97);
x_103 = 2;
x_104 = lean_uint64_shift_right(x_71, x_103);
x_105 = lean_uint64_shift_left(x_104, x_103);
x_106 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0;
x_107 = lean_uint64_lor(x_105, x_106);
x_108 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_108, 0, x_101);
lean_ctor_set(x_108, 1, x_73);
lean_ctor_set(x_108, 2, x_74);
lean_ctor_set(x_108, 3, x_75);
lean_ctor_set(x_108, 4, x_76);
lean_ctor_set(x_108, 5, x_77);
lean_ctor_set(x_108, 6, x_78);
lean_ctor_set_uint64(x_108, sizeof(void*)*7, x_107);
lean_ctor_set_uint8(x_108, sizeof(void*)*7 + 8, x_72);
lean_ctor_set_uint8(x_108, sizeof(void*)*7 + 9, x_79);
lean_ctor_set_uint8(x_108, sizeof(void*)*7 + 10, x_80);
x_109 = l_Lean_MVarId_refl(x_99, x_108, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(1);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_box(0);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed), 8, 3);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0), 8, 3);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_11);
x_13 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_24; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_24 = l_Lean_Exception_isInterrupt(x_14);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Exception_isRuntime(x_14);
lean_dec(x_14);
x_16 = x_25;
goto block_23;
}
else
{
lean_dec(x_14);
x_16 = x_24;
goto block_23;
}
block_23:
{
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_13, 0);
lean_dec(x_19);
x_20 = lean_box(x_16);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
x_21 = lean_box(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
else
{
lean_dec(x_15);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_ppExpr(x_8, x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_unsigned_to_nat(120u);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_format_pretty(x_11, x_12, x_13, x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_unsigned_to_nat(120u);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_format_pretty(x_15, x_17, x_18, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Meta_Rewrites_SideConditions_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1;
x_8 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_1 = lean_box(0);
x_2 = lean_box(1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 0, 4);
x_5 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, 0, x_5);
x_6 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, 1, x_6);
x_7 = lean_unbox(x_1);
lean_ctor_set_uint8(x_4, 2, x_7);
x_8 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, 3, x_8);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = l_Lean_Meta_Rewrites_solveByElim___closed__0;
x_11 = lean_unbox(x_8);
x_12 = lean_unbox(x_8);
lean_inc(x_5);
x_13 = l_Lean_Meta_SolveByElim_mkAssumptionSet(x_11, x_12, x_9, x_9, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed), 7, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed), 6, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed), 6, 0);
x_21 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_21, 3, x_20);
x_22 = lean_unbox(x_8);
lean_ctor_set_uint8(x_21, sizeof(void*)*4, x_22);
x_23 = lean_box(1);
x_24 = l_Lean_Meta_Rewrites_solveByElim___closed__1;
x_25 = lean_box(1);
x_26 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_27);
x_28 = lean_unbox(x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 1, x_28);
x_29 = lean_unbox(x_8);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 2, x_29);
x_30 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_30, 0, x_26);
x_31 = lean_unbox(x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_31);
x_32 = lean_unbox(x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*1 + 1, x_32);
x_33 = lean_unbox(x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*1 + 2, x_33);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_34 = l_Lean_Meta_SolveByElim_solveByElim(x_30, x_16, x_17, x_1, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_35);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1;
x_44 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_43, x_3, x_4, x_5, x_6, x_42);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_34);
if (x_45 == 0)
{
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
return x_13;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_ctor_get(x_13, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_13);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Rewrites_solveByElim___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Rewrites_solveByElim___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Rewrites_solveByElim___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Rewrites_rwLemma_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = l_List_reverse___redArg(x_2);
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
x_13 = l_Lean_MVarId_assumption(x_11, x_3, x_4, x_5, x_6, x_7);
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
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_MVarId_assumption(x_21, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_2);
x_1 = x_22;
x_2 = x_26;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_30 = x_23;
} else {
 lean_dec_ref(x_23);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("symm", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(1);
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_6);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 1, x_7);
x_8 = lean_unbox(x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 2, x_8);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("considering ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("← ", 4, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_83; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_107; lean_object* x_108; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_183; lean_object* x_184; 
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_6, 0);
lean_inc(x_195);
lean_dec(x_6);
x_183 = x_195;
x_184 = x_11;
goto block_194;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_6, 0);
lean_inc(x_196);
lean_dec(x_6);
x_197 = l_Lean_Meta_saveState___redArg(x_8, x_10, x_11);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_196, x_7, x_8, x_9, x_10, x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_198);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_183 = x_201;
x_184 = x_202;
goto block_194;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; uint8_t x_216; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_ctor_get(x_200, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_200, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_205 = x_200;
} else {
 lean_dec_ref(x_200);
 x_205 = lean_box(0);
}
x_216 = l_Lean_Exception_isInterrupt(x_203);
if (x_216 == 0)
{
uint8_t x_217; 
x_217 = l_Lean_Exception_isRuntime(x_203);
x_206 = x_217;
goto block_215;
}
else
{
x_206 = x_216;
goto block_215;
}
block_215:
{
if (x_206 == 0)
{
lean_object* x_207; uint8_t x_208; 
lean_dec(x_205);
lean_dec(x_203);
x_207 = l_Lean_Meta_SavedState_restore___redArg(x_198, x_8, x_10, x_204);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_198);
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_207, 0);
lean_dec(x_209);
x_210 = lean_box(0);
lean_ctor_set(x_207, 0, x_210);
return x_207;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_207, 1);
lean_inc(x_211);
lean_dec(x_207);
x_212 = lean_box(0);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
else
{
lean_object* x_214; 
lean_dec(x_198);
lean_dec(x_10);
lean_dec(x_8);
if (lean_is_scalar(x_205)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_205;
}
lean_ctor_set(x_214, 0, x_203);
lean_ctor_set(x_214, 1, x_204);
return x_214;
}
}
}
}
block_26:
{
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_13);
x_18 = l_Lean_Meta_SavedState_restore___redArg(x_16, x_14, x_12, x_15);
lean_dec(x_12);
lean_dec(x_14);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
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
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_15);
return x_25;
}
}
block_56:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_st_ref_get(x_31, x_32);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_39);
x_40 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_39, x_28, x_33, x_31, x_30, x_27, x_38);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_1);
lean_ctor_set(x_43, 2, x_29);
lean_ctor_set(x_43, 3, x_39);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_35);
x_44 = lean_unbox(x_42);
lean_dec(x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*4 + 1, x_44);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_40, 0, x_45);
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
x_48 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_48, 0, x_34);
lean_ctor_set(x_48, 1, x_1);
lean_ctor_set(x_48, 2, x_29);
lean_ctor_set(x_48, 3, x_39);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_35);
x_49 = lean_unbox(x_46);
lean_dec(x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*4 + 1, x_49);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_39);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_40);
if (x_52 == 0)
{
return x_40;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_40, 0);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_40);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
block_82:
{
lean_object* x_66; 
x_66 = l_Lean_Meta_Rewrites_rewriteResultLemma(x_58);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_69, x_62, x_65);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1;
x_74 = lean_unsigned_to_nat(4u);
x_75 = l_Lean_Expr_isAppOfArity(x_71, x_73, x_74);
if (x_75 == 0)
{
x_27 = x_64;
x_28 = x_57;
x_29 = x_58;
x_30 = x_63;
x_31 = x_62;
x_32 = x_72;
x_33 = x_61;
x_34 = x_71;
x_35 = x_60;
goto block_56;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_unsigned_to_nat(3u);
x_77 = l_Lean_Expr_getAppNumArgs(x_71);
x_78 = lean_nat_sub(x_77, x_76);
lean_dec(x_77);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_sub(x_78, x_79);
lean_dec(x_78);
x_81 = l_Lean_Expr_getRevArg_x21(x_71, x_80);
lean_dec(x_71);
x_27 = x_64;
x_28 = x_57;
x_29 = x_58;
x_30 = x_63;
x_31 = x_62;
x_32 = x_72;
x_33 = x_61;
x_34 = x_81;
x_35 = x_59;
goto block_56;
}
}
}
block_86:
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
block_96:
{
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_89);
x_93 = l_Lean_Meta_SavedState_restore___redArg(x_91, x_90, x_87, x_88);
lean_dec(x_87);
lean_dec(x_90);
lean_dec(x_91);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_83 = x_94;
goto block_86;
}
else
{
lean_object* x_95; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_87);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_88);
return x_95;
}
}
block_106:
{
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_101);
x_103 = l_Lean_Meta_SavedState_restore___redArg(x_99, x_98, x_97, x_100);
lean_dec(x_97);
lean_dec(x_98);
lean_dec(x_99);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_83 = x_104;
goto block_86;
}
else
{
lean_object* x_105; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_100);
return x_105;
}
}
block_167:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = l_Lean_Meta_saveState___redArg(x_8, x_10, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_box(1);
x_113 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_107);
x_114 = l_Lean_MVarId_rewrite(x_2, x_3, x_107, x_4, x_113, x_7, x_8, x_9, x_10, x_111);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
lean_dec(x_110);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 2);
lean_inc(x_118);
x_119 = l_List_isEmpty___redArg(x_118);
if (x_119 == 0)
{
lean_dec(x_107);
switch (x_5) {
case 0:
{
lean_dec(x_118);
if (x_119 == 0)
{
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_83 = x_116;
goto block_86;
}
else
{
uint8_t x_120; 
x_120 = lean_unbox(x_112);
x_57 = x_117;
x_58 = x_115;
x_59 = x_120;
x_60 = x_119;
x_61 = x_7;
x_62 = x_8;
x_63 = x_9;
x_64 = x_10;
x_65 = x_116;
goto block_82;
}
}
case 1:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = l_Lean_Meta_saveState___redArg(x_8, x_10, x_116);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_125 = l_List_mapM_loop___at___Lean_Meta_Rewrites_rwLemma_spec__0(x_118, x_124, x_7, x_8, x_9, x_10, x_123);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; uint8_t x_127; 
lean_dec(x_122);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_unbox(x_112);
x_57 = x_117;
x_58 = x_115;
x_59 = x_127;
x_60 = x_119;
x_61 = x_7;
x_62 = x_8;
x_63 = x_9;
x_64 = x_10;
x_65 = x_126;
goto block_82;
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; 
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
lean_dec(x_125);
x_130 = l_Lean_Exception_isInterrupt(x_128);
if (x_130 == 0)
{
uint8_t x_131; 
x_131 = l_Lean_Exception_isRuntime(x_128);
x_97 = x_10;
x_98 = x_8;
x_99 = x_122;
x_100 = x_129;
x_101 = x_128;
x_102 = x_131;
goto block_106;
}
else
{
x_97 = x_10;
x_98 = x_8;
x_99 = x_122;
x_100 = x_129;
x_101 = x_128;
x_102 = x_130;
goto block_106;
}
}
}
default: 
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = l_Lean_Meta_saveState___redArg(x_8, x_10, x_116);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_unsigned_to_nat(6u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_136 = l_Lean_Meta_Rewrites_solveByElim(x_118, x_135, x_7, x_8, x_9, x_10, x_134);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; uint8_t x_138; 
lean_dec(x_133);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_unbox(x_112);
x_57 = x_117;
x_58 = x_115;
x_59 = x_138;
x_60 = x_119;
x_61 = x_7;
x_62 = x_8;
x_63 = x_9;
x_64 = x_10;
x_65 = x_137;
goto block_82;
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
lean_dec(x_136);
x_141 = l_Lean_Exception_isInterrupt(x_139);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = l_Lean_Exception_isRuntime(x_139);
x_87 = x_10;
x_88 = x_140;
x_89 = x_139;
x_90 = x_8;
x_91 = x_133;
x_92 = x_142;
goto block_96;
}
else
{
x_87 = x_10;
x_88 = x_140;
x_89 = x_139;
x_90 = x_8;
x_91 = x_133;
x_92 = x_141;
goto block_96;
}
}
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_118);
x_143 = lean_st_ref_get(x_8, x_116);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
lean_dec(x_144);
lean_inc(x_146);
x_147 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_146, x_117, x_7, x_8, x_9, x_10, x_145);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_147, 0);
x_150 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_150, 0, x_107);
lean_ctor_set(x_150, 1, x_1);
lean_ctor_set(x_150, 2, x_115);
lean_ctor_set(x_150, 3, x_146);
lean_ctor_set_uint8(x_150, sizeof(void*)*4, x_4);
x_151 = lean_unbox(x_149);
lean_dec(x_149);
lean_ctor_set_uint8(x_150, sizeof(void*)*4 + 1, x_151);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_147, 0, x_152);
return x_147;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; 
x_153 = lean_ctor_get(x_147, 0);
x_154 = lean_ctor_get(x_147, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_147);
x_155 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_155, 0, x_107);
lean_ctor_set(x_155, 1, x_1);
lean_ctor_set(x_155, 2, x_115);
lean_ctor_set(x_155, 3, x_146);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_4);
x_156 = lean_unbox(x_153);
lean_dec(x_153);
lean_ctor_set_uint8(x_155, sizeof(void*)*4 + 1, x_156);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_155);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_154);
return x_158;
}
}
else
{
uint8_t x_159; 
lean_dec(x_146);
lean_dec(x_115);
lean_dec(x_107);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_147);
if (x_159 == 0)
{
return x_147;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_147, 0);
x_161 = lean_ctor_get(x_147, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_147);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
lean_dec(x_107);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_163 = lean_ctor_get(x_114, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_114, 1);
lean_inc(x_164);
lean_dec(x_114);
x_165 = l_Lean_Exception_isInterrupt(x_163);
if (x_165 == 0)
{
uint8_t x_166; 
x_166 = l_Lean_Exception_isRuntime(x_163);
x_12 = x_10;
x_13 = x_163;
x_14 = x_8;
x_15 = x_164;
x_16 = x_110;
x_17 = x_166;
goto block_26;
}
else
{
x_12 = x_10;
x_13 = x_163;
x_14 = x_8;
x_15 = x_164;
x_16 = x_110;
x_17 = x_165;
goto block_26;
}
}
}
block_182:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_173 = l_Lean_stringToMessageData(x_172);
lean_dec(x_172);
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_169);
lean_ctor_set(x_174, 1, x_173);
x_175 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4;
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
lean_inc(x_171);
x_177 = l_Lean_MessageData_ofExpr(x_171);
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_175);
x_180 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_170, x_179, x_7, x_8, x_9, x_10, x_168);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
x_107 = x_171;
x_108 = x_181;
goto block_167;
}
block_194:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_185 = l_Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites___hyg_5_;
x_186 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_185, x_9, x_184);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_unbox(x_187);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_107 = x_183;
x_108 = x_189;
goto block_167;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_186, 1);
lean_inc(x_190);
lean_dec(x_186);
x_191 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6;
if (x_4 == 0)
{
lean_object* x_192; 
x_192 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3;
x_168 = x_190;
x_169 = x_191;
x_170 = x_185;
x_171 = x_183;
x_172 = x_192;
goto block_182;
}
else
{
lean_object* x_193; 
x_193 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7;
x_168 = x_190;
x_169 = x_191;
x_170 = x_185;
x_171 = x_183;
x_172 = x_193;
goto block_182;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(x_6);
x_14 = lean_box(x_4);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed), 11, 6);
lean_closure_set(x_15, 0, x_7);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_13);
lean_closure_set(x_15, 4, x_14);
lean_closure_set(x_15, 5, x_5);
x_16 = l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0___redArg(x_1, x_15, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_Rewrites_rwLemma___lam__0(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lean_Meta_Rewrites_rwLemma(x_1, x_2, x_3, x_13, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_eq(x_3, x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = lean_infer_type(x_18, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_22 = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(x_1, x_20, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Array_append___redArg(x_5, x_23);
lean_dec(x_23);
x_11 = x_25;
x_12 = x_24;
goto block_16;
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_11 = x_26;
x_12 = x_27;
goto block_16;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_22;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_11;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_2);
x_9 = lean_apply_7(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
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
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_1);
x_11 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_10);
x_16 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg___lam__0(x_1, x_10, x_15, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_27; size_t x_30; size_t x_31; uint8_t x_32; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_22 = x_17;
} else {
 lean_dec_ref(x_17);
 x_22 = lean_box(0);
}
x_30 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_31 = lean_ptr_addr(x_14);
x_32 = lean_usize_dec_eq(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_10);
x_27 = x_32;
goto block_29;
}
else
{
size_t x_33; size_t x_34; uint8_t x_35; 
x_33 = lean_ptr_addr(x_10);
lean_dec(x_10);
x_34 = lean_ptr_addr(x_20);
x_35 = lean_usize_dec_eq(x_33, x_34);
x_27 = x_35;
goto block_29;
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
if (lean_is_scalar(x_19)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_19;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
return x_25;
}
block_29:
{
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_2);
x_28 = l_Lean_Expr_app___override(x_14, x_20);
x_23 = x_28;
goto block_26;
}
else
{
lean_dec(x_20);
lean_dec(x_14);
x_23 = x_2;
goto block_26;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
return x_16;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
case 6:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 2);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_37);
lean_inc(x_1);
x_40 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg___lam__0(x_1, x_37, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
lean_inc(x_38);
x_45 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg___lam__0(x_1, x_38, x_44, x_4, x_5, x_6, x_7, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_56; size_t x_61; size_t x_62; uint8_t x_63; 
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
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_51 = x_46;
} else {
 lean_dec_ref(x_46);
 x_51 = lean_box(0);
}
x_61 = lean_ptr_addr(x_37);
lean_dec(x_37);
x_62 = lean_ptr_addr(x_43);
x_63 = lean_usize_dec_eq(x_61, x_62);
if (x_63 == 0)
{
lean_dec(x_38);
x_56 = x_63;
goto block_60;
}
else
{
size_t x_64; size_t x_65; uint8_t x_66; 
x_64 = lean_ptr_addr(x_38);
lean_dec(x_38);
x_65 = lean_ptr_addr(x_49);
x_66 = lean_usize_dec_eq(x_64, x_65);
x_56 = x_66;
goto block_60;
}
block_55:
{
lean_object* x_53; lean_object* x_54; 
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
if (lean_is_scalar(x_48)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_48;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
return x_54;
}
block_60:
{
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_2);
x_57 = l_Lean_Expr_lam___override(x_36, x_43, x_49, x_39);
x_52 = x_57;
goto block_55;
}
else
{
uint8_t x_58; 
x_58 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_39, x_39);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_2);
x_59 = l_Lean_Expr_lam___override(x_36, x_43, x_49, x_39);
x_52 = x_59;
goto block_55;
}
else
{
lean_dec(x_49);
lean_dec(x_43);
lean_dec(x_36);
x_52 = x_2;
goto block_55;
}
}
}
}
else
{
lean_dec(x_43);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_2);
return x_45;
}
}
else
{
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_40;
}
}
case 7:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_2, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_2, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_2, 2);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_68);
lean_inc(x_1);
x_71 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg___lam__0(x_1, x_68, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_69);
x_76 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg___lam__0(x_1, x_69, x_75, x_4, x_5, x_6, x_7, x_73);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_87; size_t x_92; size_t x_93; uint8_t x_94; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_82 = x_77;
} else {
 lean_dec_ref(x_77);
 x_82 = lean_box(0);
}
x_92 = lean_ptr_addr(x_68);
lean_dec(x_68);
x_93 = lean_ptr_addr(x_74);
x_94 = lean_usize_dec_eq(x_92, x_93);
if (x_94 == 0)
{
lean_dec(x_69);
x_87 = x_94;
goto block_91;
}
else
{
size_t x_95; size_t x_96; uint8_t x_97; 
x_95 = lean_ptr_addr(x_69);
lean_dec(x_69);
x_96 = lean_ptr_addr(x_80);
x_97 = lean_usize_dec_eq(x_95, x_96);
x_87 = x_97;
goto block_91;
}
block_86:
{
lean_object* x_84; lean_object* x_85; 
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
if (lean_is_scalar(x_79)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_79;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_78);
return x_85;
}
block_91:
{
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_2);
x_88 = l_Lean_Expr_forallE___override(x_67, x_74, x_80, x_70);
x_83 = x_88;
goto block_86;
}
else
{
uint8_t x_89; 
x_89 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_70, x_70);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_2);
x_90 = l_Lean_Expr_forallE___override(x_67, x_74, x_80, x_70);
x_83 = x_90;
goto block_86;
}
else
{
lean_dec(x_80);
lean_dec(x_74);
lean_dec(x_67);
x_83 = x_2;
goto block_86;
}
}
}
}
else
{
lean_dec(x_74);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_2);
return x_76;
}
}
else
{
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_71;
}
}
case 8:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_2, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_2, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_2, 3);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_99);
lean_inc(x_1);
x_103 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg___lam__0(x_1, x_99, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_100);
lean_inc(x_1);
x_108 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg___lam__0(x_1, x_100, x_107, x_4, x_5, x_6, x_7, x_105);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
lean_inc(x_101);
x_113 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg___lam__0(x_1, x_101, x_112, x_4, x_5, x_6, x_7, x_110);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_124; size_t x_131; size_t x_132; uint8_t x_133; 
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
x_131 = lean_ptr_addr(x_99);
lean_dec(x_99);
x_132 = lean_ptr_addr(x_106);
x_133 = lean_usize_dec_eq(x_131, x_132);
if (x_133 == 0)
{
lean_dec(x_100);
x_124 = x_133;
goto block_130;
}
else
{
size_t x_134; size_t x_135; uint8_t x_136; 
x_134 = lean_ptr_addr(x_100);
lean_dec(x_100);
x_135 = lean_ptr_addr(x_111);
x_136 = lean_usize_dec_eq(x_134, x_135);
x_124 = x_136;
goto block_130;
}
block_123:
{
lean_object* x_121; lean_object* x_122; 
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
if (lean_is_scalar(x_116)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_116;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_115);
return x_122;
}
block_130:
{
if (x_124 == 0)
{
lean_object* x_125; 
lean_dec(x_101);
lean_dec(x_2);
x_125 = l_Lean_Expr_letE___override(x_98, x_106, x_111, x_117, x_102);
x_120 = x_125;
goto block_123;
}
else
{
size_t x_126; size_t x_127; uint8_t x_128; 
x_126 = lean_ptr_addr(x_101);
lean_dec(x_101);
x_127 = lean_ptr_addr(x_117);
x_128 = lean_usize_dec_eq(x_126, x_127);
if (x_128 == 0)
{
lean_object* x_129; 
lean_dec(x_2);
x_129 = l_Lean_Expr_letE___override(x_98, x_106, x_111, x_117, x_102);
x_120 = x_129;
goto block_123;
}
else
{
lean_dec(x_117);
lean_dec(x_111);
lean_dec(x_106);
lean_dec(x_98);
x_120 = x_2;
goto block_123;
}
}
}
}
else
{
lean_dec(x_111);
lean_dec(x_106);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_2);
return x_113;
}
}
else
{
lean_dec(x_106);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_108;
}
}
else
{
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_103;
}
}
case 10:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_2, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_2, 1);
lean_inc(x_138);
lean_inc(x_138);
x_139 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg___lam__0(x_1, x_138, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; size_t x_150; size_t x_151; uint8_t x_152; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_140, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_145 = x_140;
} else {
 lean_dec_ref(x_140);
 x_145 = lean_box(0);
}
x_150 = lean_ptr_addr(x_138);
lean_dec(x_138);
x_151 = lean_ptr_addr(x_143);
x_152 = lean_usize_dec_eq(x_150, x_151);
if (x_152 == 0)
{
lean_object* x_153; 
lean_dec(x_2);
x_153 = l_Lean_Expr_mdata___override(x_137, x_143);
x_146 = x_153;
goto block_149;
}
else
{
lean_dec(x_143);
lean_dec(x_137);
x_146 = x_2;
goto block_149;
}
block_149:
{
lean_object* x_147; lean_object* x_148; 
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_144);
if (lean_is_scalar(x_142)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_142;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_141);
return x_148;
}
}
else
{
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_2);
return x_139;
}
}
case 11:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_2, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_2, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_2, 2);
lean_inc(x_156);
lean_inc(x_156);
x_157 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg___lam__0(x_1, x_156, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; size_t x_168; size_t x_169; uint8_t x_170; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_158, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_158, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_163 = x_158;
} else {
 lean_dec_ref(x_158);
 x_163 = lean_box(0);
}
x_168 = lean_ptr_addr(x_156);
lean_dec(x_156);
x_169 = lean_ptr_addr(x_161);
x_170 = lean_usize_dec_eq(x_168, x_169);
if (x_170 == 0)
{
lean_object* x_171; 
lean_dec(x_2);
x_171 = l_Lean_Expr_proj___override(x_154, x_155, x_161);
x_164 = x_171;
goto block_167;
}
else
{
lean_dec(x_161);
lean_dec(x_155);
lean_dec(x_154);
x_164 = x_2;
goto block_167;
}
block_167:
{
lean_object* x_165; lean_object* x_166; 
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
if (lean_is_scalar(x_160)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_160;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_159);
return x_166;
}
}
else
{
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_2);
return x_157;
}
}
default: 
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_2);
lean_ctor_set(x_172, 1, x_3);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_8);
return x_173;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1_spec__1___redArg(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
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
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
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
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Array_reverse___redArg(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_2);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_15, x_15);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
lean_free_object(x_9);
x_18 = 0;
x_19 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_20 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(x_1, x_2, x_18, x_19, x_13, x_4, x_5, x_6, x_7, x_12);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = l_Array_reverse___redArg(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_get_size(x_2);
x_26 = lean_nat_dec_lt(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_25, x_25);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_32 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(x_1, x_2, x_30, x_31, x_23, x_4, x_5, x_6, x_7, x_22);
return x_32;
}
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Array_append___redArg(x_2, x_11);
lean_dec(x_11);
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
x_15 = l_Array_append___redArg(x_2, x_13);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_dec(x_2);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
case 6:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(x_2, x_10, x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
case 7:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(x_2, x_14, x_16, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
case 8:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_18, 0, x_1);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(x_2, x_18, x_20, x_3, x_4, x_5, x_6, x_7);
return x_21;
}
default: 
{
lean_object* x_22; 
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3), 8, 1);
lean_closure_set(x_25, 0, x_1);
x_26 = l_Array_reverse___redArg(x_23);
x_27 = l_Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(x_25, x_26, x_2, x_3, x_4, x_5, x_6, x_24);
return x_27;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_array_fget(x_1, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
x_10 = lean_array_fget(x_1, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_nat_dec_lt(x_12, x_7);
lean_dec(x_7);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_9);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_14; 
x_14 = lean_array_fswap(x_1, x_2, x_9);
lean_dec(x_2);
x_1 = x_14;
x_2 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
lean_inc(x_2);
x_10 = l_Array_insertionSort_swapLoop___at___Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(x_1, x_2);
x_11 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_1 = x_10;
x_2 = x_11;
x_3 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_35; uint8_t x_53; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_20 = x_16;
} else {
 lean_dec_ref(x_16);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_5, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_22 = x_5;
} else {
 lean_dec_ref(x_5);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_25 = x_17;
} else {
 lean_dec_ref(x_17);
 x_25 = lean_box(0);
}
x_53 = l_Lean_NameSet_contains(x_1, x_18);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = lean_unbox(x_19);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_25);
lean_dec(x_22);
x_55 = l_Lean_NameSet_contains(x_24, x_18);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = lean_unbox(x_19);
lean_dec(x_19);
x_35 = x_56;
goto block_52;
}
else
{
lean_dec(x_19);
x_35 = x_13;
goto block_52;
}
}
else
{
uint8_t x_57; 
lean_dec(x_20);
x_57 = l_Lean_NameSet_contains(x_21, x_18);
if (x_57 == 0)
{
lean_dec(x_19);
x_26 = x_53;
goto block_34;
}
else
{
uint8_t x_58; 
x_58 = lean_unbox(x_19);
lean_dec(x_19);
x_26 = x_58;
goto block_34;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_59 = !lean_is_exclusive(x_15);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_15, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_15, 0);
lean_dec(x_61);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_23);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_21);
lean_ctor_set(x_62, 1, x_15);
x_7 = x_62;
x_8 = x_6;
goto block_12;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_15);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_23);
lean_ctor_set(x_63, 1, x_24);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_21);
lean_ctor_set(x_64, 1, x_63);
x_7 = x_64;
x_8 = x_6;
goto block_12;
}
}
block_34:
{
uint8_t x_27; 
x_27 = l_instDecidableNot___redArg(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_15);
if (lean_is_scalar(x_25)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_25;
}
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
if (lean_is_scalar(x_22)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_22;
}
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
x_7 = x_29;
x_8 = x_6;
goto block_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_array_push(x_23, x_15);
x_31 = l_Lean_NameSet_insert(x_21, x_18);
if (lean_is_scalar(x_25)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_25;
}
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_24);
if (lean_is_scalar(x_22)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_22;
}
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_7 = x_33;
x_8 = x_6;
goto block_12;
}
}
block_52:
{
uint8_t x_36; 
x_36 = l_instDecidableNot___redArg(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec(x_18);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_15, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_15, 0);
lean_dec(x_39);
if (lean_is_scalar(x_20)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_20;
}
lean_ctor_set(x_40, 0, x_23);
lean_ctor_set(x_40, 1, x_24);
lean_ctor_set(x_15, 1, x_40);
lean_ctor_set(x_15, 0, x_21);
x_7 = x_15;
x_8 = x_6;
goto block_12;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_15);
if (lean_is_scalar(x_20)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_20;
}
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_24);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_21);
lean_ctor_set(x_42, 1, x_41);
x_7 = x_42;
x_8 = x_6;
goto block_12;
}
}
else
{
lean_object* x_43; uint8_t x_44; 
lean_inc(x_15);
x_43 = lean_array_push(x_23, x_15);
x_44 = !lean_is_exclusive(x_15);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_15, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_15, 0);
lean_dec(x_46);
x_47 = l_Lean_NameSet_insert(x_24, x_18);
if (lean_is_scalar(x_20)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_20;
}
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_15, 1, x_48);
lean_ctor_set(x_15, 0, x_21);
x_7 = x_15;
x_8 = x_6;
goto block_12;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_15);
x_49 = l_Lean_NameSet_insert(x_24, x_18);
if (lean_is_scalar(x_20)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_20;
}
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_21);
lean_ctor_set(x_51, 1, x_50);
x_7 = x_51;
x_8 = x_6;
goto block_12;
}
}
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
x_5 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_5, 0, x_10);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_9, x_2, x_5);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_18, x_2, x_20);
x_2 = x_22;
x_3 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_5, 0, x_10);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_9, x_2, x_5);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_18, x_2, x_20);
x_2 = x_22;
x_3 = x_23;
goto _start;
}
}
}
}
static lean_object* _init_l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_7 = x_1;
} else {
 lean_dec_ref(x_1);
 x_7 = lean_box(0);
}
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_32; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = l_Lean_MessageData_ofName(x_9);
x_15 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__2;
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_15);
lean_ctor_set(x_5, 0, x_14);
x_16 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__3;
lean_ctor_set_tag(x_4, 7);
lean_ctor_set(x_4, 1, x_16);
lean_ctor_set(x_4, 0, x_5);
x_32 = lean_unbox(x_12);
lean_dec(x_12);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__4;
x_17 = x_33;
goto block_31;
}
else
{
lean_object* x_34; 
x_34 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__5;
x_17 = x_34;
goto block_31;
}
block_31:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = l_Nat_reprFast(x_13);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_MessageData_ofFormat(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_MessageData_paren(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MessageData_paren(x_27);
if (lean_is_scalar(x_7)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_7;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_2);
x_1 = x_6;
x_2 = x_29;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_56; 
x_35 = lean_ctor_get(x_5, 0);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_5);
x_37 = l_Lean_MessageData_ofName(x_9);
x_38 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__2;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__3;
lean_ctor_set_tag(x_4, 7);
lean_ctor_set(x_4, 1, x_40);
lean_ctor_set(x_4, 0, x_39);
x_56 = lean_unbox(x_35);
lean_dec(x_35);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__4;
x_41 = x_57;
goto block_55;
}
else
{
lean_object* x_58; 
x_58 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__5;
x_41 = x_58;
goto block_55;
}
block_55:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_42 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = l_Lean_MessageData_ofFormat(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
x_46 = l_Nat_reprFast(x_36);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_MessageData_ofFormat(x_47);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_MessageData_paren(x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_MessageData_paren(x_51);
if (lean_is_scalar(x_7)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_7;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_2);
x_1 = x_6;
x_2 = x_53;
goto _start;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_83; 
x_59 = lean_ctor_get(x_4, 0);
lean_inc(x_59);
lean_dec(x_4);
x_60 = lean_ctor_get(x_5, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_62 = x_5;
} else {
 lean_dec_ref(x_5);
 x_62 = lean_box(0);
}
x_63 = l_Lean_MessageData_ofName(x_59);
x_64 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__2;
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(7, 2, 0);
} else {
 x_65 = x_62;
 lean_ctor_set_tag(x_65, 7);
}
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__3;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_83 = lean_unbox(x_60);
lean_dec(x_60);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__4;
x_68 = x_84;
goto block_82;
}
else
{
lean_object* x_85; 
x_85 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__5;
x_68 = x_85;
goto block_82;
}
block_82:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_69 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lean_MessageData_ofFormat(x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_64);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
x_73 = l_Nat_reprFast(x_61);
x_74 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = l_Lean_MessageData_ofFormat(x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_MessageData_paren(x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_67);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_MessageData_paren(x_78);
if (lean_is_scalar(x_7)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_7;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_2);
x_1 = x_6;
x_2 = x_80;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Rewrites_rewriteCandidates___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_rewriteCandidates___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Candidate rewrite lemmas:\n", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Rewrites_rewriteCandidates___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwFindDecls), 7, 1);
lean_closure_set(x_10, 0, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(x_10, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_12);
x_16 = l_Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0(x_12, x_14, x_15);
x_17 = l_Lean_Meta_Rewrites_rewriteCandidates___closed__2;
x_18 = lean_array_size(x_16);
x_19 = 0;
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___redArg(x_4, x_16, x_18, x_19, x_17, x_13);
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_24 = x_20;
} else {
 lean_dec_ref(x_20);
 x_24 = lean_box(0);
}
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_dec(x_27);
x_36 = l_Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites___hyg_46_;
x_37 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_36, x_7, x_23);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_free_object(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_28 = x_40;
goto block_35;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_37, 1);
x_43 = lean_ctor_get(x_37, 0);
lean_dec(x_43);
x_44 = l_Lean_Meta_Rewrites_rewriteCandidates___closed__4;
lean_inc(x_26);
x_45 = lean_array_to_list(x_26);
x_46 = lean_box(0);
x_47 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5(x_45, x_46);
x_48 = l_Lean_MessageData_ofList(x_47);
lean_ctor_set_tag(x_37, 7);
lean_ctor_set(x_37, 1, x_48);
lean_ctor_set(x_37, 0, x_44);
x_49 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_49);
lean_ctor_set(x_22, 0, x_37);
x_50 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_36, x_22, x_5, x_6, x_7, x_8, x_42);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_28 = x_51;
goto block_35;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_dec(x_37);
x_53 = l_Lean_Meta_Rewrites_rewriteCandidates___closed__4;
lean_inc(x_26);
x_54 = lean_array_to_list(x_26);
x_55 = lean_box(0);
x_56 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5(x_54, x_55);
x_57 = l_Lean_MessageData_ofList(x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_59);
lean_ctor_set(x_22, 0, x_58);
x_60 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_36, x_22, x_5, x_6, x_7, x_8, x_52);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_28 = x_61;
goto block_35;
}
}
block_35:
{
size_t x_29; lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_array_size(x_1);
x_30 = l_Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__3(x_29, x_19, x_1);
x_31 = lean_array_size(x_26);
x_32 = l_Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__4(x_31, x_19, x_26);
x_33 = l_Array_append___redArg(x_30, x_32);
lean_dec(x_32);
if (lean_is_scalar(x_24)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_24;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_62 = lean_ctor_get(x_22, 0);
lean_inc(x_62);
lean_dec(x_22);
x_71 = l_Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites___hyg_46_;
x_72 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_71, x_7, x_23);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_63 = x_75;
goto block_70;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_77 = x_72;
} else {
 lean_dec_ref(x_72);
 x_77 = lean_box(0);
}
x_78 = l_Lean_Meta_Rewrites_rewriteCandidates___closed__4;
lean_inc(x_62);
x_79 = lean_array_to_list(x_62);
x_80 = lean_box(0);
x_81 = l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5(x_79, x_80);
x_82 = l_Lean_MessageData_ofList(x_81);
if (lean_is_scalar(x_77)) {
 x_83 = lean_alloc_ctor(7, 2, 0);
} else {
 x_83 = x_77;
 lean_ctor_set_tag(x_83, 7);
}
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_71, x_85, x_5, x_6, x_7, x_8, x_76);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_63 = x_87;
goto block_70;
}
block_70:
{
size_t x_64; lean_object* x_65; size_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_array_size(x_1);
x_65 = l_Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__3(x_64, x_19, x_1);
x_66 = lean_array_size(x_62);
x_67 = l_Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__4(x_66, x_19, x_62);
x_68 = l_Array_append___redArg(x_65, x_67);
lean_dec(x_67);
if (lean_is_scalar(x_24)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_24;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_11);
if (x_88 == 0)
{
return x_11;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_11, 0);
x_90 = lean_ctor_get(x_11, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_11);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Rewrites_rewriteCandidates(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Rewrites_RewriteResult_newGoal(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0), 10, 5);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___redArg(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Elab_Tactic_saveState___redArg(x_7, x_9, x_11, x_13, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_12, 5);
lean_inc(x_19);
x_20 = lean_box(x_2);
lean_ctor_set(x_15, 1, x_20);
lean_ctor_set(x_15, 0, x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_Rewrites_RewriteResult_newGoal(x_3);
x_24 = l_Option_toLOption___redArg(x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_19);
if (lean_obj_tag(x_5) == 0)
{
x_27 = x_17;
goto block_30;
}
else
{
lean_object* x_31; 
lean_dec(x_17);
x_31 = lean_ctor_get(x_5, 0);
lean_inc(x_31);
lean_dec(x_5);
x_27 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(x_4, x_22, x_24, x_25, x_26, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
return x_29;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_ctor_get(x_12, 5);
lean_inc(x_34);
x_35 = lean_box(x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Meta_Rewrites_RewriteResult_newGoal(x_3);
x_40 = l_Option_toLOption___redArg(x_39);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_34);
if (lean_obj_tag(x_5) == 0)
{
x_43 = x_32;
goto block_46;
}
else
{
lean_object* x_47; 
lean_dec(x_32);
x_47 = lean_ctor_get(x_5, 0);
lean_inc(x_47);
lean_dec(x_5);
x_43 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(x_4, x_38, x_40, x_41, x_42, x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_15 = lean_ctor_get(x_2, 3);
lean_inc(x_15);
x_16 = lean_box(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed), 14, 5);
lean_closure_set(x_17, 0, x_13);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_1);
lean_closure_set(x_17, 4, x_3);
x_18 = l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(x_15, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_16;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_17 = x_11;
} else {
 lean_dec_ref(x_11);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_20 = x_12;
} else {
 lean_dec_ref(x_12);
 x_20 = lean_box(0);
}
x_21 = l_Lean_getRemainingHeartbeats___redArg(x_7, x_9);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_23 = x_4;
} else {
 lean_dec_ref(x_4);
 x_23 = lean_box(0);
}
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_29 = x_22;
} else {
 lean_dec_ref(x_22);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_36 = lean_ctor_get(x_1, 4);
lean_inc(x_36);
x_37 = lean_nat_dec_lt(x_25, x_32);
lean_dec(x_32);
lean_dec(x_25);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_array_get_size(x_27);
x_39 = lean_nat_dec_le(x_31, x_38);
lean_dec(x_38);
lean_dec(x_31);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_free_object(x_21);
x_40 = lean_box(x_35);
lean_inc(x_36);
x_41 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(x_41, 0, x_36);
lean_closure_set(x_41, 1, x_33);
lean_closure_set(x_41, 2, x_34);
lean_closure_set(x_41, 3, x_40);
lean_closure_set(x_41, 4, x_16);
lean_closure_set(x_41, 5, x_18);
lean_closure_set(x_41, 6, x_19);
x_42 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0), 8, 3);
lean_closure_set(x_42, 0, lean_box(0));
lean_closure_set(x_42, 1, x_36);
lean_closure_set(x_42, 2, x_41);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_43 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_42, x_5, x_6, x_7, x_8, x_26);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_20);
lean_dec(x_17);
lean_free_object(x_3);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
if (lean_is_scalar(x_29)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_29;
}
lean_ctor_set(x_46, 0, x_27);
lean_ctor_set(x_46, 1, x_28);
lean_inc(x_2);
if (lean_is_scalar(x_23)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_23;
}
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_46);
x_3 = x_14;
x_4 = x_47;
x_9 = x_45;
goto _start;
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
lean_dec(x_43);
x_52 = lean_ctor_get(x_50, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 3);
lean_inc(x_53);
lean_inc(x_50);
x_54 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_54, 0, x_50);
lean_inc(x_53);
x_55 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0), 8, 3);
lean_closure_set(x_55, 0, lean_box(0));
lean_closure_set(x_55, 1, x_53);
lean_closure_set(x_55, 2, x_54);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_56 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_55, x_5, x_6, x_7, x_8, x_51);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; size_t x_69; size_t x_70; size_t x_71; size_t x_72; size_t x_73; lean_object* x_74; uint8_t x_75; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_28, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_28, 1);
lean_inc(x_60);
x_61 = lean_array_get_size(x_60);
x_62 = lean_string_hash(x_57);
x_63 = 32;
x_64 = lean_uint64_shift_right(x_62, x_63);
x_65 = lean_uint64_xor(x_62, x_64);
x_66 = 16;
x_67 = lean_uint64_shift_right(x_65, x_66);
x_68 = lean_uint64_xor(x_65, x_67);
x_69 = lean_uint64_to_usize(x_68);
x_70 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_71 = 1;
x_72 = lean_usize_sub(x_70, x_71);
x_73 = lean_usize_land(x_69, x_72);
x_74 = lean_array_uget(x_60, x_73);
x_75 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__0___redArg(x_57, x_74);
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_52);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_52, 0);
x_78 = lean_ctor_get(x_52, 2);
lean_dec(x_78);
x_79 = lean_ctor_get(x_52, 1);
lean_dec(x_79);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_80 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_53, x_77, x_5, x_6, x_7, x_8, x_58);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_90; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 1);
if (x_30 == 0)
{
uint8_t x_96; 
lean_free_object(x_80);
lean_dec(x_82);
lean_free_object(x_44);
lean_dec(x_29);
lean_dec(x_23);
lean_free_object(x_3);
x_96 = !lean_is_exclusive(x_28);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_28, 1);
lean_dec(x_97);
x_98 = lean_ctor_get(x_28, 0);
lean_dec(x_98);
x_99 = lean_box(0);
if (x_75 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_add(x_59, x_100);
lean_dec(x_59);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 2, x_74);
lean_ctor_set(x_52, 1, x_99);
lean_ctor_set(x_52, 0, x_57);
x_102 = lean_array_uset(x_60, x_73, x_52);
x_103 = lean_unsigned_to_nat(4u);
x_104 = lean_nat_mul(x_101, x_103);
x_105 = lean_unsigned_to_nat(3u);
x_106 = lean_nat_div(x_104, x_105);
lean_dec(x_104);
x_107 = lean_array_get_size(x_102);
x_108 = lean_nat_dec_le(x_106, x_107);
lean_dec(x_107);
lean_dec(x_106);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_102);
lean_ctor_set(x_28, 1, x_109);
lean_ctor_set(x_28, 0, x_101);
x_90 = x_28;
goto block_95;
}
else
{
lean_ctor_set(x_28, 1, x_102);
lean_ctor_set(x_28, 0, x_101);
x_90 = x_28;
goto block_95;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_free_object(x_52);
x_110 = lean_box(0);
x_111 = lean_array_uset(x_60, x_73, x_110);
x_112 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_57, x_99, x_74);
x_113 = lean_array_uset(x_111, x_73, x_112);
lean_ctor_set(x_28, 1, x_113);
x_90 = x_28;
goto block_95;
}
}
else
{
lean_object* x_114; 
lean_dec(x_28);
x_114 = lean_box(0);
if (x_75 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_add(x_59, x_115);
lean_dec(x_59);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 2, x_74);
lean_ctor_set(x_52, 1, x_114);
lean_ctor_set(x_52, 0, x_57);
x_117 = lean_array_uset(x_60, x_73, x_52);
x_118 = lean_unsigned_to_nat(4u);
x_119 = lean_nat_mul(x_116, x_118);
x_120 = lean_unsigned_to_nat(3u);
x_121 = lean_nat_div(x_119, x_120);
lean_dec(x_119);
x_122 = lean_array_get_size(x_117);
x_123 = lean_nat_dec_le(x_121, x_122);
lean_dec(x_122);
lean_dec(x_121);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_117);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_116);
lean_ctor_set(x_125, 1, x_124);
x_90 = x_125;
goto block_95;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_116);
lean_ctor_set(x_126, 1, x_117);
x_90 = x_126;
goto block_95;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_free_object(x_52);
x_127 = lean_box(0);
x_128 = lean_array_uset(x_60, x_73, x_127);
x_129 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_57, x_114, x_74);
x_130 = lean_array_uset(x_128, x_73, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_59);
lean_ctor_set(x_131, 1, x_130);
x_90 = x_131;
goto block_95;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_20);
lean_dec(x_17);
x_132 = lean_unbox(x_82);
lean_dec(x_82);
if (x_132 == 0)
{
uint8_t x_133; 
lean_free_object(x_80);
lean_free_object(x_44);
lean_free_object(x_3);
x_133 = !lean_is_exclusive(x_28);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_28, 1);
lean_dec(x_134);
x_135 = lean_ctor_get(x_28, 0);
lean_dec(x_135);
x_136 = lean_box(0);
if (x_75 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_nat_add(x_59, x_137);
lean_dec(x_59);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 2, x_74);
lean_ctor_set(x_52, 1, x_136);
lean_ctor_set(x_52, 0, x_57);
x_139 = lean_array_uset(x_60, x_73, x_52);
x_140 = lean_unsigned_to_nat(4u);
x_141 = lean_nat_mul(x_138, x_140);
x_142 = lean_unsigned_to_nat(3u);
x_143 = lean_nat_div(x_141, x_142);
lean_dec(x_141);
x_144 = lean_array_get_size(x_139);
x_145 = lean_nat_dec_le(x_143, x_144);
lean_dec(x_144);
lean_dec(x_143);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_139);
lean_ctor_set(x_28, 1, x_146);
lean_ctor_set(x_28, 0, x_138);
x_84 = x_28;
goto block_89;
}
else
{
lean_ctor_set(x_28, 1, x_139);
lean_ctor_set(x_28, 0, x_138);
x_84 = x_28;
goto block_89;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_free_object(x_52);
x_147 = lean_box(0);
x_148 = lean_array_uset(x_60, x_73, x_147);
x_149 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_57, x_136, x_74);
x_150 = lean_array_uset(x_148, x_73, x_149);
lean_ctor_set(x_28, 1, x_150);
x_84 = x_28;
goto block_89;
}
}
else
{
lean_object* x_151; 
lean_dec(x_28);
x_151 = lean_box(0);
if (x_75 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_152 = lean_unsigned_to_nat(1u);
x_153 = lean_nat_add(x_59, x_152);
lean_dec(x_59);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 2, x_74);
lean_ctor_set(x_52, 1, x_151);
lean_ctor_set(x_52, 0, x_57);
x_154 = lean_array_uset(x_60, x_73, x_52);
x_155 = lean_unsigned_to_nat(4u);
x_156 = lean_nat_mul(x_153, x_155);
x_157 = lean_unsigned_to_nat(3u);
x_158 = lean_nat_div(x_156, x_157);
lean_dec(x_156);
x_159 = lean_array_get_size(x_154);
x_160 = lean_nat_dec_le(x_158, x_159);
lean_dec(x_159);
lean_dec(x_158);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_154);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_153);
lean_ctor_set(x_162, 1, x_161);
x_84 = x_162;
goto block_89;
}
else
{
lean_object* x_163; 
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_153);
lean_ctor_set(x_163, 1, x_154);
x_84 = x_163;
goto block_89;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_free_object(x_52);
x_164 = lean_box(0);
x_165 = lean_array_uset(x_60, x_73, x_164);
x_166 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_57, x_151, x_74);
x_167 = lean_array_uset(x_165, x_73, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_59);
lean_ctor_set(x_168, 1, x_167);
x_84 = x_168;
goto block_89;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_free_object(x_52);
lean_dec(x_74);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_169 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0;
x_170 = lean_array_push(x_169, x_50);
lean_ctor_set(x_44, 0, x_170);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_28);
lean_ctor_set(x_3, 0, x_27);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_44);
lean_ctor_set(x_171, 1, x_3);
lean_ctor_set(x_80, 0, x_171);
return x_80;
}
}
block_89:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_array_push(x_27, x_50);
if (lean_is_scalar(x_29)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_29;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
lean_inc(x_2);
if (lean_is_scalar(x_23)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_23;
}
lean_ctor_set(x_87, 0, x_2);
lean_ctor_set(x_87, 1, x_86);
x_3 = x_14;
x_4 = x_87;
x_9 = x_83;
goto _start;
}
block_95:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_array_push(x_27, x_50);
if (lean_is_scalar(x_20)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_20;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
lean_inc(x_2);
if (lean_is_scalar(x_17)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_17;
}
lean_ctor_set(x_93, 0, x_2);
lean_ctor_set(x_93, 1, x_92);
x_3 = x_14;
x_4 = x_93;
x_9 = x_83;
goto _start;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_180; 
x_172 = lean_ctor_get(x_80, 0);
x_173 = lean_ctor_get(x_80, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_80);
if (x_30 == 0)
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_172);
lean_free_object(x_44);
lean_dec(x_29);
lean_dec(x_23);
lean_free_object(x_3);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_186 = x_28;
} else {
 lean_dec_ref(x_28);
 x_186 = lean_box(0);
}
x_187 = lean_box(0);
if (x_75 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_188 = lean_unsigned_to_nat(1u);
x_189 = lean_nat_add(x_59, x_188);
lean_dec(x_59);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 2, x_74);
lean_ctor_set(x_52, 1, x_187);
lean_ctor_set(x_52, 0, x_57);
x_190 = lean_array_uset(x_60, x_73, x_52);
x_191 = lean_unsigned_to_nat(4u);
x_192 = lean_nat_mul(x_189, x_191);
x_193 = lean_unsigned_to_nat(3u);
x_194 = lean_nat_div(x_192, x_193);
lean_dec(x_192);
x_195 = lean_array_get_size(x_190);
x_196 = lean_nat_dec_le(x_194, x_195);
lean_dec(x_195);
lean_dec(x_194);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_190);
if (lean_is_scalar(x_186)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_186;
}
lean_ctor_set(x_198, 0, x_189);
lean_ctor_set(x_198, 1, x_197);
x_180 = x_198;
goto block_185;
}
else
{
lean_object* x_199; 
if (lean_is_scalar(x_186)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_186;
}
lean_ctor_set(x_199, 0, x_189);
lean_ctor_set(x_199, 1, x_190);
x_180 = x_199;
goto block_185;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_free_object(x_52);
x_200 = lean_box(0);
x_201 = lean_array_uset(x_60, x_73, x_200);
x_202 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_57, x_187, x_74);
x_203 = lean_array_uset(x_201, x_73, x_202);
if (lean_is_scalar(x_186)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_186;
}
lean_ctor_set(x_204, 0, x_59);
lean_ctor_set(x_204, 1, x_203);
x_180 = x_204;
goto block_185;
}
}
else
{
uint8_t x_205; 
lean_dec(x_20);
lean_dec(x_17);
x_205 = lean_unbox(x_172);
lean_dec(x_172);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
lean_free_object(x_44);
lean_free_object(x_3);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_206 = x_28;
} else {
 lean_dec_ref(x_28);
 x_206 = lean_box(0);
}
x_207 = lean_box(0);
if (x_75 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_208 = lean_unsigned_to_nat(1u);
x_209 = lean_nat_add(x_59, x_208);
lean_dec(x_59);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 2, x_74);
lean_ctor_set(x_52, 1, x_207);
lean_ctor_set(x_52, 0, x_57);
x_210 = lean_array_uset(x_60, x_73, x_52);
x_211 = lean_unsigned_to_nat(4u);
x_212 = lean_nat_mul(x_209, x_211);
x_213 = lean_unsigned_to_nat(3u);
x_214 = lean_nat_div(x_212, x_213);
lean_dec(x_212);
x_215 = lean_array_get_size(x_210);
x_216 = lean_nat_dec_le(x_214, x_215);
lean_dec(x_215);
lean_dec(x_214);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_210);
if (lean_is_scalar(x_206)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_206;
}
lean_ctor_set(x_218, 0, x_209);
lean_ctor_set(x_218, 1, x_217);
x_174 = x_218;
goto block_179;
}
else
{
lean_object* x_219; 
if (lean_is_scalar(x_206)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_206;
}
lean_ctor_set(x_219, 0, x_209);
lean_ctor_set(x_219, 1, x_210);
x_174 = x_219;
goto block_179;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_free_object(x_52);
x_220 = lean_box(0);
x_221 = lean_array_uset(x_60, x_73, x_220);
x_222 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_57, x_207, x_74);
x_223 = lean_array_uset(x_221, x_73, x_222);
if (lean_is_scalar(x_206)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_206;
}
lean_ctor_set(x_224, 0, x_59);
lean_ctor_set(x_224, 1, x_223);
x_174 = x_224;
goto block_179;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_free_object(x_52);
lean_dec(x_74);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_225 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0;
x_226 = lean_array_push(x_225, x_50);
lean_ctor_set(x_44, 0, x_226);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_28);
lean_ctor_set(x_3, 0, x_27);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_44);
lean_ctor_set(x_227, 1, x_3);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_173);
return x_228;
}
}
block_179:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_array_push(x_27, x_50);
if (lean_is_scalar(x_29)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_29;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_174);
lean_inc(x_2);
if (lean_is_scalar(x_23)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_23;
}
lean_ctor_set(x_177, 0, x_2);
lean_ctor_set(x_177, 1, x_176);
x_3 = x_14;
x_4 = x_177;
x_9 = x_173;
goto _start;
}
block_185:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_array_push(x_27, x_50);
if (lean_is_scalar(x_20)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_20;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
lean_inc(x_2);
if (lean_is_scalar(x_17)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_17;
}
lean_ctor_set(x_183, 0, x_2);
lean_ctor_set(x_183, 1, x_182);
x_3 = x_14;
x_4 = x_183;
x_9 = x_173;
goto _start;
}
}
}
else
{
uint8_t x_229; 
lean_free_object(x_52);
lean_dec(x_74);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_free_object(x_44);
lean_dec(x_50);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_229 = !lean_is_exclusive(x_80);
if (x_229 == 0)
{
return x_80;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_80, 0);
x_231 = lean_ctor_get(x_80, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_80);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
else
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_52, 0);
lean_inc(x_233);
lean_dec(x_52);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_234 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_53, x_233, x_5, x_6, x_7, x_8, x_58);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_244; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_237 = x_234;
} else {
 lean_dec_ref(x_234);
 x_237 = lean_box(0);
}
if (x_30 == 0)
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_237);
lean_dec(x_235);
lean_free_object(x_44);
lean_dec(x_29);
lean_dec(x_23);
lean_free_object(x_3);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_250 = x_28;
} else {
 lean_dec_ref(x_28);
 x_250 = lean_box(0);
}
x_251 = lean_box(0);
if (x_75 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_252 = lean_unsigned_to_nat(1u);
x_253 = lean_nat_add(x_59, x_252);
lean_dec(x_59);
x_254 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_254, 0, x_57);
lean_ctor_set(x_254, 1, x_251);
lean_ctor_set(x_254, 2, x_74);
x_255 = lean_array_uset(x_60, x_73, x_254);
x_256 = lean_unsigned_to_nat(4u);
x_257 = lean_nat_mul(x_253, x_256);
x_258 = lean_unsigned_to_nat(3u);
x_259 = lean_nat_div(x_257, x_258);
lean_dec(x_257);
x_260 = lean_array_get_size(x_255);
x_261 = lean_nat_dec_le(x_259, x_260);
lean_dec(x_260);
lean_dec(x_259);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_255);
if (lean_is_scalar(x_250)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_250;
}
lean_ctor_set(x_263, 0, x_253);
lean_ctor_set(x_263, 1, x_262);
x_244 = x_263;
goto block_249;
}
else
{
lean_object* x_264; 
if (lean_is_scalar(x_250)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_250;
}
lean_ctor_set(x_264, 0, x_253);
lean_ctor_set(x_264, 1, x_255);
x_244 = x_264;
goto block_249;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_265 = lean_box(0);
x_266 = lean_array_uset(x_60, x_73, x_265);
x_267 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_57, x_251, x_74);
x_268 = lean_array_uset(x_266, x_73, x_267);
if (lean_is_scalar(x_250)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_250;
}
lean_ctor_set(x_269, 0, x_59);
lean_ctor_set(x_269, 1, x_268);
x_244 = x_269;
goto block_249;
}
}
else
{
uint8_t x_270; 
lean_dec(x_20);
lean_dec(x_17);
x_270 = lean_unbox(x_235);
lean_dec(x_235);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_237);
lean_free_object(x_44);
lean_free_object(x_3);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_271 = x_28;
} else {
 lean_dec_ref(x_28);
 x_271 = lean_box(0);
}
x_272 = lean_box(0);
if (x_75 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_273 = lean_unsigned_to_nat(1u);
x_274 = lean_nat_add(x_59, x_273);
lean_dec(x_59);
x_275 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_275, 0, x_57);
lean_ctor_set(x_275, 1, x_272);
lean_ctor_set(x_275, 2, x_74);
x_276 = lean_array_uset(x_60, x_73, x_275);
x_277 = lean_unsigned_to_nat(4u);
x_278 = lean_nat_mul(x_274, x_277);
x_279 = lean_unsigned_to_nat(3u);
x_280 = lean_nat_div(x_278, x_279);
lean_dec(x_278);
x_281 = lean_array_get_size(x_276);
x_282 = lean_nat_dec_le(x_280, x_281);
lean_dec(x_281);
lean_dec(x_280);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_276);
if (lean_is_scalar(x_271)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_271;
}
lean_ctor_set(x_284, 0, x_274);
lean_ctor_set(x_284, 1, x_283);
x_238 = x_284;
goto block_243;
}
else
{
lean_object* x_285; 
if (lean_is_scalar(x_271)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_271;
}
lean_ctor_set(x_285, 0, x_274);
lean_ctor_set(x_285, 1, x_276);
x_238 = x_285;
goto block_243;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_286 = lean_box(0);
x_287 = lean_array_uset(x_60, x_73, x_286);
x_288 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_57, x_272, x_74);
x_289 = lean_array_uset(x_287, x_73, x_288);
if (lean_is_scalar(x_271)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_271;
}
lean_ctor_set(x_290, 0, x_59);
lean_ctor_set(x_290, 1, x_289);
x_238 = x_290;
goto block_243;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_74);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_291 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0;
x_292 = lean_array_push(x_291, x_50);
lean_ctor_set(x_44, 0, x_292);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_28);
lean_ctor_set(x_3, 0, x_27);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_44);
lean_ctor_set(x_293, 1, x_3);
if (lean_is_scalar(x_237)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_237;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_236);
return x_294;
}
}
block_243:
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_array_push(x_27, x_50);
if (lean_is_scalar(x_29)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_29;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_238);
lean_inc(x_2);
if (lean_is_scalar(x_23)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_23;
}
lean_ctor_set(x_241, 0, x_2);
lean_ctor_set(x_241, 1, x_240);
x_3 = x_14;
x_4 = x_241;
x_9 = x_236;
goto _start;
}
block_249:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_array_push(x_27, x_50);
if (lean_is_scalar(x_20)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_20;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_244);
lean_inc(x_2);
if (lean_is_scalar(x_17)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_17;
}
lean_ctor_set(x_247, 0, x_2);
lean_ctor_set(x_247, 1, x_246);
x_3 = x_14;
x_4 = x_247;
x_9 = x_236;
goto _start;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_74);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_free_object(x_44);
lean_dec(x_50);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_295 = lean_ctor_get(x_234, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_234, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_297 = x_234;
} else {
 lean_dec_ref(x_234);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_295);
lean_ctor_set(x_298, 1, x_296);
return x_298;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; 
lean_dec(x_74);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_52);
lean_free_object(x_44);
lean_dec(x_50);
lean_dec(x_20);
lean_dec(x_17);
lean_free_object(x_3);
if (lean_is_scalar(x_29)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_29;
}
lean_ctor_set(x_299, 0, x_27);
lean_ctor_set(x_299, 1, x_28);
lean_inc(x_2);
if (lean_is_scalar(x_23)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_23;
}
lean_ctor_set(x_300, 0, x_2);
lean_ctor_set(x_300, 1, x_299);
x_3 = x_14;
x_4 = x_300;
x_9 = x_58;
goto _start;
}
}
else
{
uint8_t x_302; 
lean_dec(x_53);
lean_dec(x_52);
lean_free_object(x_44);
lean_dec(x_50);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_302 = !lean_is_exclusive(x_56);
if (x_302 == 0)
{
return x_56;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_56, 0);
x_304 = lean_ctor_get(x_56, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_56);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_306 = lean_ctor_get(x_44, 0);
lean_inc(x_306);
lean_dec(x_44);
x_307 = lean_ctor_get(x_43, 1);
lean_inc(x_307);
lean_dec(x_43);
x_308 = lean_ctor_get(x_306, 2);
lean_inc(x_308);
x_309 = lean_ctor_get(x_306, 3);
lean_inc(x_309);
lean_inc(x_306);
x_310 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_310, 0, x_306);
lean_inc(x_309);
x_311 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0), 8, 3);
lean_closure_set(x_311, 0, lean_box(0));
lean_closure_set(x_311, 1, x_309);
lean_closure_set(x_311, 2, x_310);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_312 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_311, x_5, x_6, x_7, x_8, x_307);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint64_t x_318; uint64_t x_319; uint64_t x_320; uint64_t x_321; uint64_t x_322; uint64_t x_323; uint64_t x_324; size_t x_325; size_t x_326; size_t x_327; size_t x_328; size_t x_329; lean_object* x_330; uint8_t x_331; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = lean_ctor_get(x_28, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_28, 1);
lean_inc(x_316);
x_317 = lean_array_get_size(x_316);
x_318 = lean_string_hash(x_313);
x_319 = 32;
x_320 = lean_uint64_shift_right(x_318, x_319);
x_321 = lean_uint64_xor(x_318, x_320);
x_322 = 16;
x_323 = lean_uint64_shift_right(x_321, x_322);
x_324 = lean_uint64_xor(x_321, x_323);
x_325 = lean_uint64_to_usize(x_324);
x_326 = lean_usize_of_nat(x_317);
lean_dec(x_317);
x_327 = 1;
x_328 = lean_usize_sub(x_326, x_327);
x_329 = lean_usize_land(x_325, x_328);
x_330 = lean_array_uget(x_316, x_329);
x_331 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__0___redArg(x_313, x_330);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_308, 0);
lean_inc(x_332);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 lean_ctor_release(x_308, 2);
 x_333 = x_308;
} else {
 lean_dec_ref(x_308);
 x_333 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_334 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_309, x_332, x_5, x_6, x_7, x_8, x_314);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_344; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_337 = x_334;
} else {
 lean_dec_ref(x_334);
 x_337 = lean_box(0);
}
if (x_30 == 0)
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_337);
lean_dec(x_335);
lean_dec(x_29);
lean_dec(x_23);
lean_free_object(x_3);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_350 = x_28;
} else {
 lean_dec_ref(x_28);
 x_350 = lean_box(0);
}
x_351 = lean_box(0);
if (x_331 == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; 
x_352 = lean_unsigned_to_nat(1u);
x_353 = lean_nat_add(x_315, x_352);
lean_dec(x_315);
if (lean_is_scalar(x_333)) {
 x_354 = lean_alloc_ctor(1, 3, 0);
} else {
 x_354 = x_333;
 lean_ctor_set_tag(x_354, 1);
}
lean_ctor_set(x_354, 0, x_313);
lean_ctor_set(x_354, 1, x_351);
lean_ctor_set(x_354, 2, x_330);
x_355 = lean_array_uset(x_316, x_329, x_354);
x_356 = lean_unsigned_to_nat(4u);
x_357 = lean_nat_mul(x_353, x_356);
x_358 = lean_unsigned_to_nat(3u);
x_359 = lean_nat_div(x_357, x_358);
lean_dec(x_357);
x_360 = lean_array_get_size(x_355);
x_361 = lean_nat_dec_le(x_359, x_360);
lean_dec(x_360);
lean_dec(x_359);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; 
x_362 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_355);
if (lean_is_scalar(x_350)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_350;
}
lean_ctor_set(x_363, 0, x_353);
lean_ctor_set(x_363, 1, x_362);
x_344 = x_363;
goto block_349;
}
else
{
lean_object* x_364; 
if (lean_is_scalar(x_350)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_350;
}
lean_ctor_set(x_364, 0, x_353);
lean_ctor_set(x_364, 1, x_355);
x_344 = x_364;
goto block_349;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_333);
x_365 = lean_box(0);
x_366 = lean_array_uset(x_316, x_329, x_365);
x_367 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_313, x_351, x_330);
x_368 = lean_array_uset(x_366, x_329, x_367);
if (lean_is_scalar(x_350)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_350;
}
lean_ctor_set(x_369, 0, x_315);
lean_ctor_set(x_369, 1, x_368);
x_344 = x_369;
goto block_349;
}
}
else
{
uint8_t x_370; 
lean_dec(x_20);
lean_dec(x_17);
x_370 = lean_unbox(x_335);
lean_dec(x_335);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; 
lean_dec(x_337);
lean_free_object(x_3);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_371 = x_28;
} else {
 lean_dec_ref(x_28);
 x_371 = lean_box(0);
}
x_372 = lean_box(0);
if (x_331 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; 
x_373 = lean_unsigned_to_nat(1u);
x_374 = lean_nat_add(x_315, x_373);
lean_dec(x_315);
if (lean_is_scalar(x_333)) {
 x_375 = lean_alloc_ctor(1, 3, 0);
} else {
 x_375 = x_333;
 lean_ctor_set_tag(x_375, 1);
}
lean_ctor_set(x_375, 0, x_313);
lean_ctor_set(x_375, 1, x_372);
lean_ctor_set(x_375, 2, x_330);
x_376 = lean_array_uset(x_316, x_329, x_375);
x_377 = lean_unsigned_to_nat(4u);
x_378 = lean_nat_mul(x_374, x_377);
x_379 = lean_unsigned_to_nat(3u);
x_380 = lean_nat_div(x_378, x_379);
lean_dec(x_378);
x_381 = lean_array_get_size(x_376);
x_382 = lean_nat_dec_le(x_380, x_381);
lean_dec(x_381);
lean_dec(x_380);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; 
x_383 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_376);
if (lean_is_scalar(x_371)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_371;
}
lean_ctor_set(x_384, 0, x_374);
lean_ctor_set(x_384, 1, x_383);
x_338 = x_384;
goto block_343;
}
else
{
lean_object* x_385; 
if (lean_is_scalar(x_371)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_371;
}
lean_ctor_set(x_385, 0, x_374);
lean_ctor_set(x_385, 1, x_376);
x_338 = x_385;
goto block_343;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_333);
x_386 = lean_box(0);
x_387 = lean_array_uset(x_316, x_329, x_386);
x_388 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_313, x_372, x_330);
x_389 = lean_array_uset(x_387, x_329, x_388);
if (lean_is_scalar(x_371)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_371;
}
lean_ctor_set(x_390, 0, x_315);
lean_ctor_set(x_390, 1, x_389);
x_338 = x_390;
goto block_343;
}
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_333);
lean_dec(x_330);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_313);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_391 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0;
x_392 = lean_array_push(x_391, x_306);
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_28);
lean_ctor_set(x_3, 0, x_27);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_3);
if (lean_is_scalar(x_337)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_337;
}
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_336);
return x_395;
}
}
block_343:
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_array_push(x_27, x_306);
if (lean_is_scalar(x_29)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_29;
}
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_338);
lean_inc(x_2);
if (lean_is_scalar(x_23)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_23;
}
lean_ctor_set(x_341, 0, x_2);
lean_ctor_set(x_341, 1, x_340);
x_3 = x_14;
x_4 = x_341;
x_9 = x_336;
goto _start;
}
block_349:
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_array_push(x_27, x_306);
if (lean_is_scalar(x_20)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_20;
}
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_344);
lean_inc(x_2);
if (lean_is_scalar(x_17)) {
 x_347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_347 = x_17;
}
lean_ctor_set(x_347, 0, x_2);
lean_ctor_set(x_347, 1, x_346);
x_3 = x_14;
x_4 = x_347;
x_9 = x_336;
goto _start;
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_333);
lean_dec(x_330);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_313);
lean_dec(x_306);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_396 = lean_ctor_get(x_334, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_334, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_398 = x_334;
} else {
 lean_dec_ref(x_334);
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
else
{
lean_object* x_400; lean_object* x_401; 
lean_dec(x_330);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_313);
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_306);
lean_dec(x_20);
lean_dec(x_17);
lean_free_object(x_3);
if (lean_is_scalar(x_29)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_29;
}
lean_ctor_set(x_400, 0, x_27);
lean_ctor_set(x_400, 1, x_28);
lean_inc(x_2);
if (lean_is_scalar(x_23)) {
 x_401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_401 = x_23;
}
lean_ctor_set(x_401, 0, x_2);
lean_ctor_set(x_401, 1, x_400);
x_3 = x_14;
x_4 = x_401;
x_9 = x_314;
goto _start;
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_306);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_403 = lean_ctor_get(x_312, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_312, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_405 = x_312;
} else {
 lean_dec_ref(x_312);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 2, 0);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_404);
return x_406;
}
}
}
}
else
{
uint8_t x_407; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_407 = !lean_is_exclusive(x_43);
if (x_407 == 0)
{
return x_43;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_43, 0);
x_409 = lean_ctor_get(x_43, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_43);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
return x_410;
}
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_27);
x_411 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_411, 0, x_27);
if (lean_is_scalar(x_29)) {
 x_412 = lean_alloc_ctor(0, 2, 0);
} else {
 x_412 = x_29;
}
lean_ctor_set(x_412, 0, x_27);
lean_ctor_set(x_412, 1, x_28);
if (lean_is_scalar(x_23)) {
 x_413 = lean_alloc_ctor(0, 2, 0);
} else {
 x_413 = x_23;
}
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
lean_ctor_set(x_21, 0, x_413);
return x_21;
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_27);
x_414 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_414, 0, x_27);
if (lean_is_scalar(x_29)) {
 x_415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_415 = x_29;
}
lean_ctor_set(x_415, 0, x_27);
lean_ctor_set(x_415, 1, x_28);
if (lean_is_scalar(x_23)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_23;
}
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
lean_ctor_set(x_21, 0, x_416);
return x_21;
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; uint8_t x_429; 
x_417 = lean_ctor_get(x_21, 0);
x_418 = lean_ctor_get(x_21, 1);
lean_inc(x_418);
lean_inc(x_417);
lean_dec(x_21);
x_419 = lean_ctor_get(x_22, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_22, 1);
lean_inc(x_420);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_421 = x_22;
} else {
 lean_dec_ref(x_22);
 x_421 = lean_box(0);
}
x_422 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_423 = lean_ctor_get(x_1, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_1, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_1, 2);
lean_inc(x_425);
x_426 = lean_ctor_get(x_1, 3);
lean_inc(x_426);
x_427 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_428 = lean_ctor_get(x_1, 4);
lean_inc(x_428);
x_429 = lean_nat_dec_lt(x_417, x_424);
lean_dec(x_424);
lean_dec(x_417);
if (x_429 == 0)
{
lean_object* x_430; uint8_t x_431; 
x_430 = lean_array_get_size(x_419);
x_431 = lean_nat_dec_le(x_423, x_430);
lean_dec(x_430);
lean_dec(x_423);
if (x_431 == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_432 = lean_box(x_427);
lean_inc(x_428);
x_433 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(x_433, 0, x_428);
lean_closure_set(x_433, 1, x_425);
lean_closure_set(x_433, 2, x_426);
lean_closure_set(x_433, 3, x_432);
lean_closure_set(x_433, 4, x_16);
lean_closure_set(x_433, 5, x_18);
lean_closure_set(x_433, 6, x_19);
x_434 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0), 8, 3);
lean_closure_set(x_434, 0, lean_box(0));
lean_closure_set(x_434, 1, x_428);
lean_closure_set(x_434, 2, x_433);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_435 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_434, x_5, x_6, x_7, x_8, x_418);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_20);
lean_dec(x_17);
lean_free_object(x_3);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec(x_435);
if (lean_is_scalar(x_421)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_421;
}
lean_ctor_set(x_438, 0, x_419);
lean_ctor_set(x_438, 1, x_420);
lean_inc(x_2);
if (lean_is_scalar(x_23)) {
 x_439 = lean_alloc_ctor(0, 2, 0);
} else {
 x_439 = x_23;
}
lean_ctor_set(x_439, 0, x_2);
lean_ctor_set(x_439, 1, x_438);
x_3 = x_14;
x_4 = x_439;
x_9 = x_437;
goto _start;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_441 = lean_ctor_get(x_436, 0);
lean_inc(x_441);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 x_442 = x_436;
} else {
 lean_dec_ref(x_436);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_435, 1);
lean_inc(x_443);
lean_dec(x_435);
x_444 = lean_ctor_get(x_441, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_441, 3);
lean_inc(x_445);
lean_inc(x_441);
x_446 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_446, 0, x_441);
lean_inc(x_445);
x_447 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0), 8, 3);
lean_closure_set(x_447, 0, lean_box(0));
lean_closure_set(x_447, 1, x_445);
lean_closure_set(x_447, 2, x_446);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_448 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_447, x_5, x_6, x_7, x_8, x_443);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint64_t x_454; uint64_t x_455; uint64_t x_456; uint64_t x_457; uint64_t x_458; uint64_t x_459; uint64_t x_460; size_t x_461; size_t x_462; size_t x_463; size_t x_464; size_t x_465; lean_object* x_466; uint8_t x_467; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
x_451 = lean_ctor_get(x_420, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_420, 1);
lean_inc(x_452);
x_453 = lean_array_get_size(x_452);
x_454 = lean_string_hash(x_449);
x_455 = 32;
x_456 = lean_uint64_shift_right(x_454, x_455);
x_457 = lean_uint64_xor(x_454, x_456);
x_458 = 16;
x_459 = lean_uint64_shift_right(x_457, x_458);
x_460 = lean_uint64_xor(x_457, x_459);
x_461 = lean_uint64_to_usize(x_460);
x_462 = lean_usize_of_nat(x_453);
lean_dec(x_453);
x_463 = 1;
x_464 = lean_usize_sub(x_462, x_463);
x_465 = lean_usize_land(x_461, x_464);
x_466 = lean_array_uget(x_452, x_465);
x_467 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__0___redArg(x_449, x_466);
if (x_467 == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_468 = lean_ctor_get(x_444, 0);
lean_inc(x_468);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 lean_ctor_release(x_444, 2);
 x_469 = x_444;
} else {
 lean_dec_ref(x_444);
 x_469 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_470 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_445, x_468, x_5, x_6, x_7, x_8, x_450);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_480; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_473 = x_470;
} else {
 lean_dec_ref(x_470);
 x_473 = lean_box(0);
}
if (x_422 == 0)
{
lean_object* x_486; lean_object* x_487; 
lean_dec(x_473);
lean_dec(x_471);
lean_dec(x_442);
lean_dec(x_421);
lean_dec(x_23);
lean_free_object(x_3);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_486 = x_420;
} else {
 lean_dec_ref(x_420);
 x_486 = lean_box(0);
}
x_487 = lean_box(0);
if (x_467 == 0)
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; 
x_488 = lean_unsigned_to_nat(1u);
x_489 = lean_nat_add(x_451, x_488);
lean_dec(x_451);
if (lean_is_scalar(x_469)) {
 x_490 = lean_alloc_ctor(1, 3, 0);
} else {
 x_490 = x_469;
 lean_ctor_set_tag(x_490, 1);
}
lean_ctor_set(x_490, 0, x_449);
lean_ctor_set(x_490, 1, x_487);
lean_ctor_set(x_490, 2, x_466);
x_491 = lean_array_uset(x_452, x_465, x_490);
x_492 = lean_unsigned_to_nat(4u);
x_493 = lean_nat_mul(x_489, x_492);
x_494 = lean_unsigned_to_nat(3u);
x_495 = lean_nat_div(x_493, x_494);
lean_dec(x_493);
x_496 = lean_array_get_size(x_491);
x_497 = lean_nat_dec_le(x_495, x_496);
lean_dec(x_496);
lean_dec(x_495);
if (x_497 == 0)
{
lean_object* x_498; lean_object* x_499; 
x_498 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_491);
if (lean_is_scalar(x_486)) {
 x_499 = lean_alloc_ctor(0, 2, 0);
} else {
 x_499 = x_486;
}
lean_ctor_set(x_499, 0, x_489);
lean_ctor_set(x_499, 1, x_498);
x_480 = x_499;
goto block_485;
}
else
{
lean_object* x_500; 
if (lean_is_scalar(x_486)) {
 x_500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_500 = x_486;
}
lean_ctor_set(x_500, 0, x_489);
lean_ctor_set(x_500, 1, x_491);
x_480 = x_500;
goto block_485;
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
lean_dec(x_469);
x_501 = lean_box(0);
x_502 = lean_array_uset(x_452, x_465, x_501);
x_503 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_449, x_487, x_466);
x_504 = lean_array_uset(x_502, x_465, x_503);
if (lean_is_scalar(x_486)) {
 x_505 = lean_alloc_ctor(0, 2, 0);
} else {
 x_505 = x_486;
}
lean_ctor_set(x_505, 0, x_451);
lean_ctor_set(x_505, 1, x_504);
x_480 = x_505;
goto block_485;
}
}
else
{
uint8_t x_506; 
lean_dec(x_20);
lean_dec(x_17);
x_506 = lean_unbox(x_471);
lean_dec(x_471);
if (x_506 == 0)
{
lean_object* x_507; lean_object* x_508; 
lean_dec(x_473);
lean_dec(x_442);
lean_free_object(x_3);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_507 = x_420;
} else {
 lean_dec_ref(x_420);
 x_507 = lean_box(0);
}
x_508 = lean_box(0);
if (x_467 == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; 
x_509 = lean_unsigned_to_nat(1u);
x_510 = lean_nat_add(x_451, x_509);
lean_dec(x_451);
if (lean_is_scalar(x_469)) {
 x_511 = lean_alloc_ctor(1, 3, 0);
} else {
 x_511 = x_469;
 lean_ctor_set_tag(x_511, 1);
}
lean_ctor_set(x_511, 0, x_449);
lean_ctor_set(x_511, 1, x_508);
lean_ctor_set(x_511, 2, x_466);
x_512 = lean_array_uset(x_452, x_465, x_511);
x_513 = lean_unsigned_to_nat(4u);
x_514 = lean_nat_mul(x_510, x_513);
x_515 = lean_unsigned_to_nat(3u);
x_516 = lean_nat_div(x_514, x_515);
lean_dec(x_514);
x_517 = lean_array_get_size(x_512);
x_518 = lean_nat_dec_le(x_516, x_517);
lean_dec(x_517);
lean_dec(x_516);
if (x_518 == 0)
{
lean_object* x_519; lean_object* x_520; 
x_519 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_512);
if (lean_is_scalar(x_507)) {
 x_520 = lean_alloc_ctor(0, 2, 0);
} else {
 x_520 = x_507;
}
lean_ctor_set(x_520, 0, x_510);
lean_ctor_set(x_520, 1, x_519);
x_474 = x_520;
goto block_479;
}
else
{
lean_object* x_521; 
if (lean_is_scalar(x_507)) {
 x_521 = lean_alloc_ctor(0, 2, 0);
} else {
 x_521 = x_507;
}
lean_ctor_set(x_521, 0, x_510);
lean_ctor_set(x_521, 1, x_512);
x_474 = x_521;
goto block_479;
}
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
lean_dec(x_469);
x_522 = lean_box(0);
x_523 = lean_array_uset(x_452, x_465, x_522);
x_524 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_449, x_508, x_466);
x_525 = lean_array_uset(x_523, x_465, x_524);
if (lean_is_scalar(x_507)) {
 x_526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_526 = x_507;
}
lean_ctor_set(x_526, 0, x_451);
lean_ctor_set(x_526, 1, x_525);
x_474 = x_526;
goto block_479;
}
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_469);
lean_dec(x_466);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_449);
lean_dec(x_421);
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_527 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0;
x_528 = lean_array_push(x_527, x_441);
if (lean_is_scalar(x_442)) {
 x_529 = lean_alloc_ctor(1, 1, 0);
} else {
 x_529 = x_442;
}
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_420);
lean_ctor_set(x_3, 0, x_419);
x_530 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_530, 0, x_529);
lean_ctor_set(x_530, 1, x_3);
if (lean_is_scalar(x_473)) {
 x_531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_531 = x_473;
}
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_472);
return x_531;
}
}
block_479:
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_array_push(x_419, x_441);
if (lean_is_scalar(x_421)) {
 x_476 = lean_alloc_ctor(0, 2, 0);
} else {
 x_476 = x_421;
}
lean_ctor_set(x_476, 0, x_475);
lean_ctor_set(x_476, 1, x_474);
lean_inc(x_2);
if (lean_is_scalar(x_23)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_23;
}
lean_ctor_set(x_477, 0, x_2);
lean_ctor_set(x_477, 1, x_476);
x_3 = x_14;
x_4 = x_477;
x_9 = x_472;
goto _start;
}
block_485:
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_array_push(x_419, x_441);
if (lean_is_scalar(x_20)) {
 x_482 = lean_alloc_ctor(0, 2, 0);
} else {
 x_482 = x_20;
}
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_480);
lean_inc(x_2);
if (lean_is_scalar(x_17)) {
 x_483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_483 = x_17;
}
lean_ctor_set(x_483, 0, x_2);
lean_ctor_set(x_483, 1, x_482);
x_3 = x_14;
x_4 = x_483;
x_9 = x_472;
goto _start;
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_469);
lean_dec(x_466);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_449);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_532 = lean_ctor_get(x_470, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_470, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_534 = x_470;
} else {
 lean_dec_ref(x_470);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(1, 2, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_532);
lean_ctor_set(x_535, 1, x_533);
return x_535;
}
}
else
{
lean_object* x_536; lean_object* x_537; 
lean_dec(x_466);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_449);
lean_dec(x_445);
lean_dec(x_444);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_20);
lean_dec(x_17);
lean_free_object(x_3);
if (lean_is_scalar(x_421)) {
 x_536 = lean_alloc_ctor(0, 2, 0);
} else {
 x_536 = x_421;
}
lean_ctor_set(x_536, 0, x_419);
lean_ctor_set(x_536, 1, x_420);
lean_inc(x_2);
if (lean_is_scalar(x_23)) {
 x_537 = lean_alloc_ctor(0, 2, 0);
} else {
 x_537 = x_23;
}
lean_ctor_set(x_537, 0, x_2);
lean_ctor_set(x_537, 1, x_536);
x_3 = x_14;
x_4 = x_537;
x_9 = x_450;
goto _start;
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_445);
lean_dec(x_444);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_539 = lean_ctor_get(x_448, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_448, 1);
lean_inc(x_540);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 x_541 = x_448;
} else {
 lean_dec_ref(x_448);
 x_541 = lean_box(0);
}
if (lean_is_scalar(x_541)) {
 x_542 = lean_alloc_ctor(1, 2, 0);
} else {
 x_542 = x_541;
}
lean_ctor_set(x_542, 0, x_539);
lean_ctor_set(x_542, 1, x_540);
return x_542;
}
}
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_543 = lean_ctor_get(x_435, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_435, 1);
lean_inc(x_544);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_545 = x_435;
} else {
 lean_dec_ref(x_435);
 x_545 = lean_box(0);
}
if (lean_is_scalar(x_545)) {
 x_546 = lean_alloc_ctor(1, 2, 0);
} else {
 x_546 = x_545;
}
lean_ctor_set(x_546, 0, x_543);
lean_ctor_set(x_546, 1, x_544);
return x_546;
}
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_428);
lean_dec(x_426);
lean_dec(x_425);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_419);
x_547 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_547, 0, x_419);
if (lean_is_scalar(x_421)) {
 x_548 = lean_alloc_ctor(0, 2, 0);
} else {
 x_548 = x_421;
}
lean_ctor_set(x_548, 0, x_419);
lean_ctor_set(x_548, 1, x_420);
if (lean_is_scalar(x_23)) {
 x_549 = lean_alloc_ctor(0, 2, 0);
} else {
 x_549 = x_23;
}
lean_ctor_set(x_549, 0, x_547);
lean_ctor_set(x_549, 1, x_548);
x_550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_418);
return x_550;
}
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec(x_428);
lean_dec(x_426);
lean_dec(x_425);
lean_dec(x_423);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_419);
x_551 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_551, 0, x_419);
if (lean_is_scalar(x_421)) {
 x_552 = lean_alloc_ctor(0, 2, 0);
} else {
 x_552 = x_421;
}
lean_ctor_set(x_552, 0, x_419);
lean_ctor_set(x_552, 1, x_420);
if (lean_is_scalar(x_23)) {
 x_553 = lean_alloc_ctor(0, 2, 0);
} else {
 x_553 = x_23;
}
lean_ctor_set(x_553, 0, x_551);
lean_ctor_set(x_553, 1, x_552);
x_554 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_554, 0, x_553);
lean_ctor_set(x_554, 1, x_418);
return x_554;
}
}
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; uint8_t x_575; lean_object* x_576; uint8_t x_577; 
x_555 = lean_ctor_get(x_3, 1);
lean_inc(x_555);
lean_dec(x_3);
x_556 = lean_ctor_get(x_11, 0);
lean_inc(x_556);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_557 = x_11;
} else {
 lean_dec_ref(x_11);
 x_557 = lean_box(0);
}
x_558 = lean_ctor_get(x_12, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_12, 1);
lean_inc(x_559);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_560 = x_12;
} else {
 lean_dec_ref(x_12);
 x_560 = lean_box(0);
}
x_561 = l_Lean_getRemainingHeartbeats___redArg(x_7, x_9);
x_562 = lean_ctor_get(x_4, 1);
lean_inc(x_562);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_563 = x_4;
} else {
 lean_dec_ref(x_4);
 x_563 = lean_box(0);
}
x_564 = lean_ctor_get(x_561, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_561, 1);
lean_inc(x_565);
if (lean_is_exclusive(x_561)) {
 lean_ctor_release(x_561, 0);
 lean_ctor_release(x_561, 1);
 x_566 = x_561;
} else {
 lean_dec_ref(x_561);
 x_566 = lean_box(0);
}
x_567 = lean_ctor_get(x_562, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_562, 1);
lean_inc(x_568);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_569 = x_562;
} else {
 lean_dec_ref(x_562);
 x_569 = lean_box(0);
}
x_570 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_571 = lean_ctor_get(x_1, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_1, 1);
lean_inc(x_572);
x_573 = lean_ctor_get(x_1, 2);
lean_inc(x_573);
x_574 = lean_ctor_get(x_1, 3);
lean_inc(x_574);
x_575 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_576 = lean_ctor_get(x_1, 4);
lean_inc(x_576);
x_577 = lean_nat_dec_lt(x_564, x_572);
lean_dec(x_572);
lean_dec(x_564);
if (x_577 == 0)
{
lean_object* x_578; uint8_t x_579; 
x_578 = lean_array_get_size(x_567);
x_579 = lean_nat_dec_le(x_571, x_578);
lean_dec(x_578);
lean_dec(x_571);
if (x_579 == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_dec(x_566);
x_580 = lean_box(x_575);
lean_inc(x_576);
x_581 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(x_581, 0, x_576);
lean_closure_set(x_581, 1, x_573);
lean_closure_set(x_581, 2, x_574);
lean_closure_set(x_581, 3, x_580);
lean_closure_set(x_581, 4, x_556);
lean_closure_set(x_581, 5, x_558);
lean_closure_set(x_581, 6, x_559);
x_582 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0), 8, 3);
lean_closure_set(x_582, 0, lean_box(0));
lean_closure_set(x_582, 1, x_576);
lean_closure_set(x_582, 2, x_581);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_583 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_582, x_5, x_6, x_7, x_8, x_565);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_560);
lean_dec(x_557);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
lean_dec(x_583);
if (lean_is_scalar(x_569)) {
 x_586 = lean_alloc_ctor(0, 2, 0);
} else {
 x_586 = x_569;
}
lean_ctor_set(x_586, 0, x_567);
lean_ctor_set(x_586, 1, x_568);
lean_inc(x_2);
if (lean_is_scalar(x_563)) {
 x_587 = lean_alloc_ctor(0, 2, 0);
} else {
 x_587 = x_563;
}
lean_ctor_set(x_587, 0, x_2);
lean_ctor_set(x_587, 1, x_586);
x_3 = x_555;
x_4 = x_587;
x_9 = x_585;
goto _start;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_589 = lean_ctor_get(x_584, 0);
lean_inc(x_589);
if (lean_is_exclusive(x_584)) {
 lean_ctor_release(x_584, 0);
 x_590 = x_584;
} else {
 lean_dec_ref(x_584);
 x_590 = lean_box(0);
}
x_591 = lean_ctor_get(x_583, 1);
lean_inc(x_591);
lean_dec(x_583);
x_592 = lean_ctor_get(x_589, 2);
lean_inc(x_592);
x_593 = lean_ctor_get(x_589, 3);
lean_inc(x_593);
lean_inc(x_589);
x_594 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_594, 0, x_589);
lean_inc(x_593);
x_595 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0), 8, 3);
lean_closure_set(x_595, 0, lean_box(0));
lean_closure_set(x_595, 1, x_593);
lean_closure_set(x_595, 2, x_594);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_596 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_595, x_5, x_6, x_7, x_8, x_591);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; uint64_t x_602; uint64_t x_603; uint64_t x_604; uint64_t x_605; uint64_t x_606; uint64_t x_607; uint64_t x_608; size_t x_609; size_t x_610; size_t x_611; size_t x_612; size_t x_613; lean_object* x_614; uint8_t x_615; 
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_596, 1);
lean_inc(x_598);
lean_dec(x_596);
x_599 = lean_ctor_get(x_568, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_568, 1);
lean_inc(x_600);
x_601 = lean_array_get_size(x_600);
x_602 = lean_string_hash(x_597);
x_603 = 32;
x_604 = lean_uint64_shift_right(x_602, x_603);
x_605 = lean_uint64_xor(x_602, x_604);
x_606 = 16;
x_607 = lean_uint64_shift_right(x_605, x_606);
x_608 = lean_uint64_xor(x_605, x_607);
x_609 = lean_uint64_to_usize(x_608);
x_610 = lean_usize_of_nat(x_601);
lean_dec(x_601);
x_611 = 1;
x_612 = lean_usize_sub(x_610, x_611);
x_613 = lean_usize_land(x_609, x_612);
x_614 = lean_array_uget(x_600, x_613);
x_615 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__0___redArg(x_597, x_614);
if (x_615 == 0)
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_616 = lean_ctor_get(x_592, 0);
lean_inc(x_616);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 lean_ctor_release(x_592, 2);
 x_617 = x_592;
} else {
 lean_dec_ref(x_592);
 x_617 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_618 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_593, x_616, x_5, x_6, x_7, x_8, x_598);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_628; 
x_619 = lean_ctor_get(x_618, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_618, 1);
lean_inc(x_620);
if (lean_is_exclusive(x_618)) {
 lean_ctor_release(x_618, 0);
 lean_ctor_release(x_618, 1);
 x_621 = x_618;
} else {
 lean_dec_ref(x_618);
 x_621 = lean_box(0);
}
if (x_570 == 0)
{
lean_object* x_634; lean_object* x_635; 
lean_dec(x_621);
lean_dec(x_619);
lean_dec(x_590);
lean_dec(x_569);
lean_dec(x_563);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_634 = x_568;
} else {
 lean_dec_ref(x_568);
 x_634 = lean_box(0);
}
x_635 = lean_box(0);
if (x_615 == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; uint8_t x_645; 
x_636 = lean_unsigned_to_nat(1u);
x_637 = lean_nat_add(x_599, x_636);
lean_dec(x_599);
if (lean_is_scalar(x_617)) {
 x_638 = lean_alloc_ctor(1, 3, 0);
} else {
 x_638 = x_617;
 lean_ctor_set_tag(x_638, 1);
}
lean_ctor_set(x_638, 0, x_597);
lean_ctor_set(x_638, 1, x_635);
lean_ctor_set(x_638, 2, x_614);
x_639 = lean_array_uset(x_600, x_613, x_638);
x_640 = lean_unsigned_to_nat(4u);
x_641 = lean_nat_mul(x_637, x_640);
x_642 = lean_unsigned_to_nat(3u);
x_643 = lean_nat_div(x_641, x_642);
lean_dec(x_641);
x_644 = lean_array_get_size(x_639);
x_645 = lean_nat_dec_le(x_643, x_644);
lean_dec(x_644);
lean_dec(x_643);
if (x_645 == 0)
{
lean_object* x_646; lean_object* x_647; 
x_646 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_639);
if (lean_is_scalar(x_634)) {
 x_647 = lean_alloc_ctor(0, 2, 0);
} else {
 x_647 = x_634;
}
lean_ctor_set(x_647, 0, x_637);
lean_ctor_set(x_647, 1, x_646);
x_628 = x_647;
goto block_633;
}
else
{
lean_object* x_648; 
if (lean_is_scalar(x_634)) {
 x_648 = lean_alloc_ctor(0, 2, 0);
} else {
 x_648 = x_634;
}
lean_ctor_set(x_648, 0, x_637);
lean_ctor_set(x_648, 1, x_639);
x_628 = x_648;
goto block_633;
}
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_617);
x_649 = lean_box(0);
x_650 = lean_array_uset(x_600, x_613, x_649);
x_651 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_597, x_635, x_614);
x_652 = lean_array_uset(x_650, x_613, x_651);
if (lean_is_scalar(x_634)) {
 x_653 = lean_alloc_ctor(0, 2, 0);
} else {
 x_653 = x_634;
}
lean_ctor_set(x_653, 0, x_599);
lean_ctor_set(x_653, 1, x_652);
x_628 = x_653;
goto block_633;
}
}
else
{
uint8_t x_654; 
lean_dec(x_560);
lean_dec(x_557);
x_654 = lean_unbox(x_619);
lean_dec(x_619);
if (x_654 == 0)
{
lean_object* x_655; lean_object* x_656; 
lean_dec(x_621);
lean_dec(x_590);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_655 = x_568;
} else {
 lean_dec_ref(x_568);
 x_655 = lean_box(0);
}
x_656 = lean_box(0);
if (x_615 == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; uint8_t x_666; 
x_657 = lean_unsigned_to_nat(1u);
x_658 = lean_nat_add(x_599, x_657);
lean_dec(x_599);
if (lean_is_scalar(x_617)) {
 x_659 = lean_alloc_ctor(1, 3, 0);
} else {
 x_659 = x_617;
 lean_ctor_set_tag(x_659, 1);
}
lean_ctor_set(x_659, 0, x_597);
lean_ctor_set(x_659, 1, x_656);
lean_ctor_set(x_659, 2, x_614);
x_660 = lean_array_uset(x_600, x_613, x_659);
x_661 = lean_unsigned_to_nat(4u);
x_662 = lean_nat_mul(x_658, x_661);
x_663 = lean_unsigned_to_nat(3u);
x_664 = lean_nat_div(x_662, x_663);
lean_dec(x_662);
x_665 = lean_array_get_size(x_660);
x_666 = lean_nat_dec_le(x_664, x_665);
lean_dec(x_665);
lean_dec(x_664);
if (x_666 == 0)
{
lean_object* x_667; lean_object* x_668; 
x_667 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_660);
if (lean_is_scalar(x_655)) {
 x_668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_668 = x_655;
}
lean_ctor_set(x_668, 0, x_658);
lean_ctor_set(x_668, 1, x_667);
x_622 = x_668;
goto block_627;
}
else
{
lean_object* x_669; 
if (lean_is_scalar(x_655)) {
 x_669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_669 = x_655;
}
lean_ctor_set(x_669, 0, x_658);
lean_ctor_set(x_669, 1, x_660);
x_622 = x_669;
goto block_627;
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
lean_dec(x_617);
x_670 = lean_box(0);
x_671 = lean_array_uset(x_600, x_613, x_670);
x_672 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_597, x_656, x_614);
x_673 = lean_array_uset(x_671, x_613, x_672);
if (lean_is_scalar(x_655)) {
 x_674 = lean_alloc_ctor(0, 2, 0);
} else {
 x_674 = x_655;
}
lean_ctor_set(x_674, 0, x_599);
lean_ctor_set(x_674, 1, x_673);
x_622 = x_674;
goto block_627;
}
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
lean_dec(x_617);
lean_dec(x_614);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_597);
lean_dec(x_569);
lean_dec(x_563);
lean_dec(x_555);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_675 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0;
x_676 = lean_array_push(x_675, x_589);
if (lean_is_scalar(x_590)) {
 x_677 = lean_alloc_ctor(1, 1, 0);
} else {
 x_677 = x_590;
}
lean_ctor_set(x_677, 0, x_676);
x_678 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_678, 0, x_567);
lean_ctor_set(x_678, 1, x_568);
x_679 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_679, 0, x_677);
lean_ctor_set(x_679, 1, x_678);
if (lean_is_scalar(x_621)) {
 x_680 = lean_alloc_ctor(0, 2, 0);
} else {
 x_680 = x_621;
}
lean_ctor_set(x_680, 0, x_679);
lean_ctor_set(x_680, 1, x_620);
return x_680;
}
}
block_627:
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_623 = lean_array_push(x_567, x_589);
if (lean_is_scalar(x_569)) {
 x_624 = lean_alloc_ctor(0, 2, 0);
} else {
 x_624 = x_569;
}
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_624, 1, x_622);
lean_inc(x_2);
if (lean_is_scalar(x_563)) {
 x_625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_625 = x_563;
}
lean_ctor_set(x_625, 0, x_2);
lean_ctor_set(x_625, 1, x_624);
x_3 = x_555;
x_4 = x_625;
x_9 = x_620;
goto _start;
}
block_633:
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = lean_array_push(x_567, x_589);
if (lean_is_scalar(x_560)) {
 x_630 = lean_alloc_ctor(0, 2, 0);
} else {
 x_630 = x_560;
}
lean_ctor_set(x_630, 0, x_629);
lean_ctor_set(x_630, 1, x_628);
lean_inc(x_2);
if (lean_is_scalar(x_557)) {
 x_631 = lean_alloc_ctor(0, 2, 0);
} else {
 x_631 = x_557;
}
lean_ctor_set(x_631, 0, x_2);
lean_ctor_set(x_631, 1, x_630);
x_3 = x_555;
x_4 = x_631;
x_9 = x_620;
goto _start;
}
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_617);
lean_dec(x_614);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_597);
lean_dec(x_590);
lean_dec(x_589);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_567);
lean_dec(x_563);
lean_dec(x_560);
lean_dec(x_557);
lean_dec(x_555);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_681 = lean_ctor_get(x_618, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_618, 1);
lean_inc(x_682);
if (lean_is_exclusive(x_618)) {
 lean_ctor_release(x_618, 0);
 lean_ctor_release(x_618, 1);
 x_683 = x_618;
} else {
 lean_dec_ref(x_618);
 x_683 = lean_box(0);
}
if (lean_is_scalar(x_683)) {
 x_684 = lean_alloc_ctor(1, 2, 0);
} else {
 x_684 = x_683;
}
lean_ctor_set(x_684, 0, x_681);
lean_ctor_set(x_684, 1, x_682);
return x_684;
}
}
else
{
lean_object* x_685; lean_object* x_686; 
lean_dec(x_614);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_597);
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_590);
lean_dec(x_589);
lean_dec(x_560);
lean_dec(x_557);
if (lean_is_scalar(x_569)) {
 x_685 = lean_alloc_ctor(0, 2, 0);
} else {
 x_685 = x_569;
}
lean_ctor_set(x_685, 0, x_567);
lean_ctor_set(x_685, 1, x_568);
lean_inc(x_2);
if (lean_is_scalar(x_563)) {
 x_686 = lean_alloc_ctor(0, 2, 0);
} else {
 x_686 = x_563;
}
lean_ctor_set(x_686, 0, x_2);
lean_ctor_set(x_686, 1, x_685);
x_3 = x_555;
x_4 = x_686;
x_9 = x_598;
goto _start;
}
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_590);
lean_dec(x_589);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_567);
lean_dec(x_563);
lean_dec(x_560);
lean_dec(x_557);
lean_dec(x_555);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_688 = lean_ctor_get(x_596, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_596, 1);
lean_inc(x_689);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_690 = x_596;
} else {
 lean_dec_ref(x_596);
 x_690 = lean_box(0);
}
if (lean_is_scalar(x_690)) {
 x_691 = lean_alloc_ctor(1, 2, 0);
} else {
 x_691 = x_690;
}
lean_ctor_set(x_691, 0, x_688);
lean_ctor_set(x_691, 1, x_689);
return x_691;
}
}
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_567);
lean_dec(x_563);
lean_dec(x_560);
lean_dec(x_557);
lean_dec(x_555);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_692 = lean_ctor_get(x_583, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_583, 1);
lean_inc(x_693);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 x_694 = x_583;
} else {
 lean_dec_ref(x_583);
 x_694 = lean_box(0);
}
if (lean_is_scalar(x_694)) {
 x_695 = lean_alloc_ctor(1, 2, 0);
} else {
 x_695 = x_694;
}
lean_ctor_set(x_695, 0, x_692);
lean_ctor_set(x_695, 1, x_693);
return x_695;
}
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec(x_576);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_555);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_567);
x_696 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_696, 0, x_567);
if (lean_is_scalar(x_569)) {
 x_697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_697 = x_569;
}
lean_ctor_set(x_697, 0, x_567);
lean_ctor_set(x_697, 1, x_568);
if (lean_is_scalar(x_563)) {
 x_698 = lean_alloc_ctor(0, 2, 0);
} else {
 x_698 = x_563;
}
lean_ctor_set(x_698, 0, x_696);
lean_ctor_set(x_698, 1, x_697);
if (lean_is_scalar(x_566)) {
 x_699 = lean_alloc_ctor(0, 2, 0);
} else {
 x_699 = x_566;
}
lean_ctor_set(x_699, 0, x_698);
lean_ctor_set(x_699, 1, x_565);
return x_699;
}
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
lean_dec(x_576);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_571);
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_555);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_567);
x_700 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_700, 0, x_567);
if (lean_is_scalar(x_569)) {
 x_701 = lean_alloc_ctor(0, 2, 0);
} else {
 x_701 = x_569;
}
lean_ctor_set(x_701, 0, x_567);
lean_ctor_set(x_701, 1, x_568);
if (lean_is_scalar(x_563)) {
 x_702 = lean_alloc_ctor(0, 2, 0);
} else {
 x_702 = x_563;
}
lean_ctor_set(x_702, 0, x_700);
lean_ctor_set(x_702, 1, x_701);
if (lean_is_scalar(x_566)) {
 x_703 = lean_alloc_ctor(0, 2, 0);
} else {
 x_703 = x_566;
}
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_565);
return x_703;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_19 = x_13;
} else {
 lean_dec_ref(x_13);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_22 = x_14;
} else {
 lean_dec_ref(x_14);
 x_22 = lean_box(0);
}
x_23 = l_Lean_getRemainingHeartbeats___redArg(x_9, x_11);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_25 = x_6;
} else {
 lean_dec_ref(x_6);
 x_25 = lean_box(0);
}
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_38 = lean_ctor_get(x_1, 4);
lean_inc(x_38);
x_39 = lean_nat_dec_lt(x_27, x_34);
lean_dec(x_34);
lean_dec(x_27);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_array_get_size(x_29);
x_41 = lean_nat_dec_le(x_33, x_40);
lean_dec(x_40);
lean_dec(x_33);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_23);
x_42 = lean_box(x_37);
lean_inc(x_38);
x_43 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(x_43, 0, x_38);
lean_closure_set(x_43, 1, x_35);
lean_closure_set(x_43, 2, x_36);
lean_closure_set(x_43, 3, x_42);
lean_closure_set(x_43, 4, x_18);
lean_closure_set(x_43, 5, x_20);
lean_closure_set(x_43, 6, x_21);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0), 8, 3);
lean_closure_set(x_44, 0, lean_box(0));
lean_closure_set(x_44, 1, x_38);
lean_closure_set(x_44, 2, x_43);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_45 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_44, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_22);
lean_dec(x_19);
lean_free_object(x_5);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
if (lean_is_scalar(x_31)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_31;
}
lean_ctor_set(x_48, 0, x_29);
lean_ctor_set(x_48, 1, x_30);
lean_inc(x_2);
if (lean_is_scalar(x_25)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_25;
}
lean_ctor_set(x_49, 0, x_2);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_16, x_49, x_7, x_8, x_9, x_10, x_47);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_46, 0);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_dec(x_45);
x_54 = lean_ctor_get(x_52, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 3);
lean_inc(x_55);
lean_inc(x_52);
x_56 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_56, 0, x_52);
lean_inc(x_55);
x_57 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0), 8, 3);
lean_closure_set(x_57, 0, lean_box(0));
lean_closure_set(x_57, 1, x_55);
lean_closure_set(x_57, 2, x_56);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_58 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_57, x_7, x_8, x_9, x_10, x_53);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; size_t x_71; size_t x_72; size_t x_73; size_t x_74; size_t x_75; lean_object* x_76; uint8_t x_77; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_30, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_30, 1);
lean_inc(x_62);
x_63 = lean_array_get_size(x_62);
x_64 = lean_string_hash(x_59);
x_65 = 32;
x_66 = lean_uint64_shift_right(x_64, x_65);
x_67 = lean_uint64_xor(x_64, x_66);
x_68 = 16;
x_69 = lean_uint64_shift_right(x_67, x_68);
x_70 = lean_uint64_xor(x_67, x_69);
x_71 = lean_uint64_to_usize(x_70);
x_72 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_73 = 1;
x_74 = lean_usize_sub(x_72, x_73);
x_75 = lean_usize_land(x_71, x_74);
x_76 = lean_array_uget(x_62, x_75);
x_77 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__0___redArg(x_59, x_76);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_54);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_54, 0);
x_80 = lean_ctor_get(x_54, 2);
lean_dec(x_80);
x_81 = lean_ctor_get(x_54, 1);
lean_dec(x_81);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_82 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_55, x_79, x_7, x_8, x_9, x_10, x_60);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_92; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_ctor_get(x_82, 1);
if (x_32 == 0)
{
uint8_t x_98; 
lean_free_object(x_82);
lean_dec(x_84);
lean_free_object(x_46);
lean_dec(x_31);
lean_dec(x_25);
lean_free_object(x_5);
x_98 = !lean_is_exclusive(x_30);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_30, 1);
lean_dec(x_99);
x_100 = lean_ctor_get(x_30, 0);
lean_dec(x_100);
x_101 = lean_box(0);
if (x_77 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_nat_add(x_61, x_102);
lean_dec(x_61);
lean_ctor_set_tag(x_54, 1);
lean_ctor_set(x_54, 2, x_76);
lean_ctor_set(x_54, 1, x_101);
lean_ctor_set(x_54, 0, x_59);
x_104 = lean_array_uset(x_62, x_75, x_54);
x_105 = lean_unsigned_to_nat(4u);
x_106 = lean_nat_mul(x_103, x_105);
x_107 = lean_unsigned_to_nat(3u);
x_108 = lean_nat_div(x_106, x_107);
lean_dec(x_106);
x_109 = lean_array_get_size(x_104);
x_110 = lean_nat_dec_le(x_108, x_109);
lean_dec(x_109);
lean_dec(x_108);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_104);
lean_ctor_set(x_30, 1, x_111);
lean_ctor_set(x_30, 0, x_103);
x_92 = x_30;
goto block_97;
}
else
{
lean_ctor_set(x_30, 1, x_104);
lean_ctor_set(x_30, 0, x_103);
x_92 = x_30;
goto block_97;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_free_object(x_54);
x_112 = lean_box(0);
x_113 = lean_array_uset(x_62, x_75, x_112);
x_114 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_59, x_101, x_76);
x_115 = lean_array_uset(x_113, x_75, x_114);
lean_ctor_set(x_30, 1, x_115);
x_92 = x_30;
goto block_97;
}
}
else
{
lean_object* x_116; 
lean_dec(x_30);
x_116 = lean_box(0);
if (x_77 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_nat_add(x_61, x_117);
lean_dec(x_61);
lean_ctor_set_tag(x_54, 1);
lean_ctor_set(x_54, 2, x_76);
lean_ctor_set(x_54, 1, x_116);
lean_ctor_set(x_54, 0, x_59);
x_119 = lean_array_uset(x_62, x_75, x_54);
x_120 = lean_unsigned_to_nat(4u);
x_121 = lean_nat_mul(x_118, x_120);
x_122 = lean_unsigned_to_nat(3u);
x_123 = lean_nat_div(x_121, x_122);
lean_dec(x_121);
x_124 = lean_array_get_size(x_119);
x_125 = lean_nat_dec_le(x_123, x_124);
lean_dec(x_124);
lean_dec(x_123);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_119);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_118);
lean_ctor_set(x_127, 1, x_126);
x_92 = x_127;
goto block_97;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_118);
lean_ctor_set(x_128, 1, x_119);
x_92 = x_128;
goto block_97;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_free_object(x_54);
x_129 = lean_box(0);
x_130 = lean_array_uset(x_62, x_75, x_129);
x_131 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_59, x_116, x_76);
x_132 = lean_array_uset(x_130, x_75, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_61);
lean_ctor_set(x_133, 1, x_132);
x_92 = x_133;
goto block_97;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_22);
lean_dec(x_19);
x_134 = lean_unbox(x_84);
lean_dec(x_84);
if (x_134 == 0)
{
uint8_t x_135; 
lean_free_object(x_82);
lean_free_object(x_46);
lean_free_object(x_5);
x_135 = !lean_is_exclusive(x_30);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_30, 1);
lean_dec(x_136);
x_137 = lean_ctor_get(x_30, 0);
lean_dec(x_137);
x_138 = lean_box(0);
if (x_77 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_nat_add(x_61, x_139);
lean_dec(x_61);
lean_ctor_set_tag(x_54, 1);
lean_ctor_set(x_54, 2, x_76);
lean_ctor_set(x_54, 1, x_138);
lean_ctor_set(x_54, 0, x_59);
x_141 = lean_array_uset(x_62, x_75, x_54);
x_142 = lean_unsigned_to_nat(4u);
x_143 = lean_nat_mul(x_140, x_142);
x_144 = lean_unsigned_to_nat(3u);
x_145 = lean_nat_div(x_143, x_144);
lean_dec(x_143);
x_146 = lean_array_get_size(x_141);
x_147 = lean_nat_dec_le(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (x_147 == 0)
{
lean_object* x_148; 
x_148 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_141);
lean_ctor_set(x_30, 1, x_148);
lean_ctor_set(x_30, 0, x_140);
x_86 = x_30;
goto block_91;
}
else
{
lean_ctor_set(x_30, 1, x_141);
lean_ctor_set(x_30, 0, x_140);
x_86 = x_30;
goto block_91;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_free_object(x_54);
x_149 = lean_box(0);
x_150 = lean_array_uset(x_62, x_75, x_149);
x_151 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_59, x_138, x_76);
x_152 = lean_array_uset(x_150, x_75, x_151);
lean_ctor_set(x_30, 1, x_152);
x_86 = x_30;
goto block_91;
}
}
else
{
lean_object* x_153; 
lean_dec(x_30);
x_153 = lean_box(0);
if (x_77 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_154 = lean_unsigned_to_nat(1u);
x_155 = lean_nat_add(x_61, x_154);
lean_dec(x_61);
lean_ctor_set_tag(x_54, 1);
lean_ctor_set(x_54, 2, x_76);
lean_ctor_set(x_54, 1, x_153);
lean_ctor_set(x_54, 0, x_59);
x_156 = lean_array_uset(x_62, x_75, x_54);
x_157 = lean_unsigned_to_nat(4u);
x_158 = lean_nat_mul(x_155, x_157);
x_159 = lean_unsigned_to_nat(3u);
x_160 = lean_nat_div(x_158, x_159);
lean_dec(x_158);
x_161 = lean_array_get_size(x_156);
x_162 = lean_nat_dec_le(x_160, x_161);
lean_dec(x_161);
lean_dec(x_160);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_156);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_155);
lean_ctor_set(x_164, 1, x_163);
x_86 = x_164;
goto block_91;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_155);
lean_ctor_set(x_165, 1, x_156);
x_86 = x_165;
goto block_91;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_free_object(x_54);
x_166 = lean_box(0);
x_167 = lean_array_uset(x_62, x_75, x_166);
x_168 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_59, x_153, x_76);
x_169 = lean_array_uset(x_167, x_75, x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_61);
lean_ctor_set(x_170, 1, x_169);
x_86 = x_170;
goto block_91;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_free_object(x_54);
lean_dec(x_76);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_171 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0;
x_172 = lean_array_push(x_171, x_52);
lean_ctor_set(x_46, 0, x_172);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_29);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_46);
lean_ctor_set(x_173, 1, x_5);
lean_ctor_set(x_82, 0, x_173);
return x_82;
}
}
block_91:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_array_push(x_29, x_52);
if (lean_is_scalar(x_31)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_31;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
lean_inc(x_2);
if (lean_is_scalar(x_25)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_25;
}
lean_ctor_set(x_89, 0, x_2);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_16, x_89, x_7, x_8, x_9, x_10, x_85);
return x_90;
}
block_97:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_array_push(x_29, x_52);
if (lean_is_scalar(x_22)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_22;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
lean_inc(x_2);
if (lean_is_scalar(x_19)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_19;
}
lean_ctor_set(x_95, 0, x_2);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_16, x_95, x_7, x_8, x_9, x_10, x_85);
return x_96;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_182; 
x_174 = lean_ctor_get(x_82, 0);
x_175 = lean_ctor_get(x_82, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_82);
if (x_32 == 0)
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_174);
lean_free_object(x_46);
lean_dec(x_31);
lean_dec(x_25);
lean_free_object(x_5);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_188 = x_30;
} else {
 lean_dec_ref(x_30);
 x_188 = lean_box(0);
}
x_189 = lean_box(0);
if (x_77 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_190 = lean_unsigned_to_nat(1u);
x_191 = lean_nat_add(x_61, x_190);
lean_dec(x_61);
lean_ctor_set_tag(x_54, 1);
lean_ctor_set(x_54, 2, x_76);
lean_ctor_set(x_54, 1, x_189);
lean_ctor_set(x_54, 0, x_59);
x_192 = lean_array_uset(x_62, x_75, x_54);
x_193 = lean_unsigned_to_nat(4u);
x_194 = lean_nat_mul(x_191, x_193);
x_195 = lean_unsigned_to_nat(3u);
x_196 = lean_nat_div(x_194, x_195);
lean_dec(x_194);
x_197 = lean_array_get_size(x_192);
x_198 = lean_nat_dec_le(x_196, x_197);
lean_dec(x_197);
lean_dec(x_196);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_192);
if (lean_is_scalar(x_188)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_188;
}
lean_ctor_set(x_200, 0, x_191);
lean_ctor_set(x_200, 1, x_199);
x_182 = x_200;
goto block_187;
}
else
{
lean_object* x_201; 
if (lean_is_scalar(x_188)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_188;
}
lean_ctor_set(x_201, 0, x_191);
lean_ctor_set(x_201, 1, x_192);
x_182 = x_201;
goto block_187;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_free_object(x_54);
x_202 = lean_box(0);
x_203 = lean_array_uset(x_62, x_75, x_202);
x_204 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_59, x_189, x_76);
x_205 = lean_array_uset(x_203, x_75, x_204);
if (lean_is_scalar(x_188)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_188;
}
lean_ctor_set(x_206, 0, x_61);
lean_ctor_set(x_206, 1, x_205);
x_182 = x_206;
goto block_187;
}
}
else
{
uint8_t x_207; 
lean_dec(x_22);
lean_dec(x_19);
x_207 = lean_unbox(x_174);
lean_dec(x_174);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; 
lean_free_object(x_46);
lean_free_object(x_5);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_208 = x_30;
} else {
 lean_dec_ref(x_30);
 x_208 = lean_box(0);
}
x_209 = lean_box(0);
if (x_77 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_210 = lean_unsigned_to_nat(1u);
x_211 = lean_nat_add(x_61, x_210);
lean_dec(x_61);
lean_ctor_set_tag(x_54, 1);
lean_ctor_set(x_54, 2, x_76);
lean_ctor_set(x_54, 1, x_209);
lean_ctor_set(x_54, 0, x_59);
x_212 = lean_array_uset(x_62, x_75, x_54);
x_213 = lean_unsigned_to_nat(4u);
x_214 = lean_nat_mul(x_211, x_213);
x_215 = lean_unsigned_to_nat(3u);
x_216 = lean_nat_div(x_214, x_215);
lean_dec(x_214);
x_217 = lean_array_get_size(x_212);
x_218 = lean_nat_dec_le(x_216, x_217);
lean_dec(x_217);
lean_dec(x_216);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_212);
if (lean_is_scalar(x_208)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_208;
}
lean_ctor_set(x_220, 0, x_211);
lean_ctor_set(x_220, 1, x_219);
x_176 = x_220;
goto block_181;
}
else
{
lean_object* x_221; 
if (lean_is_scalar(x_208)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_208;
}
lean_ctor_set(x_221, 0, x_211);
lean_ctor_set(x_221, 1, x_212);
x_176 = x_221;
goto block_181;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_free_object(x_54);
x_222 = lean_box(0);
x_223 = lean_array_uset(x_62, x_75, x_222);
x_224 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_59, x_209, x_76);
x_225 = lean_array_uset(x_223, x_75, x_224);
if (lean_is_scalar(x_208)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_208;
}
lean_ctor_set(x_226, 0, x_61);
lean_ctor_set(x_226, 1, x_225);
x_176 = x_226;
goto block_181;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_free_object(x_54);
lean_dec(x_76);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_227 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0;
x_228 = lean_array_push(x_227, x_52);
lean_ctor_set(x_46, 0, x_228);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_29);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_46);
lean_ctor_set(x_229, 1, x_5);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_175);
return x_230;
}
}
block_181:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_array_push(x_29, x_52);
if (lean_is_scalar(x_31)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_31;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
lean_inc(x_2);
if (lean_is_scalar(x_25)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_25;
}
lean_ctor_set(x_179, 0, x_2);
lean_ctor_set(x_179, 1, x_178);
x_180 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_16, x_179, x_7, x_8, x_9, x_10, x_175);
return x_180;
}
block_187:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_array_push(x_29, x_52);
if (lean_is_scalar(x_22)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_22;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
lean_inc(x_2);
if (lean_is_scalar(x_19)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_19;
}
lean_ctor_set(x_185, 0, x_2);
lean_ctor_set(x_185, 1, x_184);
x_186 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_16, x_185, x_7, x_8, x_9, x_10, x_175);
return x_186;
}
}
}
else
{
uint8_t x_231; 
lean_free_object(x_54);
lean_dec(x_76);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_59);
lean_free_object(x_46);
lean_dec(x_52);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_231 = !lean_is_exclusive(x_82);
if (x_231 == 0)
{
return x_82;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_82, 0);
x_233 = lean_ctor_get(x_82, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_82);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_54, 0);
lean_inc(x_235);
lean_dec(x_54);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_236 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_55, x_235, x_7, x_8, x_9, x_10, x_60);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_246; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_239 = x_236;
} else {
 lean_dec_ref(x_236);
 x_239 = lean_box(0);
}
if (x_32 == 0)
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_239);
lean_dec(x_237);
lean_free_object(x_46);
lean_dec(x_31);
lean_dec(x_25);
lean_free_object(x_5);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_252 = x_30;
} else {
 lean_dec_ref(x_30);
 x_252 = lean_box(0);
}
x_253 = lean_box(0);
if (x_77 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_254 = lean_unsigned_to_nat(1u);
x_255 = lean_nat_add(x_61, x_254);
lean_dec(x_61);
x_256 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_256, 0, x_59);
lean_ctor_set(x_256, 1, x_253);
lean_ctor_set(x_256, 2, x_76);
x_257 = lean_array_uset(x_62, x_75, x_256);
x_258 = lean_unsigned_to_nat(4u);
x_259 = lean_nat_mul(x_255, x_258);
x_260 = lean_unsigned_to_nat(3u);
x_261 = lean_nat_div(x_259, x_260);
lean_dec(x_259);
x_262 = lean_array_get_size(x_257);
x_263 = lean_nat_dec_le(x_261, x_262);
lean_dec(x_262);
lean_dec(x_261);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_257);
if (lean_is_scalar(x_252)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_252;
}
lean_ctor_set(x_265, 0, x_255);
lean_ctor_set(x_265, 1, x_264);
x_246 = x_265;
goto block_251;
}
else
{
lean_object* x_266; 
if (lean_is_scalar(x_252)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_252;
}
lean_ctor_set(x_266, 0, x_255);
lean_ctor_set(x_266, 1, x_257);
x_246 = x_266;
goto block_251;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_267 = lean_box(0);
x_268 = lean_array_uset(x_62, x_75, x_267);
x_269 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_59, x_253, x_76);
x_270 = lean_array_uset(x_268, x_75, x_269);
if (lean_is_scalar(x_252)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_252;
}
lean_ctor_set(x_271, 0, x_61);
lean_ctor_set(x_271, 1, x_270);
x_246 = x_271;
goto block_251;
}
}
else
{
uint8_t x_272; 
lean_dec(x_22);
lean_dec(x_19);
x_272 = lean_unbox(x_237);
lean_dec(x_237);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; 
lean_dec(x_239);
lean_free_object(x_46);
lean_free_object(x_5);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_273 = x_30;
} else {
 lean_dec_ref(x_30);
 x_273 = lean_box(0);
}
x_274 = lean_box(0);
if (x_77 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_275 = lean_unsigned_to_nat(1u);
x_276 = lean_nat_add(x_61, x_275);
lean_dec(x_61);
x_277 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_277, 0, x_59);
lean_ctor_set(x_277, 1, x_274);
lean_ctor_set(x_277, 2, x_76);
x_278 = lean_array_uset(x_62, x_75, x_277);
x_279 = lean_unsigned_to_nat(4u);
x_280 = lean_nat_mul(x_276, x_279);
x_281 = lean_unsigned_to_nat(3u);
x_282 = lean_nat_div(x_280, x_281);
lean_dec(x_280);
x_283 = lean_array_get_size(x_278);
x_284 = lean_nat_dec_le(x_282, x_283);
lean_dec(x_283);
lean_dec(x_282);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; 
x_285 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_278);
if (lean_is_scalar(x_273)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_273;
}
lean_ctor_set(x_286, 0, x_276);
lean_ctor_set(x_286, 1, x_285);
x_240 = x_286;
goto block_245;
}
else
{
lean_object* x_287; 
if (lean_is_scalar(x_273)) {
 x_287 = lean_alloc_ctor(0, 2, 0);
} else {
 x_287 = x_273;
}
lean_ctor_set(x_287, 0, x_276);
lean_ctor_set(x_287, 1, x_278);
x_240 = x_287;
goto block_245;
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_288 = lean_box(0);
x_289 = lean_array_uset(x_62, x_75, x_288);
x_290 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_59, x_274, x_76);
x_291 = lean_array_uset(x_289, x_75, x_290);
if (lean_is_scalar(x_273)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_273;
}
lean_ctor_set(x_292, 0, x_61);
lean_ctor_set(x_292, 1, x_291);
x_240 = x_292;
goto block_245;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_76);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_293 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0;
x_294 = lean_array_push(x_293, x_52);
lean_ctor_set(x_46, 0, x_294);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_29);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_46);
lean_ctor_set(x_295, 1, x_5);
if (lean_is_scalar(x_239)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_239;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_238);
return x_296;
}
}
block_245:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_array_push(x_29, x_52);
if (lean_is_scalar(x_31)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_31;
}
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_240);
lean_inc(x_2);
if (lean_is_scalar(x_25)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_25;
}
lean_ctor_set(x_243, 0, x_2);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_16, x_243, x_7, x_8, x_9, x_10, x_238);
return x_244;
}
block_251:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_247 = lean_array_push(x_29, x_52);
if (lean_is_scalar(x_22)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_22;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_246);
lean_inc(x_2);
if (lean_is_scalar(x_19)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_19;
}
lean_ctor_set(x_249, 0, x_2);
lean_ctor_set(x_249, 1, x_248);
x_250 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_16, x_249, x_7, x_8, x_9, x_10, x_238);
return x_250;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_76);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_59);
lean_free_object(x_46);
lean_dec(x_52);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_297 = lean_ctor_get(x_236, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_236, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_299 = x_236;
} else {
 lean_dec_ref(x_236);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_76);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_46);
lean_dec(x_52);
lean_dec(x_22);
lean_dec(x_19);
lean_free_object(x_5);
if (lean_is_scalar(x_31)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_31;
}
lean_ctor_set(x_301, 0, x_29);
lean_ctor_set(x_301, 1, x_30);
lean_inc(x_2);
if (lean_is_scalar(x_25)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_25;
}
lean_ctor_set(x_302, 0, x_2);
lean_ctor_set(x_302, 1, x_301);
x_303 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_16, x_302, x_7, x_8, x_9, x_10, x_60);
return x_303;
}
}
else
{
uint8_t x_304; 
lean_dec(x_55);
lean_dec(x_54);
lean_free_object(x_46);
lean_dec(x_52);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_304 = !lean_is_exclusive(x_58);
if (x_304 == 0)
{
return x_58;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_58, 0);
x_306 = lean_ctor_get(x_58, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_58);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
return x_307;
}
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_308 = lean_ctor_get(x_46, 0);
lean_inc(x_308);
lean_dec(x_46);
x_309 = lean_ctor_get(x_45, 1);
lean_inc(x_309);
lean_dec(x_45);
x_310 = lean_ctor_get(x_308, 2);
lean_inc(x_310);
x_311 = lean_ctor_get(x_308, 3);
lean_inc(x_311);
lean_inc(x_308);
x_312 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_312, 0, x_308);
lean_inc(x_311);
x_313 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0), 8, 3);
lean_closure_set(x_313, 0, lean_box(0));
lean_closure_set(x_313, 1, x_311);
lean_closure_set(x_313, 2, x_312);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_314 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_313, x_7, x_8, x_9, x_10, x_309);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint64_t x_320; uint64_t x_321; uint64_t x_322; uint64_t x_323; uint64_t x_324; uint64_t x_325; uint64_t x_326; size_t x_327; size_t x_328; size_t x_329; size_t x_330; size_t x_331; lean_object* x_332; uint8_t x_333; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = lean_ctor_get(x_30, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_30, 1);
lean_inc(x_318);
x_319 = lean_array_get_size(x_318);
x_320 = lean_string_hash(x_315);
x_321 = 32;
x_322 = lean_uint64_shift_right(x_320, x_321);
x_323 = lean_uint64_xor(x_320, x_322);
x_324 = 16;
x_325 = lean_uint64_shift_right(x_323, x_324);
x_326 = lean_uint64_xor(x_323, x_325);
x_327 = lean_uint64_to_usize(x_326);
x_328 = lean_usize_of_nat(x_319);
lean_dec(x_319);
x_329 = 1;
x_330 = lean_usize_sub(x_328, x_329);
x_331 = lean_usize_land(x_327, x_330);
x_332 = lean_array_uget(x_318, x_331);
x_333 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__0___redArg(x_315, x_332);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_310, 0);
lean_inc(x_334);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 lean_ctor_release(x_310, 2);
 x_335 = x_310;
} else {
 lean_dec_ref(x_310);
 x_335 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_336 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_311, x_334, x_7, x_8, x_9, x_10, x_316);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_346; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_339 = x_336;
} else {
 lean_dec_ref(x_336);
 x_339 = lean_box(0);
}
if (x_32 == 0)
{
lean_object* x_352; lean_object* x_353; 
lean_dec(x_339);
lean_dec(x_337);
lean_dec(x_31);
lean_dec(x_25);
lean_free_object(x_5);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_352 = x_30;
} else {
 lean_dec_ref(x_30);
 x_352 = lean_box(0);
}
x_353 = lean_box(0);
if (x_333 == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; 
x_354 = lean_unsigned_to_nat(1u);
x_355 = lean_nat_add(x_317, x_354);
lean_dec(x_317);
if (lean_is_scalar(x_335)) {
 x_356 = lean_alloc_ctor(1, 3, 0);
} else {
 x_356 = x_335;
 lean_ctor_set_tag(x_356, 1);
}
lean_ctor_set(x_356, 0, x_315);
lean_ctor_set(x_356, 1, x_353);
lean_ctor_set(x_356, 2, x_332);
x_357 = lean_array_uset(x_318, x_331, x_356);
x_358 = lean_unsigned_to_nat(4u);
x_359 = lean_nat_mul(x_355, x_358);
x_360 = lean_unsigned_to_nat(3u);
x_361 = lean_nat_div(x_359, x_360);
lean_dec(x_359);
x_362 = lean_array_get_size(x_357);
x_363 = lean_nat_dec_le(x_361, x_362);
lean_dec(x_362);
lean_dec(x_361);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; 
x_364 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_357);
if (lean_is_scalar(x_352)) {
 x_365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_365 = x_352;
}
lean_ctor_set(x_365, 0, x_355);
lean_ctor_set(x_365, 1, x_364);
x_346 = x_365;
goto block_351;
}
else
{
lean_object* x_366; 
if (lean_is_scalar(x_352)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_352;
}
lean_ctor_set(x_366, 0, x_355);
lean_ctor_set(x_366, 1, x_357);
x_346 = x_366;
goto block_351;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_335);
x_367 = lean_box(0);
x_368 = lean_array_uset(x_318, x_331, x_367);
x_369 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_315, x_353, x_332);
x_370 = lean_array_uset(x_368, x_331, x_369);
if (lean_is_scalar(x_352)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_352;
}
lean_ctor_set(x_371, 0, x_317);
lean_ctor_set(x_371, 1, x_370);
x_346 = x_371;
goto block_351;
}
}
else
{
uint8_t x_372; 
lean_dec(x_22);
lean_dec(x_19);
x_372 = lean_unbox(x_337);
lean_dec(x_337);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; 
lean_dec(x_339);
lean_free_object(x_5);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_373 = x_30;
} else {
 lean_dec_ref(x_30);
 x_373 = lean_box(0);
}
x_374 = lean_box(0);
if (x_333 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
x_375 = lean_unsigned_to_nat(1u);
x_376 = lean_nat_add(x_317, x_375);
lean_dec(x_317);
if (lean_is_scalar(x_335)) {
 x_377 = lean_alloc_ctor(1, 3, 0);
} else {
 x_377 = x_335;
 lean_ctor_set_tag(x_377, 1);
}
lean_ctor_set(x_377, 0, x_315);
lean_ctor_set(x_377, 1, x_374);
lean_ctor_set(x_377, 2, x_332);
x_378 = lean_array_uset(x_318, x_331, x_377);
x_379 = lean_unsigned_to_nat(4u);
x_380 = lean_nat_mul(x_376, x_379);
x_381 = lean_unsigned_to_nat(3u);
x_382 = lean_nat_div(x_380, x_381);
lean_dec(x_380);
x_383 = lean_array_get_size(x_378);
x_384 = lean_nat_dec_le(x_382, x_383);
lean_dec(x_383);
lean_dec(x_382);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; 
x_385 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_378);
if (lean_is_scalar(x_373)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_373;
}
lean_ctor_set(x_386, 0, x_376);
lean_ctor_set(x_386, 1, x_385);
x_340 = x_386;
goto block_345;
}
else
{
lean_object* x_387; 
if (lean_is_scalar(x_373)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_373;
}
lean_ctor_set(x_387, 0, x_376);
lean_ctor_set(x_387, 1, x_378);
x_340 = x_387;
goto block_345;
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_335);
x_388 = lean_box(0);
x_389 = lean_array_uset(x_318, x_331, x_388);
x_390 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_315, x_374, x_332);
x_391 = lean_array_uset(x_389, x_331, x_390);
if (lean_is_scalar(x_373)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_373;
}
lean_ctor_set(x_392, 0, x_317);
lean_ctor_set(x_392, 1, x_391);
x_340 = x_392;
goto block_345;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_335);
lean_dec(x_332);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_315);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_393 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0;
x_394 = lean_array_push(x_393, x_308);
x_395 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_29);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_5);
if (lean_is_scalar(x_339)) {
 x_397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_397 = x_339;
}
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_338);
return x_397;
}
}
block_345:
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_341 = lean_array_push(x_29, x_308);
if (lean_is_scalar(x_31)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_31;
}
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_340);
lean_inc(x_2);
if (lean_is_scalar(x_25)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_25;
}
lean_ctor_set(x_343, 0, x_2);
lean_ctor_set(x_343, 1, x_342);
x_344 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_16, x_343, x_7, x_8, x_9, x_10, x_338);
return x_344;
}
block_351:
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_347 = lean_array_push(x_29, x_308);
if (lean_is_scalar(x_22)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_22;
}
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_346);
lean_inc(x_2);
if (lean_is_scalar(x_19)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_19;
}
lean_ctor_set(x_349, 0, x_2);
lean_ctor_set(x_349, 1, x_348);
x_350 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_16, x_349, x_7, x_8, x_9, x_10, x_338);
return x_350;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_335);
lean_dec(x_332);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_315);
lean_dec(x_308);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_398 = lean_ctor_get(x_336, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_336, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_400 = x_336;
} else {
 lean_dec_ref(x_336);
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
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec(x_332);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_315);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_308);
lean_dec(x_22);
lean_dec(x_19);
lean_free_object(x_5);
if (lean_is_scalar(x_31)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_31;
}
lean_ctor_set(x_402, 0, x_29);
lean_ctor_set(x_402, 1, x_30);
lean_inc(x_2);
if (lean_is_scalar(x_25)) {
 x_403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_403 = x_25;
}
lean_ctor_set(x_403, 0, x_2);
lean_ctor_set(x_403, 1, x_402);
x_404 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_16, x_403, x_7, x_8, x_9, x_10, x_316);
return x_404;
}
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_308);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_405 = lean_ctor_get(x_314, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_314, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_407 = x_314;
} else {
 lean_dec_ref(x_314);
 x_407 = lean_box(0);
}
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(1, 2, 0);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_405);
lean_ctor_set(x_408, 1, x_406);
return x_408;
}
}
}
}
else
{
uint8_t x_409; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_409 = !lean_is_exclusive(x_45);
if (x_409 == 0)
{
return x_45;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_45, 0);
x_411 = lean_ctor_get(x_45, 1);
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_45);
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
return x_412;
}
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_29);
x_413 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_413, 0, x_29);
if (lean_is_scalar(x_31)) {
 x_414 = lean_alloc_ctor(0, 2, 0);
} else {
 x_414 = x_31;
}
lean_ctor_set(x_414, 0, x_29);
lean_ctor_set(x_414, 1, x_30);
if (lean_is_scalar(x_25)) {
 x_415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_415 = x_25;
}
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
lean_ctor_set(x_23, 0, x_415);
return x_23;
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_29);
x_416 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_416, 0, x_29);
if (lean_is_scalar(x_31)) {
 x_417 = lean_alloc_ctor(0, 2, 0);
} else {
 x_417 = x_31;
}
lean_ctor_set(x_417, 0, x_29);
lean_ctor_set(x_417, 1, x_30);
if (lean_is_scalar(x_25)) {
 x_418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_418 = x_25;
}
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
lean_ctor_set(x_23, 0, x_418);
return x_23;
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; uint8_t x_431; 
x_419 = lean_ctor_get(x_23, 0);
x_420 = lean_ctor_get(x_23, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_23);
x_421 = lean_ctor_get(x_24, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_24, 1);
lean_inc(x_422);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_423 = x_24;
} else {
 lean_dec_ref(x_24);
 x_423 = lean_box(0);
}
x_424 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_425 = lean_ctor_get(x_1, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_1, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_1, 2);
lean_inc(x_427);
x_428 = lean_ctor_get(x_1, 3);
lean_inc(x_428);
x_429 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_430 = lean_ctor_get(x_1, 4);
lean_inc(x_430);
x_431 = lean_nat_dec_lt(x_419, x_426);
lean_dec(x_426);
lean_dec(x_419);
if (x_431 == 0)
{
lean_object* x_432; uint8_t x_433; 
x_432 = lean_array_get_size(x_421);
x_433 = lean_nat_dec_le(x_425, x_432);
lean_dec(x_432);
lean_dec(x_425);
if (x_433 == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_434 = lean_box(x_429);
lean_inc(x_430);
x_435 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(x_435, 0, x_430);
lean_closure_set(x_435, 1, x_427);
lean_closure_set(x_435, 2, x_428);
lean_closure_set(x_435, 3, x_434);
lean_closure_set(x_435, 4, x_18);
lean_closure_set(x_435, 5, x_20);
lean_closure_set(x_435, 6, x_21);
x_436 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0), 8, 3);
lean_closure_set(x_436, 0, lean_box(0));
lean_closure_set(x_436, 1, x_430);
lean_closure_set(x_436, 2, x_435);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_437 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_436, x_7, x_8, x_9, x_10, x_420);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; 
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_22);
lean_dec(x_19);
lean_free_object(x_5);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
lean_dec(x_437);
if (lean_is_scalar(x_423)) {
 x_440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_440 = x_423;
}
lean_ctor_set(x_440, 0, x_421);
lean_ctor_set(x_440, 1, x_422);
lean_inc(x_2);
if (lean_is_scalar(x_25)) {
 x_441 = lean_alloc_ctor(0, 2, 0);
} else {
 x_441 = x_25;
}
lean_ctor_set(x_441, 0, x_2);
lean_ctor_set(x_441, 1, x_440);
x_442 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_16, x_441, x_7, x_8, x_9, x_10, x_439);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_443 = lean_ctor_get(x_438, 0);
lean_inc(x_443);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 x_444 = x_438;
} else {
 lean_dec_ref(x_438);
 x_444 = lean_box(0);
}
x_445 = lean_ctor_get(x_437, 1);
lean_inc(x_445);
lean_dec(x_437);
x_446 = lean_ctor_get(x_443, 2);
lean_inc(x_446);
x_447 = lean_ctor_get(x_443, 3);
lean_inc(x_447);
lean_inc(x_443);
x_448 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_448, 0, x_443);
lean_inc(x_447);
x_449 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0), 8, 3);
lean_closure_set(x_449, 0, lean_box(0));
lean_closure_set(x_449, 1, x_447);
lean_closure_set(x_449, 2, x_448);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_450 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_449, x_7, x_8, x_9, x_10, x_445);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; uint64_t x_456; uint64_t x_457; uint64_t x_458; uint64_t x_459; uint64_t x_460; uint64_t x_461; uint64_t x_462; size_t x_463; size_t x_464; size_t x_465; size_t x_466; size_t x_467; lean_object* x_468; uint8_t x_469; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
x_453 = lean_ctor_get(x_422, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_422, 1);
lean_inc(x_454);
x_455 = lean_array_get_size(x_454);
x_456 = lean_string_hash(x_451);
x_457 = 32;
x_458 = lean_uint64_shift_right(x_456, x_457);
x_459 = lean_uint64_xor(x_456, x_458);
x_460 = 16;
x_461 = lean_uint64_shift_right(x_459, x_460);
x_462 = lean_uint64_xor(x_459, x_461);
x_463 = lean_uint64_to_usize(x_462);
x_464 = lean_usize_of_nat(x_455);
lean_dec(x_455);
x_465 = 1;
x_466 = lean_usize_sub(x_464, x_465);
x_467 = lean_usize_land(x_463, x_466);
x_468 = lean_array_uget(x_454, x_467);
x_469 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__0___redArg(x_451, x_468);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_ctor_get(x_446, 0);
lean_inc(x_470);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 lean_ctor_release(x_446, 2);
 x_471 = x_446;
} else {
 lean_dec_ref(x_446);
 x_471 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_472 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_447, x_470, x_7, x_8, x_9, x_10, x_452);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_482; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_475 = x_472;
} else {
 lean_dec_ref(x_472);
 x_475 = lean_box(0);
}
if (x_424 == 0)
{
lean_object* x_488; lean_object* x_489; 
lean_dec(x_475);
lean_dec(x_473);
lean_dec(x_444);
lean_dec(x_423);
lean_dec(x_25);
lean_free_object(x_5);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_488 = x_422;
} else {
 lean_dec_ref(x_422);
 x_488 = lean_box(0);
}
x_489 = lean_box(0);
if (x_469 == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; 
x_490 = lean_unsigned_to_nat(1u);
x_491 = lean_nat_add(x_453, x_490);
lean_dec(x_453);
if (lean_is_scalar(x_471)) {
 x_492 = lean_alloc_ctor(1, 3, 0);
} else {
 x_492 = x_471;
 lean_ctor_set_tag(x_492, 1);
}
lean_ctor_set(x_492, 0, x_451);
lean_ctor_set(x_492, 1, x_489);
lean_ctor_set(x_492, 2, x_468);
x_493 = lean_array_uset(x_454, x_467, x_492);
x_494 = lean_unsigned_to_nat(4u);
x_495 = lean_nat_mul(x_491, x_494);
x_496 = lean_unsigned_to_nat(3u);
x_497 = lean_nat_div(x_495, x_496);
lean_dec(x_495);
x_498 = lean_array_get_size(x_493);
x_499 = lean_nat_dec_le(x_497, x_498);
lean_dec(x_498);
lean_dec(x_497);
if (x_499 == 0)
{
lean_object* x_500; lean_object* x_501; 
x_500 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_493);
if (lean_is_scalar(x_488)) {
 x_501 = lean_alloc_ctor(0, 2, 0);
} else {
 x_501 = x_488;
}
lean_ctor_set(x_501, 0, x_491);
lean_ctor_set(x_501, 1, x_500);
x_482 = x_501;
goto block_487;
}
else
{
lean_object* x_502; 
if (lean_is_scalar(x_488)) {
 x_502 = lean_alloc_ctor(0, 2, 0);
} else {
 x_502 = x_488;
}
lean_ctor_set(x_502, 0, x_491);
lean_ctor_set(x_502, 1, x_493);
x_482 = x_502;
goto block_487;
}
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_471);
x_503 = lean_box(0);
x_504 = lean_array_uset(x_454, x_467, x_503);
x_505 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_451, x_489, x_468);
x_506 = lean_array_uset(x_504, x_467, x_505);
if (lean_is_scalar(x_488)) {
 x_507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_507 = x_488;
}
lean_ctor_set(x_507, 0, x_453);
lean_ctor_set(x_507, 1, x_506);
x_482 = x_507;
goto block_487;
}
}
else
{
uint8_t x_508; 
lean_dec(x_22);
lean_dec(x_19);
x_508 = lean_unbox(x_473);
lean_dec(x_473);
if (x_508 == 0)
{
lean_object* x_509; lean_object* x_510; 
lean_dec(x_475);
lean_dec(x_444);
lean_free_object(x_5);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_509 = x_422;
} else {
 lean_dec_ref(x_422);
 x_509 = lean_box(0);
}
x_510 = lean_box(0);
if (x_469 == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; 
x_511 = lean_unsigned_to_nat(1u);
x_512 = lean_nat_add(x_453, x_511);
lean_dec(x_453);
if (lean_is_scalar(x_471)) {
 x_513 = lean_alloc_ctor(1, 3, 0);
} else {
 x_513 = x_471;
 lean_ctor_set_tag(x_513, 1);
}
lean_ctor_set(x_513, 0, x_451);
lean_ctor_set(x_513, 1, x_510);
lean_ctor_set(x_513, 2, x_468);
x_514 = lean_array_uset(x_454, x_467, x_513);
x_515 = lean_unsigned_to_nat(4u);
x_516 = lean_nat_mul(x_512, x_515);
x_517 = lean_unsigned_to_nat(3u);
x_518 = lean_nat_div(x_516, x_517);
lean_dec(x_516);
x_519 = lean_array_get_size(x_514);
x_520 = lean_nat_dec_le(x_518, x_519);
lean_dec(x_519);
lean_dec(x_518);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; 
x_521 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_514);
if (lean_is_scalar(x_509)) {
 x_522 = lean_alloc_ctor(0, 2, 0);
} else {
 x_522 = x_509;
}
lean_ctor_set(x_522, 0, x_512);
lean_ctor_set(x_522, 1, x_521);
x_476 = x_522;
goto block_481;
}
else
{
lean_object* x_523; 
if (lean_is_scalar(x_509)) {
 x_523 = lean_alloc_ctor(0, 2, 0);
} else {
 x_523 = x_509;
}
lean_ctor_set(x_523, 0, x_512);
lean_ctor_set(x_523, 1, x_514);
x_476 = x_523;
goto block_481;
}
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_471);
x_524 = lean_box(0);
x_525 = lean_array_uset(x_454, x_467, x_524);
x_526 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_451, x_510, x_468);
x_527 = lean_array_uset(x_525, x_467, x_526);
if (lean_is_scalar(x_509)) {
 x_528 = lean_alloc_ctor(0, 2, 0);
} else {
 x_528 = x_509;
}
lean_ctor_set(x_528, 0, x_453);
lean_ctor_set(x_528, 1, x_527);
x_476 = x_528;
goto block_481;
}
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_471);
lean_dec(x_468);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_451);
lean_dec(x_423);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_529 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0;
x_530 = lean_array_push(x_529, x_443);
if (lean_is_scalar(x_444)) {
 x_531 = lean_alloc_ctor(1, 1, 0);
} else {
 x_531 = x_444;
}
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 1, x_422);
lean_ctor_set(x_5, 0, x_421);
x_532 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_5);
if (lean_is_scalar(x_475)) {
 x_533 = lean_alloc_ctor(0, 2, 0);
} else {
 x_533 = x_475;
}
lean_ctor_set(x_533, 0, x_532);
lean_ctor_set(x_533, 1, x_474);
return x_533;
}
}
block_481:
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_477 = lean_array_push(x_421, x_443);
if (lean_is_scalar(x_423)) {
 x_478 = lean_alloc_ctor(0, 2, 0);
} else {
 x_478 = x_423;
}
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_476);
lean_inc(x_2);
if (lean_is_scalar(x_25)) {
 x_479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_479 = x_25;
}
lean_ctor_set(x_479, 0, x_2);
lean_ctor_set(x_479, 1, x_478);
x_480 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_16, x_479, x_7, x_8, x_9, x_10, x_474);
return x_480;
}
block_487:
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_483 = lean_array_push(x_421, x_443);
if (lean_is_scalar(x_22)) {
 x_484 = lean_alloc_ctor(0, 2, 0);
} else {
 x_484 = x_22;
}
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_482);
lean_inc(x_2);
if (lean_is_scalar(x_19)) {
 x_485 = lean_alloc_ctor(0, 2, 0);
} else {
 x_485 = x_19;
}
lean_ctor_set(x_485, 0, x_2);
lean_ctor_set(x_485, 1, x_484);
x_486 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_16, x_485, x_7, x_8, x_9, x_10, x_474);
return x_486;
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_471);
lean_dec(x_468);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_451);
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_534 = lean_ctor_get(x_472, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_472, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_536 = x_472;
} else {
 lean_dec_ref(x_472);
 x_536 = lean_box(0);
}
if (lean_is_scalar(x_536)) {
 x_537 = lean_alloc_ctor(1, 2, 0);
} else {
 x_537 = x_536;
}
lean_ctor_set(x_537, 0, x_534);
lean_ctor_set(x_537, 1, x_535);
return x_537;
}
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_468);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_451);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_22);
lean_dec(x_19);
lean_free_object(x_5);
if (lean_is_scalar(x_423)) {
 x_538 = lean_alloc_ctor(0, 2, 0);
} else {
 x_538 = x_423;
}
lean_ctor_set(x_538, 0, x_421);
lean_ctor_set(x_538, 1, x_422);
lean_inc(x_2);
if (lean_is_scalar(x_25)) {
 x_539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_539 = x_25;
}
lean_ctor_set(x_539, 0, x_2);
lean_ctor_set(x_539, 1, x_538);
x_540 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_16, x_539, x_7, x_8, x_9, x_10, x_452);
return x_540;
}
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_541 = lean_ctor_get(x_450, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_450, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_543 = x_450;
} else {
 lean_dec_ref(x_450);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(1, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_541);
lean_ctor_set(x_544, 1, x_542);
return x_544;
}
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_545 = lean_ctor_get(x_437, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_437, 1);
lean_inc(x_546);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_547 = x_437;
} else {
 lean_dec_ref(x_437);
 x_547 = lean_box(0);
}
if (lean_is_scalar(x_547)) {
 x_548 = lean_alloc_ctor(1, 2, 0);
} else {
 x_548 = x_547;
}
lean_ctor_set(x_548, 0, x_545);
lean_ctor_set(x_548, 1, x_546);
return x_548;
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_430);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_421);
x_549 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_549, 0, x_421);
if (lean_is_scalar(x_423)) {
 x_550 = lean_alloc_ctor(0, 2, 0);
} else {
 x_550 = x_423;
}
lean_ctor_set(x_550, 0, x_421);
lean_ctor_set(x_550, 1, x_422);
if (lean_is_scalar(x_25)) {
 x_551 = lean_alloc_ctor(0, 2, 0);
} else {
 x_551 = x_25;
}
lean_ctor_set(x_551, 0, x_549);
lean_ctor_set(x_551, 1, x_550);
x_552 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_552, 0, x_551);
lean_ctor_set(x_552, 1, x_420);
return x_552;
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
lean_dec(x_430);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_425);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_421);
x_553 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_553, 0, x_421);
if (lean_is_scalar(x_423)) {
 x_554 = lean_alloc_ctor(0, 2, 0);
} else {
 x_554 = x_423;
}
lean_ctor_set(x_554, 0, x_421);
lean_ctor_set(x_554, 1, x_422);
if (lean_is_scalar(x_25)) {
 x_555 = lean_alloc_ctor(0, 2, 0);
} else {
 x_555 = x_25;
}
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_554);
x_556 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_556, 0, x_555);
lean_ctor_set(x_556, 1, x_420);
return x_556;
}
}
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; uint8_t x_577; lean_object* x_578; uint8_t x_579; 
x_557 = lean_ctor_get(x_5, 1);
lean_inc(x_557);
lean_dec(x_5);
x_558 = lean_ctor_get(x_13, 0);
lean_inc(x_558);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_559 = x_13;
} else {
 lean_dec_ref(x_13);
 x_559 = lean_box(0);
}
x_560 = lean_ctor_get(x_14, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_14, 1);
lean_inc(x_561);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_562 = x_14;
} else {
 lean_dec_ref(x_14);
 x_562 = lean_box(0);
}
x_563 = l_Lean_getRemainingHeartbeats___redArg(x_9, x_11);
x_564 = lean_ctor_get(x_6, 1);
lean_inc(x_564);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_565 = x_6;
} else {
 lean_dec_ref(x_6);
 x_565 = lean_box(0);
}
x_566 = lean_ctor_get(x_563, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_563, 1);
lean_inc(x_567);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 lean_ctor_release(x_563, 1);
 x_568 = x_563;
} else {
 lean_dec_ref(x_563);
 x_568 = lean_box(0);
}
x_569 = lean_ctor_get(x_564, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_564, 1);
lean_inc(x_570);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 lean_ctor_release(x_564, 1);
 x_571 = x_564;
} else {
 lean_dec_ref(x_564);
 x_571 = lean_box(0);
}
x_572 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_573 = lean_ctor_get(x_1, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_1, 1);
lean_inc(x_574);
x_575 = lean_ctor_get(x_1, 2);
lean_inc(x_575);
x_576 = lean_ctor_get(x_1, 3);
lean_inc(x_576);
x_577 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_578 = lean_ctor_get(x_1, 4);
lean_inc(x_578);
x_579 = lean_nat_dec_lt(x_566, x_574);
lean_dec(x_574);
lean_dec(x_566);
if (x_579 == 0)
{
lean_object* x_580; uint8_t x_581; 
x_580 = lean_array_get_size(x_569);
x_581 = lean_nat_dec_le(x_573, x_580);
lean_dec(x_580);
lean_dec(x_573);
if (x_581 == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
lean_dec(x_568);
x_582 = lean_box(x_577);
lean_inc(x_578);
x_583 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(x_583, 0, x_578);
lean_closure_set(x_583, 1, x_575);
lean_closure_set(x_583, 2, x_576);
lean_closure_set(x_583, 3, x_582);
lean_closure_set(x_583, 4, x_558);
lean_closure_set(x_583, 5, x_560);
lean_closure_set(x_583, 6, x_561);
x_584 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0), 8, 3);
lean_closure_set(x_584, 0, lean_box(0));
lean_closure_set(x_584, 1, x_578);
lean_closure_set(x_584, 2, x_583);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_585 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_584, x_7, x_8, x_9, x_10, x_567);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; 
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_dec(x_562);
lean_dec(x_559);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
lean_dec(x_585);
if (lean_is_scalar(x_571)) {
 x_588 = lean_alloc_ctor(0, 2, 0);
} else {
 x_588 = x_571;
}
lean_ctor_set(x_588, 0, x_569);
lean_ctor_set(x_588, 1, x_570);
lean_inc(x_2);
if (lean_is_scalar(x_565)) {
 x_589 = lean_alloc_ctor(0, 2, 0);
} else {
 x_589 = x_565;
}
lean_ctor_set(x_589, 0, x_2);
lean_ctor_set(x_589, 1, x_588);
x_590 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_557, x_589, x_7, x_8, x_9, x_10, x_587);
return x_590;
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_591 = lean_ctor_get(x_586, 0);
lean_inc(x_591);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 x_592 = x_586;
} else {
 lean_dec_ref(x_586);
 x_592 = lean_box(0);
}
x_593 = lean_ctor_get(x_585, 1);
lean_inc(x_593);
lean_dec(x_585);
x_594 = lean_ctor_get(x_591, 2);
lean_inc(x_594);
x_595 = lean_ctor_get(x_591, 3);
lean_inc(x_595);
lean_inc(x_591);
x_596 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_596, 0, x_591);
lean_inc(x_595);
x_597 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_SynthInstance_tryResolve_spec__0), 8, 3);
lean_closure_set(x_597, 0, lean_box(0));
lean_closure_set(x_597, 1, x_595);
lean_closure_set(x_597, 2, x_596);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_598 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_597, x_7, x_8, x_9, x_10, x_593);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint64_t x_604; uint64_t x_605; uint64_t x_606; uint64_t x_607; uint64_t x_608; uint64_t x_609; uint64_t x_610; size_t x_611; size_t x_612; size_t x_613; size_t x_614; size_t x_615; lean_object* x_616; uint8_t x_617; 
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
lean_dec(x_598);
x_601 = lean_ctor_get(x_570, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_570, 1);
lean_inc(x_602);
x_603 = lean_array_get_size(x_602);
x_604 = lean_string_hash(x_599);
x_605 = 32;
x_606 = lean_uint64_shift_right(x_604, x_605);
x_607 = lean_uint64_xor(x_604, x_606);
x_608 = 16;
x_609 = lean_uint64_shift_right(x_607, x_608);
x_610 = lean_uint64_xor(x_607, x_609);
x_611 = lean_uint64_to_usize(x_610);
x_612 = lean_usize_of_nat(x_603);
lean_dec(x_603);
x_613 = 1;
x_614 = lean_usize_sub(x_612, x_613);
x_615 = lean_usize_land(x_611, x_614);
x_616 = lean_array_uget(x_602, x_615);
x_617 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__0___redArg(x_599, x_616);
if (x_617 == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_594, 0);
lean_inc(x_618);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 lean_ctor_release(x_594, 2);
 x_619 = x_594;
} else {
 lean_dec_ref(x_594);
 x_619 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_620 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_595, x_618, x_7, x_8, x_9, x_10, x_600);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_630; 
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_623 = x_620;
} else {
 lean_dec_ref(x_620);
 x_623 = lean_box(0);
}
if (x_572 == 0)
{
lean_object* x_636; lean_object* x_637; 
lean_dec(x_623);
lean_dec(x_621);
lean_dec(x_592);
lean_dec(x_571);
lean_dec(x_565);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_636 = x_570;
} else {
 lean_dec_ref(x_570);
 x_636 = lean_box(0);
}
x_637 = lean_box(0);
if (x_617 == 0)
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; uint8_t x_647; 
x_638 = lean_unsigned_to_nat(1u);
x_639 = lean_nat_add(x_601, x_638);
lean_dec(x_601);
if (lean_is_scalar(x_619)) {
 x_640 = lean_alloc_ctor(1, 3, 0);
} else {
 x_640 = x_619;
 lean_ctor_set_tag(x_640, 1);
}
lean_ctor_set(x_640, 0, x_599);
lean_ctor_set(x_640, 1, x_637);
lean_ctor_set(x_640, 2, x_616);
x_641 = lean_array_uset(x_602, x_615, x_640);
x_642 = lean_unsigned_to_nat(4u);
x_643 = lean_nat_mul(x_639, x_642);
x_644 = lean_unsigned_to_nat(3u);
x_645 = lean_nat_div(x_643, x_644);
lean_dec(x_643);
x_646 = lean_array_get_size(x_641);
x_647 = lean_nat_dec_le(x_645, x_646);
lean_dec(x_646);
lean_dec(x_645);
if (x_647 == 0)
{
lean_object* x_648; lean_object* x_649; 
x_648 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_641);
if (lean_is_scalar(x_636)) {
 x_649 = lean_alloc_ctor(0, 2, 0);
} else {
 x_649 = x_636;
}
lean_ctor_set(x_649, 0, x_639);
lean_ctor_set(x_649, 1, x_648);
x_630 = x_649;
goto block_635;
}
else
{
lean_object* x_650; 
if (lean_is_scalar(x_636)) {
 x_650 = lean_alloc_ctor(0, 2, 0);
} else {
 x_650 = x_636;
}
lean_ctor_set(x_650, 0, x_639);
lean_ctor_set(x_650, 1, x_641);
x_630 = x_650;
goto block_635;
}
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_619);
x_651 = lean_box(0);
x_652 = lean_array_uset(x_602, x_615, x_651);
x_653 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_599, x_637, x_616);
x_654 = lean_array_uset(x_652, x_615, x_653);
if (lean_is_scalar(x_636)) {
 x_655 = lean_alloc_ctor(0, 2, 0);
} else {
 x_655 = x_636;
}
lean_ctor_set(x_655, 0, x_601);
lean_ctor_set(x_655, 1, x_654);
x_630 = x_655;
goto block_635;
}
}
else
{
uint8_t x_656; 
lean_dec(x_562);
lean_dec(x_559);
x_656 = lean_unbox(x_621);
lean_dec(x_621);
if (x_656 == 0)
{
lean_object* x_657; lean_object* x_658; 
lean_dec(x_623);
lean_dec(x_592);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_657 = x_570;
} else {
 lean_dec_ref(x_570);
 x_657 = lean_box(0);
}
x_658 = lean_box(0);
if (x_617 == 0)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; uint8_t x_668; 
x_659 = lean_unsigned_to_nat(1u);
x_660 = lean_nat_add(x_601, x_659);
lean_dec(x_601);
if (lean_is_scalar(x_619)) {
 x_661 = lean_alloc_ctor(1, 3, 0);
} else {
 x_661 = x_619;
 lean_ctor_set_tag(x_661, 1);
}
lean_ctor_set(x_661, 0, x_599);
lean_ctor_set(x_661, 1, x_658);
lean_ctor_set(x_661, 2, x_616);
x_662 = lean_array_uset(x_602, x_615, x_661);
x_663 = lean_unsigned_to_nat(4u);
x_664 = lean_nat_mul(x_660, x_663);
x_665 = lean_unsigned_to_nat(3u);
x_666 = lean_nat_div(x_664, x_665);
lean_dec(x_664);
x_667 = lean_array_get_size(x_662);
x_668 = lean_nat_dec_le(x_666, x_667);
lean_dec(x_667);
lean_dec(x_666);
if (x_668 == 0)
{
lean_object* x_669; lean_object* x_670; 
x_669 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__1___redArg(x_662);
if (lean_is_scalar(x_657)) {
 x_670 = lean_alloc_ctor(0, 2, 0);
} else {
 x_670 = x_657;
}
lean_ctor_set(x_670, 0, x_660);
lean_ctor_set(x_670, 1, x_669);
x_624 = x_670;
goto block_629;
}
else
{
lean_object* x_671; 
if (lean_is_scalar(x_657)) {
 x_671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_671 = x_657;
}
lean_ctor_set(x_671, 0, x_660);
lean_ctor_set(x_671, 1, x_662);
x_624 = x_671;
goto block_629;
}
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_619);
x_672 = lean_box(0);
x_673 = lean_array_uset(x_602, x_615, x_672);
x_674 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_DocString_Links_0__Lean_domainMap_spec__4___redArg(x_599, x_658, x_616);
x_675 = lean_array_uset(x_673, x_615, x_674);
if (lean_is_scalar(x_657)) {
 x_676 = lean_alloc_ctor(0, 2, 0);
} else {
 x_676 = x_657;
}
lean_ctor_set(x_676, 0, x_601);
lean_ctor_set(x_676, 1, x_675);
x_624 = x_676;
goto block_629;
}
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
lean_dec(x_619);
lean_dec(x_616);
lean_dec(x_602);
lean_dec(x_601);
lean_dec(x_599);
lean_dec(x_571);
lean_dec(x_565);
lean_dec(x_557);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_677 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0;
x_678 = lean_array_push(x_677, x_591);
if (lean_is_scalar(x_592)) {
 x_679 = lean_alloc_ctor(1, 1, 0);
} else {
 x_679 = x_592;
}
lean_ctor_set(x_679, 0, x_678);
x_680 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_680, 0, x_569);
lean_ctor_set(x_680, 1, x_570);
x_681 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_681, 0, x_679);
lean_ctor_set(x_681, 1, x_680);
if (lean_is_scalar(x_623)) {
 x_682 = lean_alloc_ctor(0, 2, 0);
} else {
 x_682 = x_623;
}
lean_ctor_set(x_682, 0, x_681);
lean_ctor_set(x_682, 1, x_622);
return x_682;
}
}
block_629:
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_625 = lean_array_push(x_569, x_591);
if (lean_is_scalar(x_571)) {
 x_626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_626 = x_571;
}
lean_ctor_set(x_626, 0, x_625);
lean_ctor_set(x_626, 1, x_624);
lean_inc(x_2);
if (lean_is_scalar(x_565)) {
 x_627 = lean_alloc_ctor(0, 2, 0);
} else {
 x_627 = x_565;
}
lean_ctor_set(x_627, 0, x_2);
lean_ctor_set(x_627, 1, x_626);
x_628 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_557, x_627, x_7, x_8, x_9, x_10, x_622);
return x_628;
}
block_635:
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_631 = lean_array_push(x_569, x_591);
if (lean_is_scalar(x_562)) {
 x_632 = lean_alloc_ctor(0, 2, 0);
} else {
 x_632 = x_562;
}
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_630);
lean_inc(x_2);
if (lean_is_scalar(x_559)) {
 x_633 = lean_alloc_ctor(0, 2, 0);
} else {
 x_633 = x_559;
}
lean_ctor_set(x_633, 0, x_2);
lean_ctor_set(x_633, 1, x_632);
x_634 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_557, x_633, x_7, x_8, x_9, x_10, x_622);
return x_634;
}
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
lean_dec(x_619);
lean_dec(x_616);
lean_dec(x_602);
lean_dec(x_601);
lean_dec(x_599);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_565);
lean_dec(x_562);
lean_dec(x_559);
lean_dec(x_557);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_683 = lean_ctor_get(x_620, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_620, 1);
lean_inc(x_684);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_685 = x_620;
} else {
 lean_dec_ref(x_620);
 x_685 = lean_box(0);
}
if (lean_is_scalar(x_685)) {
 x_686 = lean_alloc_ctor(1, 2, 0);
} else {
 x_686 = x_685;
}
lean_ctor_set(x_686, 0, x_683);
lean_ctor_set(x_686, 1, x_684);
return x_686;
}
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_616);
lean_dec(x_602);
lean_dec(x_601);
lean_dec(x_599);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_562);
lean_dec(x_559);
if (lean_is_scalar(x_571)) {
 x_687 = lean_alloc_ctor(0, 2, 0);
} else {
 x_687 = x_571;
}
lean_ctor_set(x_687, 0, x_569);
lean_ctor_set(x_687, 1, x_570);
lean_inc(x_2);
if (lean_is_scalar(x_565)) {
 x_688 = lean_alloc_ctor(0, 2, 0);
} else {
 x_688 = x_565;
}
lean_ctor_set(x_688, 0, x_2);
lean_ctor_set(x_688, 1, x_687);
x_689 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2, x_557, x_688, x_7, x_8, x_9, x_10, x_600);
return x_689;
}
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_565);
lean_dec(x_562);
lean_dec(x_559);
lean_dec(x_557);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_690 = lean_ctor_get(x_598, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_598, 1);
lean_inc(x_691);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 lean_ctor_release(x_598, 1);
 x_692 = x_598;
} else {
 lean_dec_ref(x_598);
 x_692 = lean_box(0);
}
if (lean_is_scalar(x_692)) {
 x_693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_693 = x_692;
}
lean_ctor_set(x_693, 0, x_690);
lean_ctor_set(x_693, 1, x_691);
return x_693;
}
}
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_565);
lean_dec(x_562);
lean_dec(x_559);
lean_dec(x_557);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_694 = lean_ctor_get(x_585, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_585, 1);
lean_inc(x_695);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 lean_ctor_release(x_585, 1);
 x_696 = x_585;
} else {
 lean_dec_ref(x_585);
 x_696 = lean_box(0);
}
if (lean_is_scalar(x_696)) {
 x_697 = lean_alloc_ctor(1, 2, 0);
} else {
 x_697 = x_696;
}
lean_ctor_set(x_697, 0, x_694);
lean_ctor_set(x_697, 1, x_695);
return x_697;
}
}
else
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
lean_dec(x_578);
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_562);
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_569);
x_698 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_698, 0, x_569);
if (lean_is_scalar(x_571)) {
 x_699 = lean_alloc_ctor(0, 2, 0);
} else {
 x_699 = x_571;
}
lean_ctor_set(x_699, 0, x_569);
lean_ctor_set(x_699, 1, x_570);
if (lean_is_scalar(x_565)) {
 x_700 = lean_alloc_ctor(0, 2, 0);
} else {
 x_700 = x_565;
}
lean_ctor_set(x_700, 0, x_698);
lean_ctor_set(x_700, 1, x_699);
if (lean_is_scalar(x_568)) {
 x_701 = lean_alloc_ctor(0, 2, 0);
} else {
 x_701 = x_568;
}
lean_ctor_set(x_701, 0, x_700);
lean_ctor_set(x_701, 1, x_567);
return x_701;
}
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
lean_dec(x_578);
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_573);
lean_dec(x_562);
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_569);
x_702 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_702, 0, x_569);
if (lean_is_scalar(x_571)) {
 x_703 = lean_alloc_ctor(0, 2, 0);
} else {
 x_703 = x_571;
}
lean_ctor_set(x_703, 0, x_569);
lean_ctor_set(x_703, 1, x_570);
if (lean_is_scalar(x_565)) {
 x_704 = lean_alloc_ctor(0, 2, 0);
} else {
 x_704 = x_565;
}
lean_ctor_set(x_704, 0, x_702);
lean_ctor_set(x_704, 1, x_703);
if (lean_is_scalar(x_568)) {
 x_705 = lean_alloc_ctor(0, 2, 0);
} else {
 x_705 = x_568;
}
lean_ctor_set(x_705, 0, x_704);
lean_ctor_set(x_705, 1, x_567);
return x_705;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_takeListAux___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_String_hash___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_Meta_Rewrites_takeListAux___closed__0;
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_inc(x_4);
x_14 = l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(x_1, x_11, x_10, x_4, x_4, x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_16);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_14, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_26);
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
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
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_Rewrites_findRewrites___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Rewrites_findRewrites___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Rewrites_findRewrites___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_findRewrites___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_st_ref_get(x_11, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
x_18 = l_Lean_Meta_Rewrites_rewriteCandidates(x_1, x_2, x_4, x_5, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_48; uint8_t x_49; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_getMaxHeartbeats___redArg(x_12, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_eq(x_22, x_48);
lean_dec(x_22);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = l_Lean_getRemainingHeartbeats___redArg(x_12, x_23);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_nat_mul(x_9, x_51);
lean_dec(x_51);
x_54 = lean_unsigned_to_nat(100u);
x_55 = lean_nat_div(x_53, x_54);
lean_dec(x_53);
x_25 = x_55;
x_26 = x_10;
x_27 = x_11;
x_28 = x_12;
x_29 = x_13;
x_30 = x_52;
goto block_47;
}
else
{
x_25 = x_48;
x_26 = x_10;
x_27 = x_11;
x_28 = x_12;
x_29 = x_13;
x_30 = x_23;
goto block_47;
}
block_47:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_8);
x_31 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_3);
lean_ctor_set(x_31, 3, x_4);
lean_ctor_set(x_31, 4, x_24);
lean_ctor_set_uint8(x_31, sizeof(void*)*5, x_7);
lean_ctor_set_uint8(x_31, sizeof(void*)*5 + 1, x_6);
x_32 = l_Lean_Meta_Rewrites_findRewrites___closed__4;
x_33 = lean_mk_empty_array_with_capacity(x_8);
lean_dec(x_8);
x_34 = lean_array_to_list(x_19);
x_35 = l_Lean_Meta_Rewrites_takeListAux(x_31, x_32, x_33, x_34, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_array_to_list(x_37);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_array_to_list(x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
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
}
else
{
uint8_t x_56; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_18);
if (x_56 == 0)
{
return x_18;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_18, 0);
x_58 = lean_ctor_get(x_18, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_18);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = l_Lean_Meta_Rewrites_findRewrites(x_1, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_5);
return x_17;
}
}
lean_object* initialize_Lean_Meta_LazyDiscrTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Heartbeats(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Rewrites(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_LazyDiscrTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rewrite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_SolveByElim(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Heartbeats(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__6____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__6____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__6____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__7____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__7____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__7____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__8____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__8____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__8____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__9____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__9____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__9____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__10____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__10____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__10____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__11____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__11____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__11____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__12____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__12____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__12____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__13____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__13____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__13____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__14____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__14____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__14____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__15____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__15____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__15____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__16____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__16____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__16____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__17____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__17____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__17____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__18____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__18____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__18____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
l_Lean_Meta_Rewrites_initFn___closed__19____x40_Lean_Meta_Tactic_Rewrites___hyg_5_ = _init_l_Lean_Meta_Rewrites_initFn___closed__19____x40_Lean_Meta_Tactic_Rewrites___hyg_5_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__19____x40_Lean_Meta_Tactic_Rewrites___hyg_5_);
if (builtin) {res = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites___hyg_46_ = _init_l_Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites___hyg_46_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites___hyg_46_);
l_Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites___hyg_46_ = _init_l_Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites___hyg_46_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites___hyg_46_);
l_Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites___hyg_46_ = _init_l_Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites___hyg_46_();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites___hyg_46_);
if (builtin) {res = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Rewrites_rewriteResultLemma___closed__0 = _init_l_Lean_Meta_Rewrites_rewriteResultLemma___closed__0();
lean_mark_persistent(l_Lean_Meta_Rewrites_rewriteResultLemma___closed__0);
l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1 = _init_l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1);
l_Lean_Meta_Rewrites_forwardWeight = _init_l_Lean_Meta_Rewrites_forwardWeight();
lean_mark_persistent(l_Lean_Meta_Rewrites_forwardWeight);
l_Lean_Meta_Rewrites_backwardWeight = _init_l_Lean_Meta_Rewrites_backwardWeight();
lean_mark_persistent(l_Lean_Meta_Rewrites_backwardWeight);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__6 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__6);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__7 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__7);
l_Lean_Meta_Rewrites_localHypotheses___closed__0 = _init_l_Lean_Meta_Rewrites_localHypotheses___closed__0();
lean_mark_persistent(l_Lean_Meta_Rewrites_localHypotheses___closed__0);
l_Lean_Meta_Rewrites_droppedKeys___closed__0 = _init_l_Lean_Meta_Rewrites_droppedKeys___closed__0();
lean_mark_persistent(l_Lean_Meta_Rewrites_droppedKeys___closed__0);
l_Lean_Meta_Rewrites_droppedKeys___closed__1 = _init_l_Lean_Meta_Rewrites_droppedKeys___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_droppedKeys___closed__1);
l_Lean_Meta_Rewrites_droppedKeys___closed__2 = _init_l_Lean_Meta_Rewrites_droppedKeys___closed__2();
lean_mark_persistent(l_Lean_Meta_Rewrites_droppedKeys___closed__2);
l_Lean_Meta_Rewrites_droppedKeys___closed__3 = _init_l_Lean_Meta_Rewrites_droppedKeys___closed__3();
lean_mark_persistent(l_Lean_Meta_Rewrites_droppedKeys___closed__3);
l_Lean_Meta_Rewrites_droppedKeys___closed__4 = _init_l_Lean_Meta_Rewrites_droppedKeys___closed__4();
lean_mark_persistent(l_Lean_Meta_Rewrites_droppedKeys___closed__4);
l_Lean_Meta_Rewrites_droppedKeys___closed__5 = _init_l_Lean_Meta_Rewrites_droppedKeys___closed__5();
lean_mark_persistent(l_Lean_Meta_Rewrites_droppedKeys___closed__5);
l_Lean_Meta_Rewrites_droppedKeys___closed__6 = _init_l_Lean_Meta_Rewrites_droppedKeys___closed__6();
lean_mark_persistent(l_Lean_Meta_Rewrites_droppedKeys___closed__6);
l_Lean_Meta_Rewrites_droppedKeys___closed__7 = _init_l_Lean_Meta_Rewrites_droppedKeys___closed__7();
lean_mark_persistent(l_Lean_Meta_Rewrites_droppedKeys___closed__7);
l_Lean_Meta_Rewrites_droppedKeys = _init_l_Lean_Meta_Rewrites_droppedKeys();
lean_mark_persistent(l_Lean_Meta_Rewrites_droppedKeys);
l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0 = _init_l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0();
lean_mark_persistent(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0);
if (builtin) {res = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_1190_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default);
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__0 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__0);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState);
if (builtin) {res = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_1250_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext);
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask);
l_Lean_Meta_Rewrites_rwFindDecls___closed__0 = _init_l_Lean_Meta_Rewrites_rwFindDecls___closed__0();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwFindDecls___closed__0);
l_Lean_Meta_Rewrites_rwFindDecls___closed__1 = _init_l_Lean_Meta_Rewrites_rwFindDecls___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwFindDecls___closed__1);
l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0 = _init_l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0();
l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg___closed__0 = _init_l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg___closed__0);
l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0 = _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0();
lean_mark_persistent(l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0);
l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1 = _init_l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1);
l_Lean_Meta_Rewrites_solveByElim___closed__0 = _init_l_Lean_Meta_Rewrites_solveByElim___closed__0();
lean_mark_persistent(l_Lean_Meta_Rewrites_solveByElim___closed__0);
l_Lean_Meta_Rewrites_solveByElim___closed__1 = _init_l_Lean_Meta_Rewrites_solveByElim___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_solveByElim___closed__1);
l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0 = _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0);
l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1 = _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1);
l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2 = _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2);
l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3 = _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3);
l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4 = _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4);
l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5 = _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5);
l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6 = _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6);
l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7 = _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__7);
l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0 = _init_l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0);
l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__0 = _init_l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__0();
lean_mark_persistent(l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__0);
l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__1 = _init_l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__1();
lean_mark_persistent(l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__1);
l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__2 = _init_l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__2();
lean_mark_persistent(l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__2);
l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__3 = _init_l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__3();
lean_mark_persistent(l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__3);
l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__4 = _init_l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__4();
lean_mark_persistent(l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__4);
l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__5 = _init_l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__5();
lean_mark_persistent(l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__5);
l_Lean_Meta_Rewrites_rewriteCandidates___closed__0 = _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__0();
lean_mark_persistent(l_Lean_Meta_Rewrites_rewriteCandidates___closed__0);
l_Lean_Meta_Rewrites_rewriteCandidates___closed__1 = _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_rewriteCandidates___closed__1);
l_Lean_Meta_Rewrites_rewriteCandidates___closed__2 = _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2();
lean_mark_persistent(l_Lean_Meta_Rewrites_rewriteCandidates___closed__2);
l_Lean_Meta_Rewrites_rewriteCandidates___closed__3 = _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3();
lean_mark_persistent(l_Lean_Meta_Rewrites_rewriteCandidates___closed__3);
l_Lean_Meta_Rewrites_rewriteCandidates___closed__4 = _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__4();
lean_mark_persistent(l_Lean_Meta_Rewrites_rewriteCandidates___closed__4);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___closed__0);
l_Lean_Meta_Rewrites_takeListAux___closed__0 = _init_l_Lean_Meta_Rewrites_takeListAux___closed__0();
lean_mark_persistent(l_Lean_Meta_Rewrites_takeListAux___closed__0);
l_Lean_Meta_Rewrites_findRewrites___closed__0 = _init_l_Lean_Meta_Rewrites_findRewrites___closed__0();
lean_mark_persistent(l_Lean_Meta_Rewrites_findRewrites___closed__0);
l_Lean_Meta_Rewrites_findRewrites___closed__1 = _init_l_Lean_Meta_Rewrites_findRewrites___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_findRewrites___closed__1);
l_Lean_Meta_Rewrites_findRewrites___closed__2 = _init_l_Lean_Meta_Rewrites_findRewrites___closed__2();
lean_mark_persistent(l_Lean_Meta_Rewrites_findRewrites___closed__2);
l_Lean_Meta_Rewrites_findRewrites___closed__3 = _init_l_Lean_Meta_Rewrites_findRewrites___closed__3();
lean_mark_persistent(l_Lean_Meta_Rewrites_findRewrites___closed__3);
l_Lean_Meta_Rewrites_findRewrites___closed__4 = _init_l_Lean_Meta_Rewrites_findRewrites___closed__4();
lean_mark_persistent(l_Lean_Meta_Rewrites_findRewrites___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
