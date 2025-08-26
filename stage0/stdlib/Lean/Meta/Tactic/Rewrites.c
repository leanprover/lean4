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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_paren(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_findRewrites___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResultConfig_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma___closed__0;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_localHypotheses_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__15____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
lean_object* l_Array_reverse___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__21____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
static lean_object* l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__3;
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResultConfig_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_toCtorIdx___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_localHypotheses___closed__0;
static lean_object* l_Lean_Meta_Rewrites_findRewrites___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg(uint8_t, uint8_t);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__6____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__0;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default;
uint64_t lean_string_hash(lean_object*);
lean_object* l_Option_toLOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__4(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_solveByElim___closed__1;
static lean_object* l_Lean_Meta_Rewrites_solveByElim___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2;
lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma___boxed(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0____x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__4;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Rewrites_rwLemma_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___Lean_Meta_Rewrites_localHypotheses_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__7;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__5;
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__19____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__9____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Rewrites_rwLemma_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at_____private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Rewrites_rwLemma_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___redArg(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Rewrites_rwLemma_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_findRewrites___closed__2;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__12____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__18____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_RewriteResult_addSuggestion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isMetaprogramming(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwFindDecls___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0;
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_localHypotheses_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4;
static lean_object* l_Lean_Meta_Rewrites_findRewrites___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr_2616605480____hygCtx___hyg_9_(uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__17____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
static uint64_t l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Rewrites_rwLemma_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0;
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__2;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_incPrio(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at_____private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__14____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__6;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_takeListAux___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__20____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Rewrites_rwLemma_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxHeartbeats___redArg(lean_object*, lean_object*);
lean_object* l_String_hash___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__3;
LEAN_EXPORT lean_object* l_List_elem___at___Lean_Meta_Rewrites_localHypotheses_spec__0___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Rewrites_rwLemma_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__22____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__13____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__0;
static lean_object* l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__1;
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__8____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___boxed(lean_object*);
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__16____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_backwardWeight;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg___lam__0(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__4;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_forwardWeight;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object*);
static lean_object* l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__5;
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__1;
lean_object* l_Lean_Expr_getAppFnArgs(lean_object*);
lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getRemainingHeartbeats___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
static lean_object* l_List_mapTR_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__5___closed__0;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__11____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwFindDecls___closed__1;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__7;
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_droppedKeys;
static lean_object* l_Lean_Meta_Rewrites_findRewrites___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx(uint8_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Rewrites_rwLemma_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Rewrites_rwLemma_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rewrites", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__6____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__8____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__6____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__9____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__8____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Rewrites", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__11____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__9____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__12____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__11____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__13____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__12____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__14____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__13____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__15____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__14____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__16____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__17____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__16____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__15____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__18____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__19____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__18____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__17____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__20____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__19____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__21____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__20____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__22____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__21____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__22____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2316440083u);
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hygCtx", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = 0;
x_4 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lemmas", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(414759425u);
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
x_3 = 0;
x_4 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
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
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Meta_Rewrites_RwDirection_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Rewrites_RwDirection_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
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
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Meta_Rewrites_RwDirection_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Meta_Rewrites_RwDirection_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0), 8, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
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
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), x_2, x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
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
lean_inc_ref(x_19);
lean_dec_ref(x_14);
x_20 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
x_23 = lean_string_dec_eq(x_19, x_22);
lean_dec_ref(x_19);
if (x_23 == 0)
{
lean_free_object(x_13);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_9 = x_8;
goto block_12;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_fget_borrowed(x_17, x_27);
x_29 = 0;
x_30 = lean_box(x_29);
lean_inc(x_1);
lean_ctor_set(x_13, 1, x_30);
lean_ctor_set(x_13, 0, x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_28);
x_31 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_28, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_array_fget(x_17, x_34);
lean_dec(x_17);
x_36 = 1;
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_35, x_38, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3;
x_43 = lean_array_push(x_42, x_32);
x_44 = lean_array_push(x_43, x_41);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
x_47 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3;
x_48 = lean_array_push(x_47, x_32);
x_49 = lean_array_push(x_48, x_45);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_32);
x_51 = !lean_is_exclusive(x_39);
if (x_51 == 0)
{
return x_39;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_39, 0);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_39);
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
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_31);
if (x_55 == 0)
{
return x_31;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_31, 0);
x_57 = lean_ctor_get(x_31, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_31);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec_ref(x_19);
x_59 = lean_array_get_size(x_17);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_dec_eq(x_59, x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_free_object(x_13);
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_9 = x_8;
goto block_12;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_array_fget_borrowed(x_17, x_62);
x_64 = 0;
x_65 = lean_box(x_64);
lean_inc(x_1);
lean_ctor_set(x_13, 1, x_65);
lean_ctor_set(x_13, 0, x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_63);
x_66 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_63, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec_ref(x_66);
x_69 = lean_unsigned_to_nat(2u);
x_70 = lean_array_fget(x_17, x_69);
lean_dec(x_17);
x_71 = 1;
x_72 = lean_box(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_70, x_73, x_4, x_5, x_6, x_7, x_68);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3;
x_78 = lean_array_push(x_77, x_67);
x_79 = lean_array_push(x_78, x_76);
lean_ctor_set(x_74, 0, x_79);
return x_74;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_74, 0);
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_74);
x_82 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3;
x_83 = lean_array_push(x_82, x_67);
x_84 = lean_array_push(x_83, x_80);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_67);
x_86 = !lean_is_exclusive(x_74);
if (x_86 == 0)
{
return x_74;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_74, 0);
x_88 = lean_ctor_get(x_74, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_74);
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
lean_dec(x_17);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_66);
if (x_90 == 0)
{
return x_66;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_66, 0);
x_92 = lean_ctor_get(x_66, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_66);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = lean_ctor_get(x_13, 1);
lean_inc(x_94);
lean_dec(x_13);
x_95 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_95);
lean_dec_ref(x_14);
x_96 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
x_97 = lean_string_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
x_99 = lean_string_dec_eq(x_95, x_98);
lean_dec_ref(x_95);
if (x_99 == 0)
{
lean_dec(x_94);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_9 = x_8;
goto block_12;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_array_get_size(x_94);
x_101 = lean_unsigned_to_nat(2u);
x_102 = lean_nat_dec_eq(x_100, x_101);
lean_dec(x_100);
if (x_102 == 0)
{
lean_dec(x_94);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_9 = x_8;
goto block_12;
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_unsigned_to_nat(0u);
x_104 = lean_array_fget_borrowed(x_94, x_103);
x_105 = 0;
x_106 = lean_box(x_105);
lean_inc(x_1);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_1);
lean_ctor_set(x_107, 1, x_106);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_104);
x_108 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_104, x_107, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec_ref(x_108);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_array_fget(x_94, x_111);
lean_dec(x_94);
x_113 = 1;
x_114 = lean_box(x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_1);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_112, x_115, x_4, x_5, x_6, x_7, x_110);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3;
x_121 = lean_array_push(x_120, x_109);
x_122 = lean_array_push(x_121, x_117);
if (lean_is_scalar(x_119)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_119;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_118);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_109);
x_124 = lean_ctor_get(x_116, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_116, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_126 = x_116;
} else {
 lean_dec_ref(x_116);
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
lean_dec(x_94);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_128 = lean_ctor_get(x_108, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_108, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_130 = x_108;
} else {
 lean_dec_ref(x_108);
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
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
lean_dec_ref(x_95);
x_132 = lean_array_get_size(x_94);
x_133 = lean_unsigned_to_nat(3u);
x_134 = lean_nat_dec_eq(x_132, x_133);
lean_dec(x_132);
if (x_134 == 0)
{
lean_dec(x_94);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_9 = x_8;
goto block_12;
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_array_fget_borrowed(x_94, x_135);
x_137 = 0;
x_138 = lean_box(x_137);
lean_inc(x_1);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_1);
lean_ctor_set(x_139, 1, x_138);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_136);
x_140 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_136, x_139, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec_ref(x_140);
x_143 = lean_unsigned_to_nat(2u);
x_144 = lean_array_fget(x_94, x_143);
lean_dec(x_94);
x_145 = 1;
x_146 = lean_box(x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_1);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___redArg(x_144, x_147, x_4, x_5, x_6, x_7, x_142);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_151 = x_148;
} else {
 lean_dec_ref(x_148);
 x_151 = lean_box(0);
}
x_152 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__3;
x_153 = lean_array_push(x_152, x_141);
x_154 = lean_array_push(x_153, x_149);
if (lean_is_scalar(x_151)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_151;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_150);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_141);
x_156 = lean_ctor_get(x_148, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_148, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_158 = x_148;
} else {
 lean_dec_ref(x_148);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_94);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_160 = lean_ctor_get(x_140, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_140, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_162 = x_140;
} else {
 lean_dec_ref(x_140);
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
}
else
{
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_9 = x_8;
goto block_12;
}
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_Context_config(x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint64_t x_21; uint8_t x_22; 
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_5, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 6);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 2);
lean_ctor_set_uint8(x_10, 9, x_1);
x_21 = l_Lean_Meta_Context_configKey(x_5);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; 
x_23 = lean_ctor_get(x_5, 6);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 5);
lean_dec(x_24);
x_25 = lean_ctor_get(x_5, 4);
lean_dec(x_25);
x_26 = lean_ctor_get(x_5, 3);
lean_dec(x_26);
x_27 = lean_ctor_get(x_5, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_5, 0);
lean_dec(x_29);
x_30 = 2;
x_31 = lean_uint64_shift_right(x_21, x_30);
x_32 = lean_uint64_shift_left(x_31, x_30);
x_33 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_34 = lean_uint64_lor(x_32, x_33);
x_35 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_35, 0, x_10);
lean_ctor_set_uint64(x_35, sizeof(void*)*1, x_34);
lean_ctor_set(x_5, 0, x_35);
x_36 = l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(x_2, x_3, x_4, x_4, x_5, x_6, x_7, x_8, x_9);
return x_36;
}
else
{
uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_5);
x_37 = 2;
x_38 = lean_uint64_shift_right(x_21, x_37);
x_39 = lean_uint64_shift_left(x_38, x_37);
x_40 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_41 = lean_uint64_lor(x_39, x_40);
x_42 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_42, 0, x_10);
lean_ctor_set_uint64(x_42, sizeof(void*)*1, x_41);
x_43 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_13);
lean_ctor_set(x_43, 2, x_14);
lean_ctor_set(x_43, 3, x_15);
lean_ctor_set(x_43, 4, x_16);
lean_ctor_set(x_43, 5, x_17);
lean_ctor_set(x_43, 6, x_18);
lean_ctor_set_uint8(x_43, sizeof(void*)*7, x_12);
lean_ctor_set_uint8(x_43, sizeof(void*)*7 + 1, x_19);
lean_ctor_set_uint8(x_43, sizeof(void*)*7 + 2, x_20);
x_44 = l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(x_2, x_3, x_4, x_4, x_43, x_6, x_7, x_8, x_9);
return x_44;
}
}
else
{
uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; uint64_t x_73; lean_object* x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_45 = lean_ctor_get_uint8(x_10, 0);
x_46 = lean_ctor_get_uint8(x_10, 1);
x_47 = lean_ctor_get_uint8(x_10, 2);
x_48 = lean_ctor_get_uint8(x_10, 3);
x_49 = lean_ctor_get_uint8(x_10, 4);
x_50 = lean_ctor_get_uint8(x_10, 5);
x_51 = lean_ctor_get_uint8(x_10, 6);
x_52 = lean_ctor_get_uint8(x_10, 7);
x_53 = lean_ctor_get_uint8(x_10, 8);
x_54 = lean_ctor_get_uint8(x_10, 10);
x_55 = lean_ctor_get_uint8(x_10, 11);
x_56 = lean_ctor_get_uint8(x_10, 12);
x_57 = lean_ctor_get_uint8(x_10, 13);
x_58 = lean_ctor_get_uint8(x_10, 14);
x_59 = lean_ctor_get_uint8(x_10, 15);
x_60 = lean_ctor_get_uint8(x_10, 16);
x_61 = lean_ctor_get_uint8(x_10, 17);
x_62 = lean_ctor_get_uint8(x_10, 18);
lean_dec(x_10);
x_63 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
x_64 = lean_ctor_get(x_5, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_5, 4);
lean_inc(x_67);
x_68 = lean_ctor_get(x_5, 5);
lean_inc(x_68);
x_69 = lean_ctor_get(x_5, 6);
lean_inc(x_69);
x_70 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
x_71 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 2);
x_72 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_72, 0, x_45);
lean_ctor_set_uint8(x_72, 1, x_46);
lean_ctor_set_uint8(x_72, 2, x_47);
lean_ctor_set_uint8(x_72, 3, x_48);
lean_ctor_set_uint8(x_72, 4, x_49);
lean_ctor_set_uint8(x_72, 5, x_50);
lean_ctor_set_uint8(x_72, 6, x_51);
lean_ctor_set_uint8(x_72, 7, x_52);
lean_ctor_set_uint8(x_72, 8, x_53);
lean_ctor_set_uint8(x_72, 9, x_1);
lean_ctor_set_uint8(x_72, 10, x_54);
lean_ctor_set_uint8(x_72, 11, x_55);
lean_ctor_set_uint8(x_72, 12, x_56);
lean_ctor_set_uint8(x_72, 13, x_57);
lean_ctor_set_uint8(x_72, 14, x_58);
lean_ctor_set_uint8(x_72, 15, x_59);
lean_ctor_set_uint8(x_72, 16, x_60);
lean_ctor_set_uint8(x_72, 17, x_61);
lean_ctor_set_uint8(x_72, 18, x_62);
x_73 = l_Lean_Meta_Context_configKey(x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 x_74 = x_5;
} else {
 lean_dec_ref(x_5);
 x_74 = lean_box(0);
}
x_75 = 2;
x_76 = lean_uint64_shift_right(x_73, x_75);
x_77 = lean_uint64_shift_left(x_76, x_75);
x_78 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_79 = lean_uint64_lor(x_77, x_78);
x_80 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set_uint64(x_80, sizeof(void*)*1, x_79);
if (lean_is_scalar(x_74)) {
 x_81 = lean_alloc_ctor(0, 7, 3);
} else {
 x_81 = x_74;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_64);
lean_ctor_set(x_81, 2, x_65);
lean_ctor_set(x_81, 3, x_66);
lean_ctor_set(x_81, 4, x_67);
lean_ctor_set(x_81, 5, x_68);
lean_ctor_set(x_81, 6, x_69);
lean_ctor_set_uint8(x_81, sizeof(void*)*7, x_63);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 1, x_70);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 2, x_71);
x_82 = l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(x_2, x_3, x_4, x_4, x_81, x_6, x_7, x_8, x_9);
return x_82;
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
lean_inc_ref(x_19);
lean_dec(x_10);
lean_inc(x_1);
x_20 = l_Lean_Meta_allowCompletion(x_19, x_1);
if (x_20 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_1, 1);
x_38 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__0;
x_39 = lean_string_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__1;
x_41 = lean_string_dec_eq(x_37, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_string_utf8_byte_size(x_37);
lean_inc(x_43);
lean_inc_ref(x_37);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_unsigned_to_nat(4u);
lean_inc(x_43);
x_46 = l_Substring_prevn(x_44, x_45, x_43);
lean_inc(x_43);
lean_inc_ref(x_37);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_43);
x_48 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__4;
x_49 = l_Substring_beq(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_unsigned_to_nat(5u);
lean_inc(x_43);
x_51 = l_Substring_prevn(x_44, x_50, x_43);
lean_dec_ref(x_44);
lean_inc_ref(x_37);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_37);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_43);
x_53 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___closed__7;
x_54 = l_Substring_beq(x_52, x_53);
if (x_54 == 0)
{
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_11;
goto block_36;
}
else
{
lean_dec_ref(x_21);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
goto block_18;
}
}
else
{
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_21);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
goto block_18;
}
}
else
{
lean_dec_ref(x_21);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
goto block_18;
}
}
else
{
lean_dec_ref(x_21);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
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
goto block_36;
}
block_36:
{
uint8_t x_27; 
x_27 = l_Lean_Name_isMetaprogramming(x_1);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = l_Lean_ConstantInfo_type(x_2);
x_29 = 2;
x_30 = lean_box(x_29);
x_31 = lean_box(x_27);
x_32 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed), 9, 4);
lean_closure_set(x_32, 0, x_30);
lean_closure_set(x_32, 1, x_28);
lean_closure_set(x_32, 2, x_21);
lean_closure_set(x_32, 3, x_31);
x_33 = l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(x_32, x_27, x_22, x_23, x_24, x_25, x_26);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
x_34 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_object* x_55; lean_object* x_56; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_55 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__0;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_7);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_withNewMCtxDepth___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
x_11 = lean_unbox(x_4);
x_12 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__1(x_10, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___Lean_Meta_Rewrites_localHypotheses_spec__0(lean_object* x_1, lean_object* x_2) {
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
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = lean_array_uget(x_3, x_5);
lean_inc(x_15);
x_18 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1(x_1, x_17, x_15, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_6, 0, x_22);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_15);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec_ref(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec_ref(x_19);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_27);
lean_ctor_set(x_6, 0, x_2);
x_28 = 1;
x_29 = lean_usize_add(x_5, x_28);
x_5 = x_29;
x_11 = x_26;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_dec(x_6);
x_32 = lean_array_uget(x_3, x_5);
lean_inc(x_31);
x_33 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1(x_1, x_32, x_31, x_7, x_8, x_9, x_10, x_11);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
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
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; 
lean_dec(x_31);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec_ref(x_33);
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
lean_dec_ref(x_34);
lean_inc(x_2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_2);
lean_ctor_set(x_42, 1, x_41);
x_43 = 1;
x_44 = lean_usize_add(x_5, x_43);
x_5 = x_44;
x_6 = x_42;
x_11 = x_40;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec_ref(x_5);
x_17 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_17) == 0)
{
x_7 = x_16;
x_8 = x_6;
goto block_13;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_LocalDecl_isImplementationDetail(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_LocalDecl_toExpr(x_18);
x_21 = lean_array_push(x_16, x_20);
x_7 = x_21;
x_8 = x_6;
goto block_13;
}
else
{
lean_dec(x_18);
x_7 = x_16;
x_8 = x_6;
goto block_13;
}
}
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
x_5 = x_9;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_4, x_3);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec_ref(x_5);
x_21 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_21) == 0)
{
x_11 = x_20;
x_12 = x_10;
goto block_17;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Lean_LocalDecl_isImplementationDetail(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_LocalDecl_toExpr(x_22);
x_25 = lean_array_push(x_20, x_24);
x_11 = x_25;
x_12 = x_10;
goto block_17;
}
else
{
lean_dec(x_22);
x_11 = x_20;
x_12 = x_10;
goto block_17;
}
}
}
block_17:
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_11);
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2_spec__2___redArg(x_1, x_2, x_3, x_15, x_13, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_array_size(x_10);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__1(x_1, x_11, x_10, x_13, x_14, x_12, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_20);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_inc_ref(x_17);
lean_dec(x_16);
lean_free_object(x_2);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec_ref(x_17);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec_ref(x_17);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
x_33 = lean_array_size(x_30);
x_34 = 0;
x_35 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__1(x_1, x_31, x_30, x_33, x_34, x_32, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_30);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_39 = x_35;
} else {
 lean_dec_ref(x_35);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc_ref(x_37);
lean_dec(x_36);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_44 = x_35;
} else {
 lean_dec_ref(x_35);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
lean_dec_ref(x_37);
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
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_2, 0);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_3);
x_51 = lean_array_size(x_48);
x_52 = 0;
x_53 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2(x_49, x_48, x_51, x_52, x_50, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_48);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 0);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_53, 0);
lean_dec(x_57);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
lean_ctor_set(x_2, 0, x_58);
lean_ctor_set(x_53, 0, x_2);
return x_53;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
lean_ctor_set(x_2, 0, x_60);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_2);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_inc_ref(x_55);
lean_dec(x_54);
lean_free_object(x_2);
x_62 = !lean_is_exclusive(x_53);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_53, 0);
lean_dec(x_63);
x_64 = lean_ctor_get(x_55, 0);
lean_inc(x_64);
lean_dec_ref(x_55);
lean_ctor_set(x_53, 0, x_64);
return x_53;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_53, 1);
lean_inc(x_65);
lean_dec(x_53);
x_66 = lean_ctor_get(x_55, 0);
lean_inc(x_66);
lean_dec_ref(x_55);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_2, 0);
lean_inc(x_68);
lean_dec(x_2);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_3);
x_71 = lean_array_size(x_68);
x_72 = 0;
x_73 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2(x_69, x_68, x_71, x_72, x_70, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_68);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 0);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_77 = x_73;
} else {
 lean_dec_ref(x_73);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_77;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_76);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_inc_ref(x_75);
lean_dec(x_74);
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_82 = x_73;
} else {
 lean_dec_ref(x_73);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_75, 0);
lean_inc(x_83);
lean_dec_ref(x_75);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5_spec__5___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec_ref(x_5);
x_17 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_17) == 0)
{
x_7 = x_16;
x_8 = x_6;
goto block_13;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_LocalDecl_isImplementationDetail(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_LocalDecl_toExpr(x_18);
x_21 = lean_array_push(x_16, x_20);
x_7 = x_21;
x_8 = x_6;
goto block_13;
}
else
{
lean_dec(x_18);
x_7 = x_16;
x_8 = x_6;
goto block_13;
}
}
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
x_5 = x_9;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_4, x_3);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec_ref(x_5);
x_21 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_21) == 0)
{
x_11 = x_20;
x_12 = x_10;
goto block_17;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Lean_LocalDecl_isImplementationDetail(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_LocalDecl_toExpr(x_22);
x_25 = lean_array_push(x_20, x_24);
x_11 = x_25;
x_12 = x_10;
goto block_17;
}
else
{
lean_dec(x_22);
x_11 = x_20;
x_12 = x_10;
goto block_17;
}
}
}
block_17:
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_11);
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5_spec__5___redArg(x_1, x_2, x_3, x_15, x_13, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_10 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1(x_2, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec_ref(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec_ref(x_11);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec_ref(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec_ref(x_11);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_array_size(x_9);
x_23 = 0;
x_24 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5(x_20, x_9, x_22, x_23, x_21, x_3, x_4, x_5, x_6, x_18);
lean_dec_ref(x_9);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_inc_ref(x_26);
lean_dec(x_25);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec_ref(x_26);
lean_ctor_set(x_24, 0, x_35);
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_dec(x_24);
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
lean_dec_ref(x_26);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
}
static lean_object* _init_l_Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_7);
x_8 = l_Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0;
x_9 = l_Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(x_7, x_8, x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_localHypotheses_spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_4, x_3);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_19);
x_22 = lean_infer_type(x_19, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_box(0);
x_26 = 0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_27 = l_Lean_Meta_forallMetaTelescopeReducing(x_23, x_25, x_26, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec_ref(x_27);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
x_35 = lean_ctor_get(x_30, 0);
lean_dec(x_35);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_36 = l_Lean_Meta_whnfR(x_34, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Lean_Expr_getAppFnArgs(x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_39, 1);
x_44 = lean_ctor_get(x_39, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_45);
lean_dec_ref(x_40);
x_46 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
x_47 = lean_string_dec_eq(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
x_49 = lean_string_dec_eq(x_45, x_48);
lean_dec_ref(x_45);
if (x_49 == 0)
{
lean_free_object(x_39);
lean_dec(x_43);
lean_free_object(x_30);
lean_free_object(x_28);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_38;
goto block_16;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_array_get_size(x_43);
lean_dec(x_43);
x_51 = lean_unsigned_to_nat(2u);
x_52 = lean_nat_dec_eq(x_50, x_51);
lean_dec(x_50);
if (x_52 == 0)
{
lean_free_object(x_39);
lean_free_object(x_30);
lean_free_object(x_28);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_38;
goto block_16;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_box(x_21);
lean_ctor_set(x_39, 1, x_51);
lean_ctor_set(x_39, 0, x_53);
lean_inc_ref(x_19);
lean_ctor_set(x_30, 1, x_39);
lean_ctor_set(x_30, 0, x_19);
x_54 = lean_array_push(x_5, x_30);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_box(x_52);
lean_ctor_set(x_28, 1, x_55);
lean_ctor_set(x_28, 0, x_56);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_19);
lean_ctor_set(x_57, 1, x_28);
x_58 = lean_array_push(x_54, x_57);
x_11 = x_58;
x_12 = x_38;
goto block_16;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec_ref(x_45);
x_59 = lean_array_get_size(x_43);
lean_dec(x_43);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_dec_eq(x_59, x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_free_object(x_39);
lean_free_object(x_30);
lean_free_object(x_28);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_38;
goto block_16;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_unsigned_to_nat(2u);
x_63 = lean_box(x_21);
lean_ctor_set(x_39, 1, x_62);
lean_ctor_set(x_39, 0, x_63);
lean_inc_ref(x_19);
lean_ctor_set(x_30, 1, x_39);
lean_ctor_set(x_30, 0, x_19);
x_64 = lean_array_push(x_5, x_30);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_box(x_61);
lean_ctor_set(x_28, 1, x_65);
lean_ctor_set(x_28, 0, x_66);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_19);
lean_ctor_set(x_67, 1, x_28);
x_68 = lean_array_push(x_64, x_67);
x_11 = x_68;
x_12 = x_38;
goto block_16;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_39, 1);
lean_inc(x_69);
lean_dec(x_39);
x_70 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_70);
lean_dec_ref(x_40);
x_71 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
x_72 = lean_string_dec_eq(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
x_74 = lean_string_dec_eq(x_70, x_73);
lean_dec_ref(x_70);
if (x_74 == 0)
{
lean_dec(x_69);
lean_free_object(x_30);
lean_free_object(x_28);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_38;
goto block_16;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_array_get_size(x_69);
lean_dec(x_69);
x_76 = lean_unsigned_to_nat(2u);
x_77 = lean_nat_dec_eq(x_75, x_76);
lean_dec(x_75);
if (x_77 == 0)
{
lean_free_object(x_30);
lean_free_object(x_28);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_38;
goto block_16;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_box(x_21);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
lean_inc_ref(x_19);
lean_ctor_set(x_30, 1, x_79);
lean_ctor_set(x_30, 0, x_19);
x_80 = lean_array_push(x_5, x_30);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_box(x_77);
lean_ctor_set(x_28, 1, x_81);
lean_ctor_set(x_28, 0, x_82);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_19);
lean_ctor_set(x_83, 1, x_28);
x_84 = lean_array_push(x_80, x_83);
x_11 = x_84;
x_12 = x_38;
goto block_16;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec_ref(x_70);
x_85 = lean_array_get_size(x_69);
lean_dec(x_69);
x_86 = lean_unsigned_to_nat(3u);
x_87 = lean_nat_dec_eq(x_85, x_86);
lean_dec(x_85);
if (x_87 == 0)
{
lean_free_object(x_30);
lean_free_object(x_28);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_38;
goto block_16;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = lean_unsigned_to_nat(2u);
x_89 = lean_box(x_21);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
lean_inc_ref(x_19);
lean_ctor_set(x_30, 1, x_90);
lean_ctor_set(x_30, 0, x_19);
x_91 = lean_array_push(x_5, x_30);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_box(x_87);
lean_ctor_set(x_28, 1, x_92);
lean_ctor_set(x_28, 0, x_93);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_19);
lean_ctor_set(x_94, 1, x_28);
x_95 = lean_array_push(x_91, x_94);
x_11 = x_95;
x_12 = x_38;
goto block_16;
}
}
}
}
else
{
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_free_object(x_30);
lean_free_object(x_28);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_38;
goto block_16;
}
}
else
{
lean_dec(x_40);
lean_dec_ref(x_39);
lean_free_object(x_30);
lean_free_object(x_28);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_38;
goto block_16;
}
}
else
{
uint8_t x_96; 
lean_free_object(x_30);
lean_free_object(x_28);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_96 = !lean_is_exclusive(x_36);
if (x_96 == 0)
{
return x_36;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_36, 0);
x_98 = lean_ctor_get(x_36, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_36);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_30, 1);
lean_inc(x_100);
lean_dec(x_30);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_101 = l_Lean_Meta_whnfR(x_100, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec_ref(x_101);
x_104 = l_Lean_Expr_getAppFnArgs(x_102);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 1)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_108 = x_104;
} else {
 lean_dec_ref(x_104);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_105, 1);
lean_inc_ref(x_109);
lean_dec_ref(x_105);
x_110 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
x_111 = lean_string_dec_eq(x_109, x_110);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
x_113 = lean_string_dec_eq(x_109, x_112);
lean_dec_ref(x_109);
if (x_113 == 0)
{
lean_dec(x_108);
lean_dec(x_107);
lean_free_object(x_28);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_103;
goto block_16;
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_array_get_size(x_107);
lean_dec(x_107);
x_115 = lean_unsigned_to_nat(2u);
x_116 = lean_nat_dec_eq(x_114, x_115);
lean_dec(x_114);
if (x_116 == 0)
{
lean_dec(x_108);
lean_free_object(x_28);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_103;
goto block_16;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_box(x_21);
if (lean_is_scalar(x_108)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_108;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
lean_inc_ref(x_19);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_19);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_array_push(x_5, x_119);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_box(x_116);
lean_ctor_set(x_28, 1, x_121);
lean_ctor_set(x_28, 0, x_122);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_19);
lean_ctor_set(x_123, 1, x_28);
x_124 = lean_array_push(x_120, x_123);
x_11 = x_124;
x_12 = x_103;
goto block_16;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec_ref(x_109);
x_125 = lean_array_get_size(x_107);
lean_dec(x_107);
x_126 = lean_unsigned_to_nat(3u);
x_127 = lean_nat_dec_eq(x_125, x_126);
lean_dec(x_125);
if (x_127 == 0)
{
lean_dec(x_108);
lean_free_object(x_28);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_103;
goto block_16;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_128 = lean_unsigned_to_nat(2u);
x_129 = lean_box(x_21);
if (lean_is_scalar(x_108)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_108;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
lean_inc_ref(x_19);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_19);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_array_push(x_5, x_131);
x_133 = lean_unsigned_to_nat(1u);
x_134 = lean_box(x_127);
lean_ctor_set(x_28, 1, x_133);
lean_ctor_set(x_28, 0, x_134);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_19);
lean_ctor_set(x_135, 1, x_28);
x_136 = lean_array_push(x_132, x_135);
x_11 = x_136;
x_12 = x_103;
goto block_16;
}
}
}
else
{
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_free_object(x_28);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_103;
goto block_16;
}
}
else
{
lean_dec(x_105);
lean_dec_ref(x_104);
lean_free_object(x_28);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_103;
goto block_16;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_free_object(x_28);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_137 = lean_ctor_get(x_101, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_101, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_139 = x_101;
} else {
 lean_dec_ref(x_101);
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
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_28, 1);
lean_inc(x_141);
lean_dec(x_28);
x_142 = lean_ctor_get(x_27, 1);
lean_inc(x_142);
lean_dec_ref(x_27);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_145 = l_Lean_Meta_whnfR(x_143, x_6, x_7, x_8, x_9, x_142);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec_ref(x_145);
x_148 = l_Lean_Expr_getAppFnArgs(x_146);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 1)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_152 = x_148;
} else {
 lean_dec_ref(x_148);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_149, 1);
lean_inc_ref(x_153);
lean_dec_ref(x_149);
x_154 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__1;
x_155 = lean_string_dec_eq(x_153, x_154);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lam__0___closed__2;
x_157 = lean_string_dec_eq(x_153, x_156);
lean_dec_ref(x_153);
if (x_157 == 0)
{
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_144);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_147;
goto block_16;
}
else
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_158 = lean_array_get_size(x_151);
lean_dec(x_151);
x_159 = lean_unsigned_to_nat(2u);
x_160 = lean_nat_dec_eq(x_158, x_159);
lean_dec(x_158);
if (x_160 == 0)
{
lean_dec(x_152);
lean_dec(x_144);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_147;
goto block_16;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_161 = lean_box(x_21);
if (lean_is_scalar(x_152)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_152;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_159);
lean_inc_ref(x_19);
if (lean_is_scalar(x_144)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_144;
}
lean_ctor_set(x_163, 0, x_19);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_array_push(x_5, x_163);
x_165 = lean_unsigned_to_nat(1u);
x_166 = lean_box(x_160);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_19);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_array_push(x_164, x_168);
x_11 = x_169;
x_12 = x_147;
goto block_16;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
lean_dec_ref(x_153);
x_170 = lean_array_get_size(x_151);
lean_dec(x_151);
x_171 = lean_unsigned_to_nat(3u);
x_172 = lean_nat_dec_eq(x_170, x_171);
lean_dec(x_170);
if (x_172 == 0)
{
lean_dec(x_152);
lean_dec(x_144);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_147;
goto block_16;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_173 = lean_unsigned_to_nat(2u);
x_174 = lean_box(x_21);
if (lean_is_scalar(x_152)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_152;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
lean_inc_ref(x_19);
if (lean_is_scalar(x_144)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_144;
}
lean_ctor_set(x_176, 0, x_19);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_array_push(x_5, x_176);
x_178 = lean_unsigned_to_nat(1u);
x_179 = lean_box(x_172);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_19);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_array_push(x_177, x_181);
x_11 = x_182;
x_12 = x_147;
goto block_16;
}
}
}
else
{
lean_dec_ref(x_149);
lean_dec_ref(x_148);
lean_dec(x_144);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_147;
goto block_16;
}
}
else
{
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_144);
lean_dec_ref(x_19);
x_11 = x_5;
x_12 = x_147;
goto block_16;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_144);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_183 = lean_ctor_get(x_145, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_145, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_185 = x_145;
} else {
 lean_dec_ref(x_145);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
}
else
{
uint8_t x_187; 
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_187 = !lean_is_exclusive(x_27);
if (x_187 == 0)
{
return x_27;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_27, 0);
x_189 = lean_ctor_get(x_27, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_27);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_191 = !lean_is_exclusive(x_22);
if (x_191 == 0)
{
return x_22;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_22, 0);
x_193 = lean_ctor_get(x_22, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_22);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
else
{
lean_dec_ref(x_19);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
lean_inc_ref(x_2);
x_7 = l_Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Lean_Meta_Rewrites_localHypotheses___closed__0;
x_11 = lean_array_size(x_8);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_localHypotheses_spec__9(x_1, x_8, x_11, x_12, x_10, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_8);
return x_13;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2_spec__2___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2_spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1_spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5_spec__5___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5_spec__5(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1_spec__5(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forIn___at___Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_localHypotheses_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_localHypotheses_spec__9(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2_(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0____x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___lam__0____x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_box(2);
x_5 = l_Lean_registerEnvExtension___redArg(x_3, x_2, x_4, x_1);
return x_5;
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
x_4 = lean_unbox(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_dec(x_7);
x_8 = 0;
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_mul(x_9, x_1);
lean_dec(x_1);
x_11 = lean_box(x_8);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_2, 0, x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_2);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = 0;
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_mul(x_15, x_1);
lean_dec(x_1);
x_17 = lean_box(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
lean_dec(x_22);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_2);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
return x_30;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Rewrites_RewriteResult_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_saveState___redArg(x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc(x_3);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5, x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
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
uint8_t x_18; 
lean_dec(x_11);
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
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec_ref(x_10);
x_24 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5, x_23);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_22);
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
}
else
{
uint8_t x_33; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_7);
if (x_33 == 0)
{
return x_7;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static uint64_t _init_l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 2;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_4);
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_Meta_Context_config(x_4);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; uint64_t x_25; uint8_t x_26; 
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_4, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 5);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 6);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 1);
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 2);
x_23 = l_Lean_Expr_mvarId_x21(x_10);
lean_dec(x_10);
x_24 = 2;
lean_ctor_set_uint8(x_12, 9, x_24);
x_25 = l_Lean_Meta_Context_configKey(x_4);
x_26 = !lean_is_exclusive(x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; lean_object* x_39; lean_object* x_40; 
x_27 = lean_ctor_get(x_4, 6);
lean_dec(x_27);
x_28 = lean_ctor_get(x_4, 5);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 4);
lean_dec(x_29);
x_30 = lean_ctor_get(x_4, 3);
lean_dec(x_30);
x_31 = lean_ctor_get(x_4, 2);
lean_dec(x_31);
x_32 = lean_ctor_get(x_4, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_4, 0);
lean_dec(x_33);
x_34 = 2;
x_35 = lean_uint64_shift_right(x_25, x_34);
x_36 = lean_uint64_shift_left(x_35, x_34);
x_37 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0;
x_38 = lean_uint64_lor(x_36, x_37);
x_39 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set_uint64(x_39, sizeof(void*)*1, x_38);
lean_ctor_set(x_4, 0, x_39);
x_40 = l_Lean_MVarId_refl(x_23, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = 1;
x_44 = lean_box(x_43);
lean_ctor_set(x_40, 0, x_44);
return x_40;
}
else
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = 1;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_40);
if (x_49 == 0)
{
return x_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_40, 0);
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_40);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_4);
x_53 = 2;
x_54 = lean_uint64_shift_right(x_25, x_53);
x_55 = lean_uint64_shift_left(x_54, x_53);
x_56 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0;
x_57 = lean_uint64_lor(x_55, x_56);
x_58 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_58, 0, x_12);
lean_ctor_set_uint64(x_58, sizeof(void*)*1, x_57);
x_59 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_15);
lean_ctor_set(x_59, 2, x_16);
lean_ctor_set(x_59, 3, x_17);
lean_ctor_set(x_59, 4, x_18);
lean_ctor_set(x_59, 5, x_19);
lean_ctor_set(x_59, 6, x_20);
lean_ctor_set_uint8(x_59, sizeof(void*)*7, x_14);
lean_ctor_set_uint8(x_59, sizeof(void*)*7 + 1, x_21);
lean_ctor_set_uint8(x_59, sizeof(void*)*7 + 2, x_22);
x_60 = l_Lean_MVarId_refl(x_23, x_59, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
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
x_63 = 1;
x_64 = lean_box(x_63);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
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
}
else
{
uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; uint64_t x_100; lean_object* x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_70 = lean_ctor_get_uint8(x_12, 0);
x_71 = lean_ctor_get_uint8(x_12, 1);
x_72 = lean_ctor_get_uint8(x_12, 2);
x_73 = lean_ctor_get_uint8(x_12, 3);
x_74 = lean_ctor_get_uint8(x_12, 4);
x_75 = lean_ctor_get_uint8(x_12, 5);
x_76 = lean_ctor_get_uint8(x_12, 6);
x_77 = lean_ctor_get_uint8(x_12, 7);
x_78 = lean_ctor_get_uint8(x_12, 8);
x_79 = lean_ctor_get_uint8(x_12, 10);
x_80 = lean_ctor_get_uint8(x_12, 11);
x_81 = lean_ctor_get_uint8(x_12, 12);
x_82 = lean_ctor_get_uint8(x_12, 13);
x_83 = lean_ctor_get_uint8(x_12, 14);
x_84 = lean_ctor_get_uint8(x_12, 15);
x_85 = lean_ctor_get_uint8(x_12, 16);
x_86 = lean_ctor_get_uint8(x_12, 17);
x_87 = lean_ctor_get_uint8(x_12, 18);
lean_dec(x_12);
x_88 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
x_89 = lean_ctor_get(x_4, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_91);
x_92 = lean_ctor_get(x_4, 4);
lean_inc(x_92);
x_93 = lean_ctor_get(x_4, 5);
lean_inc(x_93);
x_94 = lean_ctor_get(x_4, 6);
lean_inc(x_94);
x_95 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 1);
x_96 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 2);
x_97 = l_Lean_Expr_mvarId_x21(x_10);
lean_dec(x_10);
x_98 = 2;
x_99 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_99, 0, x_70);
lean_ctor_set_uint8(x_99, 1, x_71);
lean_ctor_set_uint8(x_99, 2, x_72);
lean_ctor_set_uint8(x_99, 3, x_73);
lean_ctor_set_uint8(x_99, 4, x_74);
lean_ctor_set_uint8(x_99, 5, x_75);
lean_ctor_set_uint8(x_99, 6, x_76);
lean_ctor_set_uint8(x_99, 7, x_77);
lean_ctor_set_uint8(x_99, 8, x_78);
lean_ctor_set_uint8(x_99, 9, x_98);
lean_ctor_set_uint8(x_99, 10, x_79);
lean_ctor_set_uint8(x_99, 11, x_80);
lean_ctor_set_uint8(x_99, 12, x_81);
lean_ctor_set_uint8(x_99, 13, x_82);
lean_ctor_set_uint8(x_99, 14, x_83);
lean_ctor_set_uint8(x_99, 15, x_84);
lean_ctor_set_uint8(x_99, 16, x_85);
lean_ctor_set_uint8(x_99, 17, x_86);
lean_ctor_set_uint8(x_99, 18, x_87);
x_100 = l_Lean_Meta_Context_configKey(x_4);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 x_101 = x_4;
} else {
 lean_dec_ref(x_4);
 x_101 = lean_box(0);
}
x_102 = 2;
x_103 = lean_uint64_shift_right(x_100, x_102);
x_104 = lean_uint64_shift_left(x_103, x_102);
x_105 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___closed__0;
x_106 = lean_uint64_lor(x_104, x_105);
x_107 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_107, 0, x_99);
lean_ctor_set_uint64(x_107, sizeof(void*)*1, x_106);
if (lean_is_scalar(x_101)) {
 x_108 = lean_alloc_ctor(0, 7, 3);
} else {
 x_108 = x_101;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_89);
lean_ctor_set(x_108, 2, x_90);
lean_ctor_set(x_108, 3, x_91);
lean_ctor_set(x_108, 4, x_92);
lean_ctor_set(x_108, 5, x_93);
lean_ctor_set(x_108, 6, x_94);
lean_ctor_set_uint8(x_108, sizeof(void*)*7, x_88);
lean_ctor_set_uint8(x_108, sizeof(void*)*7 + 1, x_95);
lean_ctor_set_uint8(x_108, sizeof(void*)*7 + 2, x_96);
x_109 = l_Lean_MVarId_refl(x_97, x_108, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; 
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
x_112 = 1;
x_113 = lean_box(x_112);
if (lean_is_scalar(x_111)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_111;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_110);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_109, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_117 = x_109;
} else {
 lean_dec_ref(x_109);
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
else
{
uint8_t x_119; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_119 = !lean_is_exclusive(x_9);
if (x_119 == 0)
{
return x_9;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_9, 0);
x_121 = lean_ctor_get(x_9, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_9);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = 0;
x_10 = lean_box(0);
x_11 = lean_box(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0___boxed), 8, 3);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_12);
x_14 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_25; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_25 = l_Lean_Exception_isInterrupt(x_15);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Exception_isRuntime(x_15);
lean_dec(x_15);
x_17 = x_26;
goto block_24;
}
else
{
lean_dec(x_15);
x_17 = x_25;
goto block_24;
}
block_24:
{
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_14, 0);
lean_dec(x_20);
x_21 = lean_box(x_17);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
x_22 = lean_box(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
return x_23;
}
}
else
{
lean_dec(x_16);
return x_14;
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
x_10 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_Meta_ppExpr(x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
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
else
{
uint8_t x_21; 
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Rewrites_SideConditions_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
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
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Meta_Rewrites_SideConditions_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Meta_Rewrites_SideConditions_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
lean_inc_ref(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
lean_inc_ref(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_3, x_27);
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
x_33 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_4, 2);
lean_inc(x_35);
lean_inc_ref(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
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
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
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
x_8 = l_Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_box(0);
x_10 = l_Lean_Meta_Rewrites_solveByElim___closed__0;
lean_inc_ref(x_5);
x_11 = l_Lean_Meta_SolveByElim_mkAssumptionSet(x_8, x_8, x_9, x_9, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed), 7, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_solveByElim___lam__1___boxed), 6, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_solveByElim___lam__2___boxed), 6, 0);
x_19 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_8);
x_20 = 1;
x_21 = l_Lean_Meta_Rewrites_solveByElim___closed__1;
x_22 = 1;
x_23 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 1, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 2, x_8);
x_24 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*1 + 1, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*1 + 2, x_20);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_25 = l_Lean_Meta_SolveByElim_solveByElim(x_24, x_14, x_15, x_1, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_26);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec_ref(x_25);
x_34 = l_Lean_Meta_Rewrites_solveByElim___lam__2___closed__1;
x_35 = l_Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0___redArg(x_34, x_3, x_4, x_5, x_6, x_33);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
uint8_t x_40; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Rewrites_solveByElim___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Rewrites_rwLemma_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVarsCore(x_9, x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_st_ref_take(x_2, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
x_18 = lean_st_ref_set(x_2, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 2);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_st_ref_set(x_2, x_27, x_15);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Rewrites_rwLemma_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___Lean_Meta_Rewrites_rwLemma_spec__0___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Rewrites_rwLemma_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_13 = l_Lean_MVarId_assumption(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_23 = l_Lean_MVarId_assumption(x_21, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Rewrites_rwLemma_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 13);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Rewrites_rwLemma_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Rewrites_rwLemma_spec__2___redArg(x_1, x_4, x_6);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_Rewrites_solveByElim_spec__0_spec__0(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 4);
lean_inc_ref(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 4);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; double x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__0;
x_23 = 0;
x_24 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__1;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_23);
x_26 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__2;
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_27);
lean_ctor_set(x_12, 0, x_8);
x_28 = l_Lean_PersistentArray_push___redArg(x_21, x_12);
lean_ctor_set(x_14, 0, x_28);
x_29 = lean_st_ref_set(x_6, x_13, x_16);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint64_t x_36; lean_object* x_37; double x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
lean_dec(x_14);
x_38 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__0;
x_39 = 0;
x_40 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__1;
x_41 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_float(x_41, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_41, sizeof(void*)*2 + 8, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_39);
x_42 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__2;
x_43 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_10);
lean_ctor_set(x_43, 2, x_42);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_43);
lean_ctor_set(x_12, 0, x_8);
x_44 = l_Lean_PersistentArray_push___redArg(x_37, x_12);
x_45 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint64(x_45, sizeof(void*)*1, x_36);
lean_ctor_set(x_13, 4, x_45);
x_46 = lean_st_ref_set(x_6, x_13, x_16);
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
x_49 = lean_box(0);
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
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint64_t x_59; lean_object* x_60; lean_object* x_61; double x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
x_53 = lean_ctor_get(x_13, 2);
x_54 = lean_ctor_get(x_13, 3);
x_55 = lean_ctor_get(x_13, 5);
x_56 = lean_ctor_get(x_13, 6);
x_57 = lean_ctor_get(x_13, 7);
x_58 = lean_ctor_get(x_13, 8);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_59 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_60 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_60);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_61 = x_14;
} else {
 lean_dec_ref(x_14);
 x_61 = lean_box(0);
}
x_62 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__0;
x_63 = 0;
x_64 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__1;
x_65 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_float(x_65, sizeof(void*)*2, x_62);
lean_ctor_set_float(x_65, sizeof(void*)*2 + 8, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 16, x_63);
x_66 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__2;
x_67 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_10);
lean_ctor_set(x_67, 2, x_66);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_67);
lean_ctor_set(x_12, 0, x_8);
x_68 = l_Lean_PersistentArray_push___redArg(x_60, x_12);
if (lean_is_scalar(x_61)) {
 x_69 = lean_alloc_ctor(0, 1, 8);
} else {
 x_69 = x_61;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set_uint64(x_69, sizeof(void*)*1, x_59);
x_70 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_52);
lean_ctor_set(x_70, 2, x_53);
lean_ctor_set(x_70, 3, x_54);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set(x_70, 5, x_55);
lean_ctor_set(x_70, 6, x_56);
lean_ctor_set(x_70, 7, x_57);
lean_ctor_set(x_70, 8, x_58);
x_71 = lean_st_ref_set(x_6, x_70, x_16);
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
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; double x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_dec(x_12);
x_77 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_13, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_13, 3);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_13, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_13, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_13, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_13, 8);
lean_inc_ref(x_84);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 lean_ctor_release(x_13, 6);
 lean_ctor_release(x_13, 7);
 lean_ctor_release(x_13, 8);
 x_85 = x_13;
} else {
 lean_dec_ref(x_13);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_87 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_88 = x_14;
} else {
 lean_dec_ref(x_14);
 x_88 = lean_box(0);
}
x_89 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__0;
x_90 = 0;
x_91 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__1;
x_92 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_float(x_92, sizeof(void*)*2, x_89);
lean_ctor_set_float(x_92, sizeof(void*)*2 + 8, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*2 + 16, x_90);
x_93 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__2;
x_94 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_10);
lean_ctor_set(x_94, 2, x_93);
lean_inc(x_8);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_8);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_PersistentArray_push___redArg(x_87, x_95);
if (lean_is_scalar(x_88)) {
 x_97 = lean_alloc_ctor(0, 1, 8);
} else {
 x_97 = x_88;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set_uint64(x_97, sizeof(void*)*1, x_86);
if (lean_is_scalar(x_85)) {
 x_98 = lean_alloc_ctor(0, 9, 0);
} else {
 x_98 = x_85;
}
lean_ctor_set(x_98, 0, x_77);
lean_ctor_set(x_98, 1, x_78);
lean_ctor_set(x_98, 2, x_79);
lean_ctor_set(x_98, 3, x_80);
lean_ctor_set(x_98, 4, x_97);
lean_ctor_set(x_98, 5, x_81);
lean_ctor_set(x_98, 6, x_82);
lean_ctor_set(x_98, 7, x_83);
lean_ctor_set(x_98, 8, x_84);
x_99 = lean_st_ref_set(x_6, x_98, x_76);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
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
uint8_t x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 0;
x_2 = lean_box(0);
x_3 = 1;
x_4 = 2;
x_5 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("considering ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6() {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_87; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_119; lean_object* x_120; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_204; lean_object* x_205; 
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_6, 0);
lean_inc(x_216);
lean_dec_ref(x_6);
x_204 = x_216;
x_205 = x_11;
goto block_215;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_6, 0);
lean_inc(x_217);
lean_dec_ref(x_6);
x_218 = l_Lean_Meta_saveState___redArg(x_8, x_10, x_11);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec_ref(x_218);
lean_inc_ref(x_9);
x_221 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_217, x_7, x_8, x_9, x_10, x_220);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_219);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec_ref(x_221);
x_204 = x_222;
x_205 = x_223;
goto block_215;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; uint8_t x_241; 
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_241 = l_Lean_Exception_isInterrupt(x_224);
if (x_241 == 0)
{
uint8_t x_242; 
x_242 = l_Lean_Exception_isRuntime(x_224);
x_227 = x_242;
goto block_240;
}
else
{
x_227 = x_241;
goto block_240;
}
block_240:
{
if (x_227 == 0)
{
lean_object* x_228; 
lean_dec(x_226);
lean_dec(x_224);
x_228 = l_Lean_Meta_SavedState_restore___redArg(x_219, x_8, x_10, x_225);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_219);
if (lean_obj_tag(x_228) == 0)
{
uint8_t x_229; 
x_229 = !lean_is_exclusive(x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_228, 0);
lean_dec(x_230);
x_231 = lean_box(0);
lean_ctor_set(x_228, 0, x_231);
return x_228;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_228, 1);
lean_inc(x_232);
lean_dec(x_228);
x_233 = lean_box(0);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
else
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_228);
if (x_235 == 0)
{
return x_228;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_228, 0);
x_237 = lean_ctor_get(x_228, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_228);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
else
{
lean_object* x_239; 
lean_dec(x_219);
lean_dec(x_10);
lean_dec(x_8);
if (lean_is_scalar(x_226)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_226;
}
lean_ctor_set(x_239, 0, x_224);
lean_ctor_set(x_239, 1, x_225);
return x_239;
}
}
}
}
else
{
uint8_t x_243; 
lean_dec(x_217);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_243 = !lean_is_exclusive(x_218);
if (x_243 == 0)
{
return x_218;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_218, 0);
x_245 = lean_ctor_get(x_218, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_218);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
block_30:
{
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_14);
x_18 = l_Lean_Meta_SavedState_restore___redArg(x_12, x_15, x_13, x_16);
lean_dec(x_13);
lean_dec(x_15);
lean_dec_ref(x_12);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
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
uint8_t x_25; 
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
else
{
lean_object* x_29; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_16);
return x_29;
}
}
block_60:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_st_ref_get(x_34, x_31);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_43);
lean_dec(x_41);
lean_inc_ref(x_43);
x_44 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_43, x_32, x_35, x_34, x_33, x_37, x_42);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_1);
lean_ctor_set(x_47, 2, x_36);
lean_ctor_set(x_47, 3, x_43);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_39);
x_48 = lean_unbox(x_46);
lean_dec(x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*4 + 1, x_48);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_44, 0, x_49);
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_52 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_52, 0, x_38);
lean_ctor_set(x_52, 1, x_1);
lean_ctor_set(x_52, 2, x_36);
lean_ctor_set(x_52, 3, x_43);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_39);
x_53 = lean_unbox(x_50);
lean_dec(x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*4 + 1, x_53);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec_ref(x_43);
lean_dec_ref(x_38);
lean_dec_ref(x_36);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_44);
if (x_56 == 0)
{
return x_44;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_44, 0);
x_58 = lean_ctor_get(x_44, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_44);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
block_86:
{
lean_object* x_70; 
x_70 = l_Lean_Meta_Rewrites_rewriteResultLemma(x_64);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_61);
lean_dec(x_1);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
lean_dec_ref(x_70);
x_74 = l_Lean_instantiateMVars___at___Lean_Meta_Rewrites_rwLemma_spec__0___redArg(x_73, x_66, x_69);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__1;
x_78 = lean_unsigned_to_nat(4u);
x_79 = l_Lean_Expr_isAppOfArity(x_75, x_77, x_78);
if (x_79 == 0)
{
x_31 = x_76;
x_32 = x_61;
x_33 = x_67;
x_34 = x_66;
x_35 = x_65;
x_36 = x_64;
x_37 = x_68;
x_38 = x_75;
x_39 = x_63;
goto block_60;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_unsigned_to_nat(3u);
x_81 = l_Lean_Expr_getAppNumArgs(x_75);
x_82 = lean_nat_sub(x_81, x_80);
lean_dec(x_81);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_sub(x_82, x_83);
lean_dec(x_82);
x_85 = l_Lean_Expr_getRevArg_x21(x_75, x_84);
lean_dec(x_75);
x_31 = x_76;
x_32 = x_61;
x_33 = x_67;
x_34 = x_66;
x_35 = x_65;
x_36 = x_64;
x_37 = x_68;
x_38 = x_85;
x_39 = x_62;
goto block_60;
}
}
}
block_90:
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
block_104:
{
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec_ref(x_92);
x_97 = l_Lean_Meta_SavedState_restore___redArg(x_95, x_93, x_91, x_94);
lean_dec(x_91);
lean_dec(x_93);
lean_dec_ref(x_95);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec_ref(x_97);
x_87 = x_98;
goto block_90;
}
else
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_97);
if (x_99 == 0)
{
return x_97;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_97, 0);
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_97);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; 
lean_dec_ref(x_95);
lean_dec(x_93);
lean_dec(x_91);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_92);
lean_ctor_set(x_103, 1, x_94);
return x_103;
}
}
block_118:
{
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec_ref(x_105);
x_111 = l_Lean_Meta_SavedState_restore___redArg(x_107, x_108, x_106, x_109);
lean_dec(x_106);
lean_dec(x_108);
lean_dec_ref(x_107);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec_ref(x_111);
x_87 = x_112;
goto block_90;
}
else
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_111);
if (x_113 == 0)
{
return x_111;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_111, 0);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_111);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; 
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec(x_106);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_105);
lean_ctor_set(x_117, 1, x_109);
return x_117;
}
}
block_188:
{
lean_object* x_121; 
x_121 = l_Lean_Meta_saveState___redArg(x_8, x_10, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec_ref(x_121);
x_124 = 1;
x_125 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__2;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_119);
x_126 = l_Lean_MVarId_rewrite(x_2, x_3, x_119, x_4, x_125, x_7, x_8, x_9, x_10, x_123);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
lean_dec(x_122);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec_ref(x_126);
x_129 = lean_ctor_get(x_127, 0);
x_130 = lean_ctor_get(x_127, 2);
x_131 = l_List_isEmpty___redArg(x_130);
if (x_131 == 0)
{
lean_inc_ref(x_129);
lean_dec_ref(x_119);
switch (x_5) {
case 0:
{
if (x_131 == 0)
{
lean_dec_ref(x_129);
lean_dec(x_127);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_87 = x_128;
goto block_90;
}
else
{
x_61 = x_129;
x_62 = x_124;
x_63 = x_131;
x_64 = x_127;
x_65 = x_7;
x_66 = x_8;
x_67 = x_9;
x_68 = x_10;
x_69 = x_128;
goto block_86;
}
}
case 1:
{
lean_object* x_132; 
x_132 = l_Lean_Meta_saveState___redArg(x_8, x_10, x_128);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec_ref(x_132);
x_135 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_130);
x_136 = l_List_mapM_loop___at___Lean_Meta_Rewrites_rwLemma_spec__1(x_130, x_135, x_7, x_8, x_9, x_10, x_134);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
lean_dec(x_133);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec_ref(x_136);
x_61 = x_129;
x_62 = x_124;
x_63 = x_131;
x_64 = x_127;
x_65 = x_7;
x_66 = x_8;
x_67 = x_9;
x_68 = x_10;
x_69 = x_137;
goto block_86;
}
else
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
lean_dec_ref(x_129);
lean_dec(x_127);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec(x_1);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec_ref(x_136);
x_140 = l_Lean_Exception_isInterrupt(x_138);
if (x_140 == 0)
{
uint8_t x_141; 
x_141 = l_Lean_Exception_isRuntime(x_138);
x_105 = x_138;
x_106 = x_10;
x_107 = x_133;
x_108 = x_8;
x_109 = x_139;
x_110 = x_141;
goto block_118;
}
else
{
x_105 = x_138;
x_106 = x_10;
x_107 = x_133;
x_108 = x_8;
x_109 = x_139;
x_110 = x_140;
goto block_118;
}
}
}
else
{
uint8_t x_142; 
lean_dec_ref(x_129);
lean_dec(x_127);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_132);
if (x_142 == 0)
{
return x_132;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_132, 0);
x_144 = lean_ctor_get(x_132, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_132);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
default: 
{
lean_object* x_146; 
x_146 = l_Lean_Meta_saveState___redArg(x_8, x_10, x_128);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec_ref(x_146);
x_149 = lean_unsigned_to_nat(6u);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_130);
x_150 = l_Lean_Meta_Rewrites_solveByElim(x_130, x_149, x_7, x_8, x_9, x_10, x_148);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
lean_dec(x_147);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec_ref(x_150);
x_61 = x_129;
x_62 = x_124;
x_63 = x_131;
x_64 = x_127;
x_65 = x_7;
x_66 = x_8;
x_67 = x_9;
x_68 = x_10;
x_69 = x_151;
goto block_86;
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
lean_dec_ref(x_129);
lean_dec(x_127);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec(x_1);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec_ref(x_150);
x_154 = l_Lean_Exception_isInterrupt(x_152);
if (x_154 == 0)
{
uint8_t x_155; 
x_155 = l_Lean_Exception_isRuntime(x_152);
x_91 = x_10;
x_92 = x_152;
x_93 = x_8;
x_94 = x_153;
x_95 = x_147;
x_96 = x_155;
goto block_104;
}
else
{
x_91 = x_10;
x_92 = x_152;
x_93 = x_8;
x_94 = x_153;
x_95 = x_147;
x_96 = x_154;
goto block_104;
}
}
}
else
{
uint8_t x_156; 
lean_dec_ref(x_129);
lean_dec(x_127);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_146);
if (x_156 == 0)
{
return x_146;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_146, 0);
x_158 = lean_ctor_get(x_146, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_146);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_st_ref_get(x_8, x_128);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec_ref(x_160);
x_163 = lean_ctor_get(x_161, 0);
lean_inc_ref(x_163);
lean_dec(x_161);
lean_inc_ref(x_129);
lean_inc_ref(x_163);
x_164 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_163, x_129, x_7, x_8, x_9, x_10, x_162);
if (lean_obj_tag(x_164) == 0)
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_164, 0);
x_167 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_167, 0, x_119);
lean_ctor_set(x_167, 1, x_1);
lean_ctor_set(x_167, 2, x_127);
lean_ctor_set(x_167, 3, x_163);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_4);
x_168 = lean_unbox(x_166);
lean_dec(x_166);
lean_ctor_set_uint8(x_167, sizeof(void*)*4 + 1, x_168);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_164, 0, x_169);
return x_164;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; 
x_170 = lean_ctor_get(x_164, 0);
x_171 = lean_ctor_get(x_164, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_164);
x_172 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_172, 0, x_119);
lean_ctor_set(x_172, 1, x_1);
lean_ctor_set(x_172, 2, x_127);
lean_ctor_set(x_172, 3, x_163);
lean_ctor_set_uint8(x_172, sizeof(void*)*4, x_4);
x_173 = lean_unbox(x_170);
lean_dec(x_170);
lean_ctor_set_uint8(x_172, sizeof(void*)*4 + 1, x_173);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_172);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_171);
return x_175;
}
}
else
{
uint8_t x_176; 
lean_dec_ref(x_163);
lean_dec(x_127);
lean_dec_ref(x_119);
lean_dec(x_1);
x_176 = !lean_is_exclusive(x_164);
if (x_176 == 0)
{
return x_164;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_164, 0);
x_178 = lean_ctor_get(x_164, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_164);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_dec_ref(x_119);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec(x_1);
x_180 = lean_ctor_get(x_126, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_126, 1);
lean_inc(x_181);
lean_dec_ref(x_126);
x_182 = l_Lean_Exception_isInterrupt(x_180);
if (x_182 == 0)
{
uint8_t x_183; 
x_183 = l_Lean_Exception_isRuntime(x_180);
x_12 = x_122;
x_13 = x_10;
x_14 = x_180;
x_15 = x_8;
x_16 = x_181;
x_17 = x_183;
goto block_30;
}
else
{
x_12 = x_122;
x_13 = x_10;
x_14 = x_180;
x_15 = x_8;
x_16 = x_181;
x_17 = x_182;
goto block_30;
}
}
}
else
{
uint8_t x_184; 
lean_dec_ref(x_119);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_121);
if (x_184 == 0)
{
return x_121;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_121, 0);
x_186 = lean_ctor_get(x_121, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_121);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
block_203:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_194 = l_Lean_stringToMessageData(x_193);
lean_dec_ref(x_193);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_190);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3;
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
lean_inc_ref(x_191);
x_198 = l_Lean_MessageData_ofExpr(x_191);
x_199 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_196);
x_201 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3(x_189, x_200, x_7, x_8, x_9, x_10, x_192);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec_ref(x_201);
x_119 = x_191;
x_120 = x_202;
goto block_188;
}
block_215:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_206 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_;
x_207 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Rewrites_rwLemma_spec__2___redArg(x_206, x_9, x_205);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_unbox(x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
lean_dec_ref(x_207);
x_119 = x_204;
x_120 = x_210;
goto block_188;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_207, 1);
lean_inc(x_211);
lean_dec_ref(x_207);
x_212 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__5;
if (x_4 == 0)
{
lean_object* x_213; 
x_213 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__1;
x_189 = x_206;
x_190 = x_212;
x_191 = x_204;
x_192 = x_211;
x_193 = x_213;
goto block_203;
}
else
{
lean_object* x_214; 
x_214 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__6;
x_189 = x_206;
x_190 = x_212;
x_191 = x_204;
x_192 = x_211;
x_193 = x_214;
goto block_203;
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
x_16 = l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0___redArg(x_1, x_15, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Rewrites_rwLemma_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___Lean_Meta_Rewrites_rwLemma_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Rewrites_rwLemma_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___Lean_Meta_Rewrites_rwLemma_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Rewrites_rwLemma_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Rewrites_rwLemma_spec__2___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Rewrites_rwLemma_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Rewrites_rwLemma_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
x_13 = lean_unbox(x_5);
x_14 = l_Lean_Meta_Rewrites_rwLemma___lam__0(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
x_14 = lean_unbox(x_6);
x_15 = l_Lean_Meta_Rewrites_rwLemma(x_1, x_2, x_3, x_13, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_eq(x_3, x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_19 = lean_infer_type(x_18, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_1);
x_22 = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(x_1, x_20, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = l_Array_append___redArg(x_5, x_23);
lean_dec(x_23);
x_11 = x_25;
x_12 = x_24;
goto block_16;
}
else
{
lean_dec_ref(x_5);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec_ref(x_22);
x_11 = x_26;
x_12 = x_27;
goto block_16;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_22;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
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
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0), 8, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = 1;
x_12 = 0;
x_13 = lean_box(0);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), x_1, x_11, x_11, x_4, x_12, x_13, x_10, x_3, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_lambdaLetTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at_____private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport_spec__0___redArg___lam__0), 8, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = 0;
x_11 = lean_box(0);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___redArg(x_10, x_11, x_1, x_9, x_3, x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_forallTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_2);
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
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
x_11 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
lean_inc_ref(x_10);
x_16 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(x_1, x_10, x_15, x_4, x_5, x_6, x_7, x_13);
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
x_31 = lean_ptr_addr(x_14);
x_32 = lean_usize_dec_eq(x_30, x_31);
if (x_32 == 0)
{
x_27 = x_32;
goto block_29;
}
else
{
size_t x_33; size_t x_34; uint8_t x_35; 
x_33 = lean_ptr_addr(x_10);
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_2);
return x_16;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
case 6:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
x_38 = lean_ctor_get(x_2, 2);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_37);
lean_inc_ref(x_1);
x_40 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(x_1, x_37, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
lean_inc_ref(x_38);
x_45 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(x_1, x_38, x_44, x_4, x_5, x_6, x_7, x_42);
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
x_62 = lean_ptr_addr(x_43);
x_63 = lean_usize_dec_eq(x_61, x_62);
if (x_63 == 0)
{
x_56 = x_63;
goto block_60;
}
else
{
size_t x_64; size_t x_65; uint8_t x_66; 
x_64 = lean_ptr_addr(x_38);
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
lean_inc(x_36);
lean_dec_ref(x_2);
x_57 = l_Lean_Expr_lam___override(x_36, x_43, x_49, x_39);
x_52 = x_57;
goto block_55;
}
else
{
uint8_t x_58; 
x_58 = l_Lean_beqBinderInfo____x40_Lean_Expr_2616605480____hygCtx___hyg_9_(x_39, x_39);
if (x_58 == 0)
{
lean_object* x_59; 
lean_inc(x_36);
lean_dec_ref(x_2);
x_59 = l_Lean_Expr_lam___override(x_36, x_43, x_49, x_39);
x_52 = x_59;
goto block_55;
}
else
{
lean_dec(x_49);
lean_dec(x_43);
x_52 = x_2;
goto block_55;
}
}
}
}
else
{
lean_dec(x_43);
lean_dec_ref(x_2);
return x_45;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_40;
}
}
case 7:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_2, 0);
x_68 = lean_ctor_get(x_2, 1);
x_69 = lean_ctor_get(x_2, 2);
x_70 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_68);
lean_inc_ref(x_1);
x_71 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(x_1, x_68, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
lean_inc_ref(x_69);
x_76 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(x_1, x_69, x_75, x_4, x_5, x_6, x_7, x_73);
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
x_93 = lean_ptr_addr(x_74);
x_94 = lean_usize_dec_eq(x_92, x_93);
if (x_94 == 0)
{
x_87 = x_94;
goto block_91;
}
else
{
size_t x_95; size_t x_96; uint8_t x_97; 
x_95 = lean_ptr_addr(x_69);
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
lean_inc(x_67);
lean_dec_ref(x_2);
x_88 = l_Lean_Expr_forallE___override(x_67, x_74, x_80, x_70);
x_83 = x_88;
goto block_86;
}
else
{
uint8_t x_89; 
x_89 = l_Lean_beqBinderInfo____x40_Lean_Expr_2616605480____hygCtx___hyg_9_(x_70, x_70);
if (x_89 == 0)
{
lean_object* x_90; 
lean_inc(x_67);
lean_dec_ref(x_2);
x_90 = l_Lean_Expr_forallE___override(x_67, x_74, x_80, x_70);
x_83 = x_90;
goto block_86;
}
else
{
lean_dec(x_80);
lean_dec(x_74);
x_83 = x_2;
goto block_86;
}
}
}
}
else
{
lean_dec(x_74);
lean_dec_ref(x_2);
return x_76;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_71;
}
}
case 8:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_2, 0);
x_99 = lean_ctor_get(x_2, 1);
x_100 = lean_ctor_get(x_2, 2);
x_101 = lean_ctor_get(x_2, 3);
x_102 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_99);
lean_inc_ref(x_1);
x_103 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(x_1, x_99, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec_ref(x_103);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_100);
lean_inc_ref(x_1);
x_108 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(x_1, x_100, x_107, x_4, x_5, x_6, x_7, x_105);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec_ref(x_108);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
lean_inc_ref(x_101);
x_113 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(x_1, x_101, x_112, x_4, x_5, x_6, x_7, x_110);
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
x_132 = lean_ptr_addr(x_106);
x_133 = lean_usize_dec_eq(x_131, x_132);
if (x_133 == 0)
{
x_124 = x_133;
goto block_130;
}
else
{
size_t x_134; size_t x_135; uint8_t x_136; 
x_134 = lean_ptr_addr(x_100);
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
lean_inc(x_98);
lean_dec_ref(x_2);
x_125 = l_Lean_Expr_letE___override(x_98, x_106, x_111, x_117, x_102);
x_120 = x_125;
goto block_123;
}
else
{
size_t x_126; size_t x_127; uint8_t x_128; 
x_126 = lean_ptr_addr(x_101);
x_127 = lean_ptr_addr(x_117);
x_128 = lean_usize_dec_eq(x_126, x_127);
if (x_128 == 0)
{
lean_object* x_129; 
lean_inc(x_98);
lean_dec_ref(x_2);
x_129 = l_Lean_Expr_letE___override(x_98, x_106, x_111, x_117, x_102);
x_120 = x_129;
goto block_123;
}
else
{
lean_dec(x_117);
lean_dec(x_111);
lean_dec(x_106);
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
lean_dec_ref(x_2);
return x_113;
}
}
else
{
lean_dec(x_106);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_108;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_103;
}
}
case 10:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_2, 0);
x_138 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_138);
x_139 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(x_1, x_138, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_151 = lean_ptr_addr(x_143);
x_152 = lean_usize_dec_eq(x_150, x_151);
if (x_152 == 0)
{
lean_object* x_153; 
lean_inc(x_137);
lean_dec_ref(x_2);
x_153 = l_Lean_Expr_mdata___override(x_137, x_143);
x_146 = x_153;
goto block_149;
}
else
{
lean_dec(x_143);
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
lean_dec_ref(x_2);
return x_139;
}
}
case 11:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_2, 0);
x_155 = lean_ctor_get(x_2, 1);
x_156 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_156);
x_157 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg___lam__0(x_1, x_156, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_169 = lean_ptr_addr(x_161);
x_170 = lean_usize_dec_eq(x_168, x_169);
if (x_170 == 0)
{
lean_object* x_171; 
lean_inc(x_155);
lean_inc(x_154);
lean_dec_ref(x_2);
x_171 = l_Lean_Expr_proj___override(x_154, x_155, x_161);
x_164 = x_171;
goto block_167;
}
else
{
lean_dec(x_161);
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
lean_dec_ref(x_2);
return x_157;
}
}
default: 
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_traverseChildren___at___Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3_spec__3___redArg(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
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
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(x_1, x_2, x_18, x_19, x_13, x_4, x_5, x_6, x_7, x_12);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
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
x_32 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(x_1, x_2, x_30, x_31, x_23, x_4, x_5, x_6, x_7, x_22);
return x_32;
}
}
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___closed__0;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
case 6:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = 0;
x_12 = 1;
x_13 = l_Lean_Meta_lambdaLetTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(x_2, x_10, x_11, x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
case 7:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = 0;
x_16 = l_Lean_Meta_forallTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(x_2, x_14, x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
case 8:
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_17, 0, x_1);
x_18 = 0;
x_19 = 1;
x_20 = l_Lean_Meta_lambdaLetTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(x_2, x_17, x_18, x_19, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
default: 
{
lean_object* x_21; 
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_21 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__3), 8, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = l_Array_reverse___redArg(x_22);
x_26 = l_Lean_Expr_foldlM___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__3___redArg(x_24, x_25, x_2, x_3, x_4, x_5, x_6, x_23);
return x_26;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_21;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___redArg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__0(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Meta_lambdaLetTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_lambdaLetTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__1(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_forallTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_forallTelescope___at___Lean_Meta_Rewrites_getSubexpressionMatches_spec__2(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at_____private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_array_fget_borrowed(x_1, x_2);
x_6 = lean_ctor_get(x_5, 1);
x_7 = lean_ctor_get(x_6, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
x_10 = lean_array_fget_borrowed(x_1, x_9);
x_11 = lean_ctor_get(x_10, 1);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_nat_dec_lt(x_12, x_7);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at_____private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at_____private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at_____private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0_spec__0___redArg(x_1, x_2);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
x_26 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(x_18, x_1);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = lean_unbox(x_19);
lean_dec(x_19);
if (x_27 == 0)
{
uint8_t x_28; uint8_t x_29; 
x_28 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(x_18, x_25);
x_29 = l_instDecidableNot___redArg(x_28);
if (x_29 == 0)
{
lean_dec(x_18);
lean_dec_ref(x_15);
x_7 = x_5;
x_8 = x_6;
goto block_12;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_push(x_24, x_15);
x_31 = l_Lean_NameSet_insert(x_25, x_18);
lean_ctor_set(x_17, 1, x_31);
lean_ctor_set(x_17, 0, x_30);
x_7 = x_5;
x_8 = x_6;
goto block_12;
}
}
else
{
uint8_t x_32; uint8_t x_33; 
x_32 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(x_18, x_21);
x_33 = l_instDecidableNot___redArg(x_32);
if (x_33 == 0)
{
lean_dec(x_18);
lean_dec_ref(x_15);
x_7 = x_5;
x_8 = x_6;
goto block_12;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_array_push(x_24, x_15);
x_35 = l_Lean_NameSet_insert(x_21, x_18);
lean_ctor_set(x_17, 0, x_34);
lean_ctor_set(x_5, 0, x_35);
x_7 = x_5;
x_8 = x_6;
goto block_12;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_15);
x_7 = x_5;
x_8 = x_6;
goto block_12;
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
x_38 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(x_18, x_1);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = lean_unbox(x_19);
lean_dec(x_19);
if (x_39 == 0)
{
uint8_t x_40; uint8_t x_41; 
x_40 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(x_18, x_37);
x_41 = l_instDecidableNot___redArg(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_18);
lean_dec_ref(x_15);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_37);
lean_ctor_set(x_5, 1, x_42);
x_7 = x_5;
x_8 = x_6;
goto block_12;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_array_push(x_36, x_15);
x_44 = l_Lean_NameSet_insert(x_37, x_18);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_5, 1, x_45);
x_7 = x_5;
x_8 = x_6;
goto block_12;
}
}
else
{
uint8_t x_46; uint8_t x_47; 
x_46 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(x_18, x_21);
x_47 = l_instDecidableNot___redArg(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_18);
lean_dec_ref(x_15);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_37);
lean_ctor_set(x_5, 1, x_48);
x_7 = x_5;
x_8 = x_6;
goto block_12;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_array_push(x_36, x_15);
x_50 = l_Lean_NameSet_insert(x_21, x_18);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_37);
lean_ctor_set(x_5, 1, x_51);
lean_ctor_set(x_5, 0, x_50);
x_7 = x_5;
x_8 = x_6;
goto block_12;
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_15);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_36);
lean_ctor_set(x_52, 1, x_37);
lean_ctor_set(x_5, 1, x_52);
x_7 = x_5;
x_8 = x_6;
goto block_12;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_5, 0);
lean_inc(x_53);
lean_dec(x_5);
x_54 = lean_ctor_get(x_17, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_17, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_56 = x_17;
} else {
 lean_dec_ref(x_17);
 x_56 = lean_box(0);
}
x_57 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(x_18, x_1);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = lean_unbox(x_19);
lean_dec(x_19);
if (x_58 == 0)
{
uint8_t x_59; uint8_t x_60; 
x_59 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(x_18, x_55);
x_60 = l_instDecidableNot___redArg(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_18);
lean_dec_ref(x_15);
if (lean_is_scalar(x_56)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_56;
}
lean_ctor_set(x_61, 0, x_54);
lean_ctor_set(x_61, 1, x_55);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_61);
x_7 = x_62;
x_8 = x_6;
goto block_12;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_array_push(x_54, x_15);
x_64 = l_Lean_NameSet_insert(x_55, x_18);
if (lean_is_scalar(x_56)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_56;
}
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_53);
lean_ctor_set(x_66, 1, x_65);
x_7 = x_66;
x_8 = x_6;
goto block_12;
}
}
else
{
uint8_t x_67; uint8_t x_68; 
x_67 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_NameMap_contains_spec__0___redArg(x_18, x_53);
x_68 = l_instDecidableNot___redArg(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_18);
lean_dec_ref(x_15);
if (lean_is_scalar(x_56)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_56;
}
lean_ctor_set(x_69, 0, x_54);
lean_ctor_set(x_69, 1, x_55);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_69);
x_7 = x_70;
x_8 = x_6;
goto block_12;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_array_push(x_54, x_15);
x_72 = l_Lean_NameSet_insert(x_53, x_18);
if (lean_is_scalar(x_56)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_56;
}
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_55);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_7 = x_74;
x_8 = x_6;
goto block_12;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_15);
if (lean_is_scalar(x_56)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_56;
}
lean_ctor_set(x_75, 0, x_54);
lean_ctor_set(x_75, 1, x_55);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_53);
lean_ctor_set(x_76, 1, x_75);
x_7 = x_76;
x_8 = x_6;
goto block_12;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_unsigned_to_nat(0u);
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
x_17 = lean_unsigned_to_nat(0u);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_unsigned_to_nat(0u);
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
x_17 = lean_unsigned_to_nat(0u);
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
x_1 = lean_box(1);
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
x_2 = lean_box(1);
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
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_11 = l_Lean_Meta_Rewrites_getSubexpressionMatches___redArg(x_10, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_12);
x_16 = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___Lean_Meta_Rewrites_rewriteCandidates_spec__0(x_12, x_14, x_15);
x_17 = l_Lean_Meta_Rewrites_rewriteCandidates___closed__2;
x_18 = lean_array_size(x_16);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___redArg(x_4, x_16, x_18, x_19, x_17, x_13);
lean_dec_ref(x_16);
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
x_36 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
x_37 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Rewrites_rwLemma_spec__2___redArg(x_36, x_7, x_23);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_free_object(x_22);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec_ref(x_37);
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
x_49 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_49);
lean_ctor_set(x_22, 0, x_37);
x_50 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3(x_36, x_22, x_5, x_6, x_7, x_8, x_42);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec_ref(x_50);
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
x_59 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_59);
lean_ctor_set(x_22, 0, x_58);
x_60 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3(x_36, x_22, x_5, x_6, x_7, x_8, x_52);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec_ref(x_60);
x_28 = x_61;
goto block_35;
}
}
block_35:
{
size_t x_29; lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_array_size(x_1);
x_30 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__3(x_29, x_19, x_1);
x_31 = lean_array_size(x_26);
x_32 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__4(x_31, x_19, x_26);
x_33 = l_Array_append___redArg(x_30, x_32);
lean_dec_ref(x_32);
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
x_71 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_;
x_72 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Rewrites_rwLemma_spec__2___redArg(x_71, x_7, x_23);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec_ref(x_72);
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
x_84 = l_Lean_Meta_Rewrites_rwLemma___lam__0___closed__3;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3(x_71, x_85, x_5, x_6, x_7, x_8, x_76);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec_ref(x_86);
x_63 = x_87;
goto block_70;
}
block_70:
{
size_t x_64; lean_object* x_65; size_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_array_size(x_1);
x_65 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__3(x_64, x_19, x_1);
x_66 = lean_array_size(x_62);
x_67 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__4(x_66, x_19, x_62);
x_68 = l_Array_append___redArg(x_65, x_67);
lean_dec_ref(x_67);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___redArg(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lean_Meta_Rewrites_rewriteCandidates_spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lean_Meta_Rewrites_rewriteCandidates_spec__4(x_4, x_5, x_3);
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
lean_inc_ref(x_4);
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
lean_dec_ref(x_1);
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
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), x_1, x_12, x_7, x_8, x_9, x_10, x_11);
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
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_saveState___redArg(x_7, x_9, x_11, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_12, 5);
x_19 = lean_box(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_Rewrites_RewriteResult_newGoal(x_3);
x_24 = l_Option_toLOption___redArg(x_23);
x_25 = lean_box(0);
lean_inc(x_18);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_18);
if (lean_obj_tag(x_5) == 0)
{
x_27 = x_16;
goto block_30;
}
else
{
lean_object* x_31; 
lean_dec(x_16);
x_31 = lean_ctor_get(x_5, 0);
lean_inc(x_31);
lean_dec_ref(x_5);
x_27 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(x_4, x_22, x_24, x_25, x_26, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
return x_29;
}
}
else
{
uint8_t x_32; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_15 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_15);
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
x_16 = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lam__0(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResultConfig_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResultConfig_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Rewrites_RewriteResultConfig_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_string_dec_eq(x_4, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_string_hash(x_2);
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
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_string_hash(x_4);
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
x_26 = lean_string_hash(x_22);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2_spec__2_spec__2___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2___redArg(lean_object* x_1) {
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
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_string_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__5___redArg(x_1, x_2, x_7);
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
x_13 = lean_string_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__5___redArg(x_1, x_2, x_12);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_string_hash(x_2);
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
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_2, x_20);
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
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2___redArg(x_25);
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
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__5___redArg(x_2, x_3, x_20);
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
x_40 = lean_string_hash(x_2);
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
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_2, x_52);
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
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__2___redArg(x_57);
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
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2_spec__5___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec_ref(x_3);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l_Lean_getRemainingHeartbeats___redArg(x_7, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_4, 1);
x_20 = lean_ctor_get(x_4, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_ctor_get(x_1, 3);
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_33 = lean_ctor_get(x_1, 4);
x_34 = lean_nat_dec_lt(x_23, x_29);
lean_dec(x_23);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_array_get_size(x_25);
x_36 = lean_nat_dec_le(x_28, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_17);
x_37 = lean_box(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_33);
x_38 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(x_38, 0, x_33);
lean_closure_set(x_38, 1, x_30);
lean_closure_set(x_38, 2, x_31);
lean_closure_set(x_38, 3, x_37);
lean_closure_set(x_38, 4, x_14);
lean_closure_set(x_38, 5, x_15);
lean_closure_set(x_38, 6, x_16);
lean_inc_ref(x_33);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_39, 0, lean_box(0));
lean_closure_set(x_39, 1, x_33);
lean_closure_set(x_39, 2, x_38);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_40 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_39, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
lean_inc(x_2);
lean_ctor_set(x_4, 0, x_2);
x_3 = x_13;
x_9 = x_42;
goto _start;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec_ref(x_40);
x_47 = lean_ctor_get(x_45, 2);
x_48 = lean_ctor_get(x_45, 3);
lean_inc(x_45);
x_49 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_49, 0, x_45);
lean_inc_ref(x_48);
x_50 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_50, 0, lean_box(0));
lean_closure_set(x_50, 1, x_48);
lean_closure_set(x_50, 2, x_49);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_51 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_50, x_5, x_6, x_7, x_8, x_46);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(x_26, x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_55);
lean_inc_ref(x_48);
x_56 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_48, x_55, x_5, x_6, x_7, x_8, x_53);
if (lean_obj_tag(x_56) == 0)
{
if (x_27 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_free_object(x_41);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_box(0);
x_59 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_26, x_52, x_58);
x_60 = lean_array_push(x_25, x_45);
lean_ctor_set(x_19, 1, x_59);
lean_ctor_set(x_19, 0, x_60);
lean_inc(x_2);
lean_ctor_set(x_4, 0, x_2);
x_3 = x_13;
x_9 = x_57;
goto _start;
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_41);
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
lean_dec_ref(x_56);
x_65 = lean_box(0);
x_66 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_26, x_52, x_65);
x_67 = lean_array_push(x_25, x_45);
lean_ctor_set(x_19, 1, x_66);
lean_ctor_set(x_19, 0, x_67);
lean_inc(x_2);
lean_ctor_set(x_4, 0, x_2);
x_3 = x_13;
x_9 = x_64;
goto _start;
}
else
{
uint8_t x_69; 
lean_dec(x_52);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_69 = !lean_is_exclusive(x_56);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_56, 0);
lean_dec(x_70);
x_71 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0;
x_72 = lean_array_push(x_71, x_45);
lean_ctor_set(x_41, 0, x_72);
lean_ctor_set(x_4, 0, x_41);
lean_ctor_set(x_56, 0, x_4);
return x_56;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_56, 1);
lean_inc(x_73);
lean_dec(x_56);
x_74 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0;
x_75 = lean_array_push(x_74, x_45);
lean_ctor_set(x_41, 0, x_75);
lean_ctor_set(x_4, 0, x_41);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_4);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_52);
lean_free_object(x_41);
lean_dec(x_45);
lean_free_object(x_19);
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_77 = !lean_is_exclusive(x_56);
if (x_77 == 0)
{
return x_56;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_56, 0);
x_79 = lean_ctor_get(x_56, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_56);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_dec(x_52);
lean_free_object(x_41);
lean_dec(x_45);
lean_inc(x_2);
lean_ctor_set(x_4, 0, x_2);
x_3 = x_13;
x_9 = x_53;
goto _start;
}
}
else
{
uint8_t x_82; 
lean_free_object(x_41);
lean_dec(x_45);
lean_free_object(x_19);
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_82 = !lean_is_exclusive(x_51);
if (x_82 == 0)
{
return x_51;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_51, 0);
x_84 = lean_ctor_get(x_51, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_51);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_41, 0);
lean_inc(x_86);
lean_dec(x_41);
x_87 = lean_ctor_get(x_40, 1);
lean_inc(x_87);
lean_dec_ref(x_40);
x_88 = lean_ctor_get(x_86, 2);
x_89 = lean_ctor_get(x_86, 3);
lean_inc(x_86);
x_90 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_90, 0, x_86);
lean_inc_ref(x_89);
x_91 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_91, 0, lean_box(0));
lean_closure_set(x_91, 1, x_89);
lean_closure_set(x_91, 2, x_90);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_92 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_91, x_5, x_6, x_7, x_8, x_87);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec_ref(x_92);
x_95 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(x_26, x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_88, 0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_96);
lean_inc_ref(x_89);
x_97 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_89, x_96, x_5, x_6, x_7, x_8, x_94);
if (lean_obj_tag(x_97) == 0)
{
if (x_27 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = lean_box(0);
x_100 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_26, x_93, x_99);
x_101 = lean_array_push(x_25, x_86);
lean_ctor_set(x_19, 1, x_100);
lean_ctor_set(x_19, 0, x_101);
lean_inc(x_2);
lean_ctor_set(x_4, 0, x_2);
x_3 = x_13;
x_9 = x_98;
goto _start;
}
else
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
x_104 = lean_unbox(x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_97, 1);
lean_inc(x_105);
lean_dec_ref(x_97);
x_106 = lean_box(0);
x_107 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_26, x_93, x_106);
x_108 = lean_array_push(x_25, x_86);
lean_ctor_set(x_19, 1, x_107);
lean_ctor_set(x_19, 0, x_108);
lean_inc(x_2);
lean_ctor_set(x_4, 0, x_2);
x_3 = x_13;
x_9 = x_105;
goto _start;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_93);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_110 = lean_ctor_get(x_97, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_111 = x_97;
} else {
 lean_dec_ref(x_97);
 x_111 = lean_box(0);
}
x_112 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0;
x_113 = lean_array_push(x_112, x_86);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_4, 0, x_114);
if (lean_is_scalar(x_111)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_111;
}
lean_ctor_set(x_115, 0, x_4);
lean_ctor_set(x_115, 1, x_110);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_93);
lean_dec(x_86);
lean_free_object(x_19);
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_116 = lean_ctor_get(x_97, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_97, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_118 = x_97;
} else {
 lean_dec_ref(x_97);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_dec(x_93);
lean_dec(x_86);
lean_inc(x_2);
lean_ctor_set(x_4, 0, x_2);
x_3 = x_13;
x_9 = x_94;
goto _start;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_86);
lean_free_object(x_19);
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_121 = lean_ctor_get(x_92, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_92, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_123 = x_92;
} else {
 lean_dec_ref(x_92);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_free_object(x_19);
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_125 = !lean_is_exclusive(x_40);
if (x_125 == 0)
{
return x_40;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_40, 0);
x_127 = lean_ctor_get(x_40, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_40);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_25);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_25);
lean_ctor_set(x_4, 0, x_129);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
}
else
{
lean_object* x_130; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_25);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_25);
lean_ctor_set(x_4, 0, x_130);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; uint8_t x_142; 
x_131 = lean_ctor_get(x_17, 0);
x_132 = lean_ctor_get(x_17, 1);
x_133 = lean_ctor_get(x_19, 0);
x_134 = lean_ctor_get(x_19, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_19);
x_135 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_136 = lean_ctor_get(x_1, 0);
x_137 = lean_ctor_get(x_1, 1);
x_138 = lean_ctor_get(x_1, 2);
x_139 = lean_ctor_get(x_1, 3);
x_140 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_141 = lean_ctor_get(x_1, 4);
x_142 = lean_nat_dec_lt(x_131, x_137);
lean_dec(x_131);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_array_get_size(x_133);
x_144 = lean_nat_dec_le(x_136, x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_free_object(x_17);
x_145 = lean_box(x_140);
lean_inc_ref(x_139);
lean_inc(x_138);
lean_inc_ref(x_141);
x_146 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(x_146, 0, x_141);
lean_closure_set(x_146, 1, x_138);
lean_closure_set(x_146, 2, x_139);
lean_closure_set(x_146, 3, x_145);
lean_closure_set(x_146, 4, x_14);
lean_closure_set(x_146, 5, x_15);
lean_closure_set(x_146, 6, x_16);
lean_inc_ref(x_141);
x_147 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_147, 0, lean_box(0));
lean_closure_set(x_147, 1, x_141);
lean_closure_set(x_147, 2, x_146);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_148 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_147, x_5, x_6, x_7, x_8, x_132);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec_ref(x_148);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_133);
lean_ctor_set(x_151, 1, x_134);
lean_inc(x_2);
lean_ctor_set(x_4, 1, x_151);
lean_ctor_set(x_4, 0, x_2);
x_3 = x_13;
x_9 = x_150;
goto _start;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_153 = lean_ctor_get(x_149, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_154 = x_149;
} else {
 lean_dec_ref(x_149);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_148, 1);
lean_inc(x_155);
lean_dec_ref(x_148);
x_156 = lean_ctor_get(x_153, 2);
x_157 = lean_ctor_get(x_153, 3);
lean_inc(x_153);
x_158 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_158, 0, x_153);
lean_inc_ref(x_157);
x_159 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_159, 0, lean_box(0));
lean_closure_set(x_159, 1, x_157);
lean_closure_set(x_159, 2, x_158);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_160 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_159, x_5, x_6, x_7, x_8, x_155);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec_ref(x_160);
x_163 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(x_134, x_161);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_156, 0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_164);
lean_inc_ref(x_157);
x_165 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_157, x_164, x_5, x_6, x_7, x_8, x_162);
if (lean_obj_tag(x_165) == 0)
{
if (x_135 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_154);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec_ref(x_165);
x_167 = lean_box(0);
x_168 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_134, x_161, x_167);
x_169 = lean_array_push(x_133, x_153);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
lean_inc(x_2);
lean_ctor_set(x_4, 1, x_170);
lean_ctor_set(x_4, 0, x_2);
x_3 = x_13;
x_9 = x_166;
goto _start;
}
else
{
lean_object* x_172; uint8_t x_173; 
x_172 = lean_ctor_get(x_165, 0);
lean_inc(x_172);
x_173 = lean_unbox(x_172);
lean_dec(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_154);
x_174 = lean_ctor_get(x_165, 1);
lean_inc(x_174);
lean_dec_ref(x_165);
x_175 = lean_box(0);
x_176 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_134, x_161, x_175);
x_177 = lean_array_push(x_133, x_153);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
lean_inc(x_2);
lean_ctor_set(x_4, 1, x_178);
lean_ctor_set(x_4, 0, x_2);
x_3 = x_13;
x_9 = x_174;
goto _start;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_161);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_180 = lean_ctor_get(x_165, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_181 = x_165;
} else {
 lean_dec_ref(x_165);
 x_181 = lean_box(0);
}
x_182 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0;
x_183 = lean_array_push(x_182, x_153);
if (lean_is_scalar(x_154)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_154;
}
lean_ctor_set(x_184, 0, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_133);
lean_ctor_set(x_185, 1, x_134);
lean_ctor_set(x_4, 1, x_185);
lean_ctor_set(x_4, 0, x_184);
if (lean_is_scalar(x_181)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_181;
}
lean_ctor_set(x_186, 0, x_4);
lean_ctor_set(x_186, 1, x_180);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_161);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_134);
lean_dec(x_133);
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_187 = lean_ctor_get(x_165, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_165, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_189 = x_165;
} else {
 lean_dec_ref(x_165);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
else
{
lean_object* x_191; 
lean_dec(x_161);
lean_dec(x_154);
lean_dec(x_153);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_133);
lean_ctor_set(x_191, 1, x_134);
lean_inc(x_2);
lean_ctor_set(x_4, 1, x_191);
lean_ctor_set(x_4, 0, x_2);
x_3 = x_13;
x_9 = x_162;
goto _start;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_134);
lean_dec(x_133);
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_193 = lean_ctor_get(x_160, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_160, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_195 = x_160;
} else {
 lean_dec_ref(x_160);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_134);
lean_dec(x_133);
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_197 = lean_ctor_get(x_148, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_148, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_199 = x_148;
} else {
 lean_dec_ref(x_148);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_133);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_133);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_133);
lean_ctor_set(x_202, 1, x_134);
lean_ctor_set(x_4, 1, x_202);
lean_ctor_set(x_4, 0, x_201);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_133);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_133);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_133);
lean_ctor_set(x_204, 1, x_134);
lean_ctor_set(x_4, 1, x_204);
lean_ctor_set(x_4, 0, x_203);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; uint8_t x_217; 
x_205 = lean_ctor_get(x_17, 0);
x_206 = lean_ctor_get(x_17, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_17);
x_207 = lean_ctor_get(x_19, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_19, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_209 = x_19;
} else {
 lean_dec_ref(x_19);
 x_209 = lean_box(0);
}
x_210 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_211 = lean_ctor_get(x_1, 0);
x_212 = lean_ctor_get(x_1, 1);
x_213 = lean_ctor_get(x_1, 2);
x_214 = lean_ctor_get(x_1, 3);
x_215 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_216 = lean_ctor_get(x_1, 4);
x_217 = lean_nat_dec_lt(x_205, x_212);
lean_dec(x_205);
if (x_217 == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_array_get_size(x_207);
x_219 = lean_nat_dec_le(x_211, x_218);
lean_dec(x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_box(x_215);
lean_inc_ref(x_214);
lean_inc(x_213);
lean_inc_ref(x_216);
x_221 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(x_221, 0, x_216);
lean_closure_set(x_221, 1, x_213);
lean_closure_set(x_221, 2, x_214);
lean_closure_set(x_221, 3, x_220);
lean_closure_set(x_221, 4, x_14);
lean_closure_set(x_221, 5, x_15);
lean_closure_set(x_221, 6, x_16);
lean_inc_ref(x_216);
x_222 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_222, 0, lean_box(0));
lean_closure_set(x_222, 1, x_216);
lean_closure_set(x_222, 2, x_221);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_223 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_222, x_5, x_6, x_7, x_8, x_206);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec_ref(x_223);
if (lean_is_scalar(x_209)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_209;
}
lean_ctor_set(x_226, 0, x_207);
lean_ctor_set(x_226, 1, x_208);
lean_inc(x_2);
lean_ctor_set(x_4, 1, x_226);
lean_ctor_set(x_4, 0, x_2);
x_3 = x_13;
x_9 = x_225;
goto _start;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_228 = lean_ctor_get(x_224, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 x_229 = x_224;
} else {
 lean_dec_ref(x_224);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_223, 1);
lean_inc(x_230);
lean_dec_ref(x_223);
x_231 = lean_ctor_get(x_228, 2);
x_232 = lean_ctor_get(x_228, 3);
lean_inc(x_228);
x_233 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_233, 0, x_228);
lean_inc_ref(x_232);
x_234 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_234, 0, lean_box(0));
lean_closure_set(x_234, 1, x_232);
lean_closure_set(x_234, 2, x_233);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_235 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_234, x_5, x_6, x_7, x_8, x_230);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec_ref(x_235);
x_238 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(x_208, x_236);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_231, 0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_239);
lean_inc_ref(x_232);
x_240 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_232, x_239, x_5, x_6, x_7, x_8, x_237);
if (lean_obj_tag(x_240) == 0)
{
if (x_210 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_229);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec_ref(x_240);
x_242 = lean_box(0);
x_243 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_208, x_236, x_242);
x_244 = lean_array_push(x_207, x_228);
if (lean_is_scalar(x_209)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_209;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_243);
lean_inc(x_2);
lean_ctor_set(x_4, 1, x_245);
lean_ctor_set(x_4, 0, x_2);
x_3 = x_13;
x_9 = x_241;
goto _start;
}
else
{
lean_object* x_247; uint8_t x_248; 
x_247 = lean_ctor_get(x_240, 0);
lean_inc(x_247);
x_248 = lean_unbox(x_247);
lean_dec(x_247);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_229);
x_249 = lean_ctor_get(x_240, 1);
lean_inc(x_249);
lean_dec_ref(x_240);
x_250 = lean_box(0);
x_251 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_208, x_236, x_250);
x_252 = lean_array_push(x_207, x_228);
if (lean_is_scalar(x_209)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_209;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_251);
lean_inc(x_2);
lean_ctor_set(x_4, 1, x_253);
lean_ctor_set(x_4, 0, x_2);
x_3 = x_13;
x_9 = x_249;
goto _start;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_236);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_255 = lean_ctor_get(x_240, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_256 = x_240;
} else {
 lean_dec_ref(x_240);
 x_256 = lean_box(0);
}
x_257 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0;
x_258 = lean_array_push(x_257, x_228);
if (lean_is_scalar(x_229)) {
 x_259 = lean_alloc_ctor(1, 1, 0);
} else {
 x_259 = x_229;
}
lean_ctor_set(x_259, 0, x_258);
if (lean_is_scalar(x_209)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_209;
}
lean_ctor_set(x_260, 0, x_207);
lean_ctor_set(x_260, 1, x_208);
lean_ctor_set(x_4, 1, x_260);
lean_ctor_set(x_4, 0, x_259);
if (lean_is_scalar(x_256)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_256;
}
lean_ctor_set(x_261, 0, x_4);
lean_ctor_set(x_261, 1, x_255);
return x_261;
}
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_236);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_262 = lean_ctor_get(x_240, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_240, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_264 = x_240;
} else {
 lean_dec_ref(x_240);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
else
{
lean_object* x_266; 
lean_dec(x_236);
lean_dec(x_229);
lean_dec(x_228);
if (lean_is_scalar(x_209)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_209;
}
lean_ctor_set(x_266, 0, x_207);
lean_ctor_set(x_266, 1, x_208);
lean_inc(x_2);
lean_ctor_set(x_4, 1, x_266);
lean_ctor_set(x_4, 0, x_2);
x_3 = x_13;
x_9 = x_237;
goto _start;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_268 = lean_ctor_get(x_235, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_235, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_270 = x_235;
} else {
 lean_dec_ref(x_235);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_272 = lean_ctor_get(x_223, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_223, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_274 = x_223;
} else {
 lean_dec_ref(x_223);
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
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_207);
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_207);
if (lean_is_scalar(x_209)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_209;
}
lean_ctor_set(x_277, 0, x_207);
lean_ctor_set(x_277, 1, x_208);
lean_ctor_set(x_4, 1, x_277);
lean_ctor_set(x_4, 0, x_276);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_4);
lean_ctor_set(x_278, 1, x_206);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_207);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_207);
if (lean_is_scalar(x_209)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_209;
}
lean_ctor_set(x_280, 0, x_207);
lean_ctor_set(x_280, 1, x_208);
lean_ctor_set(x_4, 1, x_280);
lean_ctor_set(x_4, 0, x_279);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_4);
lean_ctor_set(x_281, 1, x_206);
return x_281;
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; lean_object* x_295; uint8_t x_296; 
x_282 = lean_ctor_get(x_4, 1);
lean_inc(x_282);
lean_dec(x_4);
x_283 = lean_ctor_get(x_17, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_17, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_285 = x_17;
} else {
 lean_dec_ref(x_17);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_282, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_282, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_288 = x_282;
} else {
 lean_dec_ref(x_282);
 x_288 = lean_box(0);
}
x_289 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_290 = lean_ctor_get(x_1, 0);
x_291 = lean_ctor_get(x_1, 1);
x_292 = lean_ctor_get(x_1, 2);
x_293 = lean_ctor_get(x_1, 3);
x_294 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_295 = lean_ctor_get(x_1, 4);
x_296 = lean_nat_dec_lt(x_283, x_291);
lean_dec(x_283);
if (x_296 == 0)
{
lean_object* x_297; uint8_t x_298; 
x_297 = lean_array_get_size(x_286);
x_298 = lean_nat_dec_le(x_290, x_297);
lean_dec(x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_285);
x_299 = lean_box(x_294);
lean_inc_ref(x_293);
lean_inc(x_292);
lean_inc_ref(x_295);
x_300 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(x_300, 0, x_295);
lean_closure_set(x_300, 1, x_292);
lean_closure_set(x_300, 2, x_293);
lean_closure_set(x_300, 3, x_299);
lean_closure_set(x_300, 4, x_14);
lean_closure_set(x_300, 5, x_15);
lean_closure_set(x_300, 6, x_16);
lean_inc_ref(x_295);
x_301 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_301, 0, lean_box(0));
lean_closure_set(x_301, 1, x_295);
lean_closure_set(x_301, 2, x_300);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_302 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_301, x_5, x_6, x_7, x_8, x_284);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec_ref(x_302);
if (lean_is_scalar(x_288)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_288;
}
lean_ctor_set(x_305, 0, x_286);
lean_ctor_set(x_305, 1, x_287);
lean_inc(x_2);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_2);
lean_ctor_set(x_306, 1, x_305);
x_3 = x_13;
x_4 = x_306;
x_9 = x_304;
goto _start;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_308 = lean_ctor_get(x_303, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 x_309 = x_303;
} else {
 lean_dec_ref(x_303);
 x_309 = lean_box(0);
}
x_310 = lean_ctor_get(x_302, 1);
lean_inc(x_310);
lean_dec_ref(x_302);
x_311 = lean_ctor_get(x_308, 2);
x_312 = lean_ctor_get(x_308, 3);
lean_inc(x_308);
x_313 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_313, 0, x_308);
lean_inc_ref(x_312);
x_314 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_314, 0, lean_box(0));
lean_closure_set(x_314, 1, x_312);
lean_closure_set(x_314, 2, x_313);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_315 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_314, x_5, x_6, x_7, x_8, x_310);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec_ref(x_315);
x_318 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(x_287, x_316);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_311, 0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_319);
lean_inc_ref(x_312);
x_320 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_312, x_319, x_5, x_6, x_7, x_8, x_317);
if (lean_obj_tag(x_320) == 0)
{
if (x_289 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_309);
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
lean_dec_ref(x_320);
x_322 = lean_box(0);
x_323 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_287, x_316, x_322);
x_324 = lean_array_push(x_286, x_308);
if (lean_is_scalar(x_288)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_288;
}
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
lean_inc(x_2);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_2);
lean_ctor_set(x_326, 1, x_325);
x_3 = x_13;
x_4 = x_326;
x_9 = x_321;
goto _start;
}
else
{
lean_object* x_328; uint8_t x_329; 
x_328 = lean_ctor_get(x_320, 0);
lean_inc(x_328);
x_329 = lean_unbox(x_328);
lean_dec(x_328);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_309);
x_330 = lean_ctor_get(x_320, 1);
lean_inc(x_330);
lean_dec_ref(x_320);
x_331 = lean_box(0);
x_332 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_287, x_316, x_331);
x_333 = lean_array_push(x_286, x_308);
if (lean_is_scalar(x_288)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_288;
}
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_332);
lean_inc(x_2);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_2);
lean_ctor_set(x_335, 1, x_334);
x_3 = x_13;
x_4 = x_335;
x_9 = x_330;
goto _start;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_316);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_337 = lean_ctor_get(x_320, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_338 = x_320;
} else {
 lean_dec_ref(x_320);
 x_338 = lean_box(0);
}
x_339 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0;
x_340 = lean_array_push(x_339, x_308);
if (lean_is_scalar(x_309)) {
 x_341 = lean_alloc_ctor(1, 1, 0);
} else {
 x_341 = x_309;
}
lean_ctor_set(x_341, 0, x_340);
if (lean_is_scalar(x_288)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_288;
}
lean_ctor_set(x_342, 0, x_286);
lean_ctor_set(x_342, 1, x_287);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
if (lean_is_scalar(x_338)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_338;
}
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_337);
return x_344;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_316);
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_345 = lean_ctor_get(x_320, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_320, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_347 = x_320;
} else {
 lean_dec_ref(x_320);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(1, 2, 0);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_345);
lean_ctor_set(x_348, 1, x_346);
return x_348;
}
}
else
{
lean_object* x_349; lean_object* x_350; 
lean_dec(x_316);
lean_dec(x_309);
lean_dec(x_308);
if (lean_is_scalar(x_288)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_288;
}
lean_ctor_set(x_349, 0, x_286);
lean_ctor_set(x_349, 1, x_287);
lean_inc(x_2);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_2);
lean_ctor_set(x_350, 1, x_349);
x_3 = x_13;
x_4 = x_350;
x_9 = x_317;
goto _start;
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_352 = lean_ctor_get(x_315, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_315, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_354 = x_315;
} else {
 lean_dec_ref(x_315);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 2, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_353);
return x_355;
}
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_356 = lean_ctor_get(x_302, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_302, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_358 = x_302;
} else {
 lean_dec_ref(x_302);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_286);
x_360 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_360, 0, x_286);
if (lean_is_scalar(x_288)) {
 x_361 = lean_alloc_ctor(0, 2, 0);
} else {
 x_361 = x_288;
}
lean_ctor_set(x_361, 0, x_286);
lean_ctor_set(x_361, 1, x_287);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_361);
if (lean_is_scalar(x_285)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_285;
}
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_284);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_286);
x_364 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_364, 0, x_286);
if (lean_is_scalar(x_288)) {
 x_365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_365 = x_288;
}
lean_ctor_set(x_365, 0, x_286);
lean_ctor_set(x_365, 1, x_287);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
if (lean_is_scalar(x_285)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_285;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_284);
return x_367;
}
}
}
else
{
uint8_t x_368; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_368 = !lean_is_exclusive(x_17);
if (x_368 == 0)
{
return x_17;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_17, 0);
x_370 = lean_ctor_get(x_17, 1);
lean_inc(x_370);
lean_inc(x_369);
lean_dec(x_17);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
return x_371;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec_ref(x_5);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lean_getRemainingHeartbeats___redArg(x_9, x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_ctor_get(x_1, 1);
x_32 = lean_ctor_get(x_1, 2);
x_33 = lean_ctor_get(x_1, 3);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_35 = lean_ctor_get(x_1, 4);
x_36 = lean_nat_dec_lt(x_25, x_31);
lean_dec(x_25);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_array_get_size(x_27);
x_38 = lean_nat_dec_le(x_30, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_19);
x_39 = lean_box(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_35);
x_40 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(x_40, 0, x_35);
lean_closure_set(x_40, 1, x_32);
lean_closure_set(x_40, 2, x_33);
lean_closure_set(x_40, 3, x_39);
lean_closure_set(x_40, 4, x_16);
lean_closure_set(x_40, 5, x_17);
lean_closure_set(x_40, 6, x_18);
lean_inc_ref(x_35);
x_41 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_41, 0, lean_box(0));
lean_closure_set(x_41, 1, x_35);
lean_closure_set(x_41, 2, x_40);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_42 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_41, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
lean_inc(x_2);
lean_ctor_set(x_6, 0, x_2);
x_45 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_44);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec_ref(x_42);
x_49 = lean_ctor_get(x_47, 2);
x_50 = lean_ctor_get(x_47, 3);
lean_inc(x_47);
x_51 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_51, 0, x_47);
lean_inc_ref(x_50);
x_52 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_52, 0, lean_box(0));
lean_closure_set(x_52, 1, x_50);
lean_closure_set(x_52, 2, x_51);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_53 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_52, x_7, x_8, x_9, x_10, x_48);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(x_28, x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_49, 0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_57);
lean_inc_ref(x_50);
x_58 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_50, x_57, x_7, x_8, x_9, x_10, x_55);
if (lean_obj_tag(x_58) == 0)
{
if (x_29 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_free_object(x_43);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_box(0);
x_61 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_28, x_54, x_60);
x_62 = lean_array_push(x_27, x_47);
lean_ctor_set(x_21, 1, x_61);
lean_ctor_set(x_21, 0, x_62);
lean_inc(x_2);
lean_ctor_set(x_6, 0, x_2);
x_63 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_59);
return x_63;
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_free_object(x_43);
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
lean_dec_ref(x_58);
x_67 = lean_box(0);
x_68 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_28, x_54, x_67);
x_69 = lean_array_push(x_27, x_47);
lean_ctor_set(x_21, 1, x_68);
lean_ctor_set(x_21, 0, x_69);
lean_inc(x_2);
lean_ctor_set(x_6, 0, x_2);
x_70 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_66);
return x_70;
}
else
{
uint8_t x_71; 
lean_dec(x_54);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_58);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_58, 0);
lean_dec(x_72);
x_73 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0;
x_74 = lean_array_push(x_73, x_47);
lean_ctor_set(x_43, 0, x_74);
lean_ctor_set(x_6, 0, x_43);
lean_ctor_set(x_58, 0, x_6);
return x_58;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_58, 1);
lean_inc(x_75);
lean_dec(x_58);
x_76 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0;
x_77 = lean_array_push(x_76, x_47);
lean_ctor_set(x_43, 0, x_77);
lean_ctor_set(x_6, 0, x_43);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_6);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_47);
lean_free_object(x_21);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_79 = !lean_is_exclusive(x_58);
if (x_79 == 0)
{
return x_58;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_58, 0);
x_81 = lean_ctor_get(x_58, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_58);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; 
lean_dec(x_54);
lean_free_object(x_43);
lean_dec(x_47);
lean_inc(x_2);
lean_ctor_set(x_6, 0, x_2);
x_83 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_55);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_free_object(x_43);
lean_dec(x_47);
lean_free_object(x_21);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_84 = !lean_is_exclusive(x_53);
if (x_84 == 0)
{
return x_53;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_53, 0);
x_86 = lean_ctor_get(x_53, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_53);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_88 = lean_ctor_get(x_43, 0);
lean_inc(x_88);
lean_dec(x_43);
x_89 = lean_ctor_get(x_42, 1);
lean_inc(x_89);
lean_dec_ref(x_42);
x_90 = lean_ctor_get(x_88, 2);
x_91 = lean_ctor_get(x_88, 3);
lean_inc(x_88);
x_92 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_92, 0, x_88);
lean_inc_ref(x_91);
x_93 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_93, 0, lean_box(0));
lean_closure_set(x_93, 1, x_91);
lean_closure_set(x_93, 2, x_92);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_94 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_93, x_7, x_8, x_9, x_10, x_89);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec_ref(x_94);
x_97 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(x_28, x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_90, 0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_98);
lean_inc_ref(x_91);
x_99 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_91, x_98, x_7, x_8, x_9, x_10, x_96);
if (lean_obj_tag(x_99) == 0)
{
if (x_29 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = lean_box(0);
x_102 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_28, x_95, x_101);
x_103 = lean_array_push(x_27, x_88);
lean_ctor_set(x_21, 1, x_102);
lean_ctor_set(x_21, 0, x_103);
lean_inc(x_2);
lean_ctor_set(x_6, 0, x_2);
x_104 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_100);
return x_104;
}
else
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_99, 1);
lean_inc(x_107);
lean_dec_ref(x_99);
x_108 = lean_box(0);
x_109 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_28, x_95, x_108);
x_110 = lean_array_push(x_27, x_88);
lean_ctor_set(x_21, 1, x_109);
lean_ctor_set(x_21, 0, x_110);
lean_inc(x_2);
lean_ctor_set(x_6, 0, x_2);
x_111 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_107);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_95);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_112 = lean_ctor_get(x_99, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_113 = x_99;
} else {
 lean_dec_ref(x_99);
 x_113 = lean_box(0);
}
x_114 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0;
x_115 = lean_array_push(x_114, x_88);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_6, 0, x_116);
if (lean_is_scalar(x_113)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_113;
}
lean_ctor_set(x_117, 0, x_6);
lean_ctor_set(x_117, 1, x_112);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_95);
lean_dec(x_88);
lean_free_object(x_21);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_118 = lean_ctor_get(x_99, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_99, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_120 = x_99;
} else {
 lean_dec_ref(x_99);
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
lean_object* x_122; 
lean_dec(x_95);
lean_dec(x_88);
lean_inc(x_2);
lean_ctor_set(x_6, 0, x_2);
x_122 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_96);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_88);
lean_free_object(x_21);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_123 = lean_ctor_get(x_94, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_94, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_125 = x_94;
} else {
 lean_dec_ref(x_94);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
}
else
{
uint8_t x_127; 
lean_free_object(x_21);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_127 = !lean_is_exclusive(x_42);
if (x_127 == 0)
{
return x_42;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_42, 0);
x_129 = lean_ctor_get(x_42, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_42);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
lean_object* x_131; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_27);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_27);
lean_ctor_set(x_6, 0, x_131);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
}
else
{
lean_object* x_132; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_27);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_27);
lean_ctor_set(x_6, 0, x_132);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; uint8_t x_144; 
x_133 = lean_ctor_get(x_19, 0);
x_134 = lean_ctor_get(x_19, 1);
x_135 = lean_ctor_get(x_21, 0);
x_136 = lean_ctor_get(x_21, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_21);
x_137 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_138 = lean_ctor_get(x_1, 0);
x_139 = lean_ctor_get(x_1, 1);
x_140 = lean_ctor_get(x_1, 2);
x_141 = lean_ctor_get(x_1, 3);
x_142 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_143 = lean_ctor_get(x_1, 4);
x_144 = lean_nat_dec_lt(x_133, x_139);
lean_dec(x_133);
if (x_144 == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_array_get_size(x_135);
x_146 = lean_nat_dec_le(x_138, x_145);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_free_object(x_19);
x_147 = lean_box(x_142);
lean_inc_ref(x_141);
lean_inc(x_140);
lean_inc_ref(x_143);
x_148 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(x_148, 0, x_143);
lean_closure_set(x_148, 1, x_140);
lean_closure_set(x_148, 2, x_141);
lean_closure_set(x_148, 3, x_147);
lean_closure_set(x_148, 4, x_16);
lean_closure_set(x_148, 5, x_17);
lean_closure_set(x_148, 6, x_18);
lean_inc_ref(x_143);
x_149 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_149, 0, lean_box(0));
lean_closure_set(x_149, 1, x_143);
lean_closure_set(x_149, 2, x_148);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_150 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_149, x_7, x_8, x_9, x_10, x_134);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec_ref(x_150);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_135);
lean_ctor_set(x_153, 1, x_136);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_153);
lean_ctor_set(x_6, 0, x_2);
x_154 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_152);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_156 = x_151;
} else {
 lean_dec_ref(x_151);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_150, 1);
lean_inc(x_157);
lean_dec_ref(x_150);
x_158 = lean_ctor_get(x_155, 2);
x_159 = lean_ctor_get(x_155, 3);
lean_inc(x_155);
x_160 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_160, 0, x_155);
lean_inc_ref(x_159);
x_161 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_161, 0, lean_box(0));
lean_closure_set(x_161, 1, x_159);
lean_closure_set(x_161, 2, x_160);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_162 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_161, x_7, x_8, x_9, x_10, x_157);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec_ref(x_162);
x_165 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(x_136, x_163);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_158, 0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_166);
lean_inc_ref(x_159);
x_167 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_159, x_166, x_7, x_8, x_9, x_10, x_164);
if (lean_obj_tag(x_167) == 0)
{
if (x_137 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_156);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec_ref(x_167);
x_169 = lean_box(0);
x_170 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_136, x_163, x_169);
x_171 = lean_array_push(x_135, x_155);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_172);
lean_ctor_set(x_6, 0, x_2);
x_173 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_168);
return x_173;
}
else
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_ctor_get(x_167, 0);
lean_inc(x_174);
x_175 = lean_unbox(x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_156);
x_176 = lean_ctor_get(x_167, 1);
lean_inc(x_176);
lean_dec_ref(x_167);
x_177 = lean_box(0);
x_178 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_136, x_163, x_177);
x_179 = lean_array_push(x_135, x_155);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_180);
lean_ctor_set(x_6, 0, x_2);
x_181 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_176);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_163);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_182 = lean_ctor_get(x_167, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_183 = x_167;
} else {
 lean_dec_ref(x_167);
 x_183 = lean_box(0);
}
x_184 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0;
x_185 = lean_array_push(x_184, x_155);
if (lean_is_scalar(x_156)) {
 x_186 = lean_alloc_ctor(1, 1, 0);
} else {
 x_186 = x_156;
}
lean_ctor_set(x_186, 0, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_135);
lean_ctor_set(x_187, 1, x_136);
lean_ctor_set(x_6, 1, x_187);
lean_ctor_set(x_6, 0, x_186);
if (lean_is_scalar(x_183)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_183;
}
lean_ctor_set(x_188, 0, x_6);
lean_ctor_set(x_188, 1, x_182);
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_163);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_136);
lean_dec(x_135);
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_189 = lean_ctor_get(x_167, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_167, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_191 = x_167;
} else {
 lean_dec_ref(x_167);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_163);
lean_dec(x_156);
lean_dec(x_155);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_135);
lean_ctor_set(x_193, 1, x_136);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_193);
lean_ctor_set(x_6, 0, x_2);
x_194 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_164);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_136);
lean_dec(x_135);
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_195 = lean_ctor_get(x_162, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_162, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_197 = x_162;
} else {
 lean_dec_ref(x_162);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_136);
lean_dec(x_135);
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_199 = lean_ctor_get(x_150, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_150, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_201 = x_150;
} else {
 lean_dec_ref(x_150);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_135);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_135);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_135);
lean_ctor_set(x_204, 1, x_136);
lean_ctor_set(x_6, 1, x_204);
lean_ctor_set(x_6, 0, x_203);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
}
else
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_135);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_135);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_135);
lean_ctor_set(x_206, 1, x_136);
lean_ctor_set(x_6, 1, x_206);
lean_ctor_set(x_6, 0, x_205);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; uint8_t x_219; 
x_207 = lean_ctor_get(x_19, 0);
x_208 = lean_ctor_get(x_19, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_19);
x_209 = lean_ctor_get(x_21, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_21, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_211 = x_21;
} else {
 lean_dec_ref(x_21);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_213 = lean_ctor_get(x_1, 0);
x_214 = lean_ctor_get(x_1, 1);
x_215 = lean_ctor_get(x_1, 2);
x_216 = lean_ctor_get(x_1, 3);
x_217 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_218 = lean_ctor_get(x_1, 4);
x_219 = lean_nat_dec_lt(x_207, x_214);
lean_dec(x_207);
if (x_219 == 0)
{
lean_object* x_220; uint8_t x_221; 
x_220 = lean_array_get_size(x_209);
x_221 = lean_nat_dec_le(x_213, x_220);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_222 = lean_box(x_217);
lean_inc_ref(x_216);
lean_inc(x_215);
lean_inc_ref(x_218);
x_223 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(x_223, 0, x_218);
lean_closure_set(x_223, 1, x_215);
lean_closure_set(x_223, 2, x_216);
lean_closure_set(x_223, 3, x_222);
lean_closure_set(x_223, 4, x_16);
lean_closure_set(x_223, 5, x_17);
lean_closure_set(x_223, 6, x_18);
lean_inc_ref(x_218);
x_224 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_224, 0, lean_box(0));
lean_closure_set(x_224, 1, x_218);
lean_closure_set(x_224, 2, x_223);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_225 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_224, x_7, x_8, x_9, x_10, x_208);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec_ref(x_225);
if (lean_is_scalar(x_211)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_211;
}
lean_ctor_set(x_228, 0, x_209);
lean_ctor_set(x_228, 1, x_210);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_228);
lean_ctor_set(x_6, 0, x_2);
x_229 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_227);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_230 = lean_ctor_get(x_226, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 x_231 = x_226;
} else {
 lean_dec_ref(x_226);
 x_231 = lean_box(0);
}
x_232 = lean_ctor_get(x_225, 1);
lean_inc(x_232);
lean_dec_ref(x_225);
x_233 = lean_ctor_get(x_230, 2);
x_234 = lean_ctor_get(x_230, 3);
lean_inc(x_230);
x_235 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_235, 0, x_230);
lean_inc_ref(x_234);
x_236 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_236, 0, lean_box(0));
lean_closure_set(x_236, 1, x_234);
lean_closure_set(x_236, 2, x_235);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_237 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_236, x_7, x_8, x_9, x_10, x_232);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec_ref(x_237);
x_240 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(x_210, x_238);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_233, 0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_241);
lean_inc_ref(x_234);
x_242 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_234, x_241, x_7, x_8, x_9, x_10, x_239);
if (lean_obj_tag(x_242) == 0)
{
if (x_212 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_231);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec_ref(x_242);
x_244 = lean_box(0);
x_245 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_210, x_238, x_244);
x_246 = lean_array_push(x_209, x_230);
if (lean_is_scalar(x_211)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_211;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_245);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_247);
lean_ctor_set(x_6, 0, x_2);
x_248 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_243);
return x_248;
}
else
{
lean_object* x_249; uint8_t x_250; 
x_249 = lean_ctor_get(x_242, 0);
lean_inc(x_249);
x_250 = lean_unbox(x_249);
lean_dec(x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_231);
x_251 = lean_ctor_get(x_242, 1);
lean_inc(x_251);
lean_dec_ref(x_242);
x_252 = lean_box(0);
x_253 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_210, x_238, x_252);
x_254 = lean_array_push(x_209, x_230);
if (lean_is_scalar(x_211)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_211;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_255);
lean_ctor_set(x_6, 0, x_2);
x_256 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_251);
return x_256;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_238);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_257 = lean_ctor_get(x_242, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_258 = x_242;
} else {
 lean_dec_ref(x_242);
 x_258 = lean_box(0);
}
x_259 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0;
x_260 = lean_array_push(x_259, x_230);
if (lean_is_scalar(x_231)) {
 x_261 = lean_alloc_ctor(1, 1, 0);
} else {
 x_261 = x_231;
}
lean_ctor_set(x_261, 0, x_260);
if (lean_is_scalar(x_211)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_211;
}
lean_ctor_set(x_262, 0, x_209);
lean_ctor_set(x_262, 1, x_210);
lean_ctor_set(x_6, 1, x_262);
lean_ctor_set(x_6, 0, x_261);
if (lean_is_scalar(x_258)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_258;
}
lean_ctor_set(x_263, 0, x_6);
lean_ctor_set(x_263, 1, x_257);
return x_263;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_238);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_264 = lean_ctor_get(x_242, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_242, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_266 = x_242;
} else {
 lean_dec_ref(x_242);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
else
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_238);
lean_dec(x_231);
lean_dec(x_230);
if (lean_is_scalar(x_211)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_211;
}
lean_ctor_set(x_268, 0, x_209);
lean_ctor_set(x_268, 1, x_210);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_268);
lean_ctor_set(x_6, 0, x_2);
x_269 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_6, x_7, x_8, x_9, x_10, x_239);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_270 = lean_ctor_get(x_237, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_237, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_272 = x_237;
} else {
 lean_dec_ref(x_237);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
lean_free_object(x_6);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_274 = lean_ctor_get(x_225, 0);
lean_inc(x_274);
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
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_274);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_209);
x_278 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_278, 0, x_209);
if (lean_is_scalar(x_211)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_211;
}
lean_ctor_set(x_279, 0, x_209);
lean_ctor_set(x_279, 1, x_210);
lean_ctor_set(x_6, 1, x_279);
lean_ctor_set(x_6, 0, x_278);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_6);
lean_ctor_set(x_280, 1, x_208);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_209);
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_209);
if (lean_is_scalar(x_211)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_211;
}
lean_ctor_set(x_282, 0, x_209);
lean_ctor_set(x_282, 1, x_210);
lean_ctor_set(x_6, 1, x_282);
lean_ctor_set(x_6, 0, x_281);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_6);
lean_ctor_set(x_283, 1, x_208);
return x_283;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; uint8_t x_298; 
x_284 = lean_ctor_get(x_6, 1);
lean_inc(x_284);
lean_dec(x_6);
x_285 = lean_ctor_get(x_19, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_19, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_287 = x_19;
} else {
 lean_dec_ref(x_19);
 x_287 = lean_box(0);
}
x_288 = lean_ctor_get(x_284, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_284, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_290 = x_284;
} else {
 lean_dec_ref(x_284);
 x_290 = lean_box(0);
}
x_291 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_292 = lean_ctor_get(x_1, 0);
x_293 = lean_ctor_get(x_1, 1);
x_294 = lean_ctor_get(x_1, 2);
x_295 = lean_ctor_get(x_1, 3);
x_296 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_297 = lean_ctor_get(x_1, 4);
x_298 = lean_nat_dec_lt(x_285, x_293);
lean_dec(x_285);
if (x_298 == 0)
{
lean_object* x_299; uint8_t x_300; 
x_299 = lean_array_get_size(x_288);
x_300 = lean_nat_dec_le(x_292, x_299);
lean_dec(x_299);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_287);
x_301 = lean_box(x_296);
lean_inc_ref(x_295);
lean_inc(x_294);
lean_inc_ref(x_297);
x_302 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(x_302, 0, x_297);
lean_closure_set(x_302, 1, x_294);
lean_closure_set(x_302, 2, x_295);
lean_closure_set(x_302, 3, x_301);
lean_closure_set(x_302, 4, x_16);
lean_closure_set(x_302, 5, x_17);
lean_closure_set(x_302, 6, x_18);
lean_inc_ref(x_297);
x_303 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_303, 0, lean_box(0));
lean_closure_set(x_303, 1, x_297);
lean_closure_set(x_303, 2, x_302);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_304 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_303, x_7, x_8, x_9, x_10, x_286);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec_ref(x_304);
if (lean_is_scalar(x_290)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_290;
}
lean_ctor_set(x_307, 0, x_288);
lean_ctor_set(x_307, 1, x_289);
lean_inc(x_2);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_2);
lean_ctor_set(x_308, 1, x_307);
x_309 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_308, x_7, x_8, x_9, x_10, x_306);
return x_309;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_310 = lean_ctor_get(x_305, 0);
lean_inc(x_310);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 x_311 = x_305;
} else {
 lean_dec_ref(x_305);
 x_311 = lean_box(0);
}
x_312 = lean_ctor_get(x_304, 1);
lean_inc(x_312);
lean_dec_ref(x_304);
x_313 = lean_ctor_get(x_310, 2);
x_314 = lean_ctor_get(x_310, 3);
lean_inc(x_310);
x_315 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_315, 0, x_310);
lean_inc_ref(x_314);
x_316 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__0), 8, 3);
lean_closure_set(x_316, 0, lean_box(0));
lean_closure_set(x_316, 1, x_314);
lean_closure_set(x_316, 2, x_315);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_317 = l_Lean_withoutModifyingState___at___Lean_Meta_Rewrites_dischargableWithRfl_x3f_spec__1___redArg(x_316, x_7, x_8, x_9, x_10, x_312);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec_ref(x_317);
x_320 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(x_289, x_318);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_313, 0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_321);
lean_inc_ref(x_314);
x_322 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_314, x_321, x_7, x_8, x_9, x_10, x_319);
if (lean_obj_tag(x_322) == 0)
{
if (x_291 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_311);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
lean_dec_ref(x_322);
x_324 = lean_box(0);
x_325 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_289, x_318, x_324);
x_326 = lean_array_push(x_288, x_310);
if (lean_is_scalar(x_290)) {
 x_327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_327 = x_290;
}
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_325);
lean_inc(x_2);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_2);
lean_ctor_set(x_328, 1, x_327);
x_329 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_328, x_7, x_8, x_9, x_10, x_323);
return x_329;
}
else
{
lean_object* x_330; uint8_t x_331; 
x_330 = lean_ctor_get(x_322, 0);
lean_inc(x_330);
x_331 = lean_unbox(x_330);
lean_dec(x_330);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_311);
x_332 = lean_ctor_get(x_322, 1);
lean_inc(x_332);
lean_dec_ref(x_322);
x_333 = lean_box(0);
x_334 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_Meta_Rewrites_takeListAux_spec__2___redArg(x_289, x_318, x_333);
x_335 = lean_array_push(x_288, x_310);
if (lean_is_scalar(x_290)) {
 x_336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_336 = x_290;
}
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_334);
lean_inc(x_2);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_2);
lean_ctor_set(x_337, 1, x_336);
x_338 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_337, x_7, x_8, x_9, x_10, x_332);
return x_338;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_318);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_339 = lean_ctor_get(x_322, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_340 = x_322;
} else {
 lean_dec_ref(x_322);
 x_340 = lean_box(0);
}
x_341 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0;
x_342 = lean_array_push(x_341, x_310);
if (lean_is_scalar(x_311)) {
 x_343 = lean_alloc_ctor(1, 1, 0);
} else {
 x_343 = x_311;
}
lean_ctor_set(x_343, 0, x_342);
if (lean_is_scalar(x_290)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_290;
}
lean_ctor_set(x_344, 0, x_288);
lean_ctor_set(x_344, 1, x_289);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
if (lean_is_scalar(x_340)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_340;
}
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_339);
return x_346;
}
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_318);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_347 = lean_ctor_get(x_322, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_322, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_349 = x_322;
} else {
 lean_dec_ref(x_322);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_348);
return x_350;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_318);
lean_dec(x_311);
lean_dec(x_310);
if (lean_is_scalar(x_290)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_290;
}
lean_ctor_set(x_351, 0, x_288);
lean_ctor_set(x_351, 1, x_289);
lean_inc(x_2);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_2);
lean_ctor_set(x_352, 1, x_351);
x_353 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg(x_1, x_2, x_15, x_352, x_7, x_8, x_9, x_10, x_319);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_354 = lean_ctor_get(x_317, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_317, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_356 = x_317;
} else {
 lean_dec_ref(x_317);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_354);
lean_ctor_set(x_357, 1, x_355);
return x_357;
}
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_358 = lean_ctor_get(x_304, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_304, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_360 = x_304;
} else {
 lean_dec_ref(x_304);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_288);
x_362 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_362, 0, x_288);
if (lean_is_scalar(x_290)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_290;
}
lean_ctor_set(x_363, 0, x_288);
lean_ctor_set(x_363, 1, x_289);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
if (lean_is_scalar(x_287)) {
 x_365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_365 = x_287;
}
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_286);
return x_365;
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
lean_inc(x_288);
x_366 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_366, 0, x_288);
if (lean_is_scalar(x_290)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_290;
}
lean_ctor_set(x_367, 0, x_288);
lean_ctor_set(x_367, 1, x_289);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
if (lean_is_scalar(x_287)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_287;
}
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_286);
return x_369;
}
}
}
else
{
uint8_t x_370; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
lean_dec_ref(x_1);
x_370 = !lean_is_exclusive(x_19);
if (x_370 == 0)
{
return x_19;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_19, 0);
x_372 = lean_ctor_get(x_19, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_19);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
return x_373;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
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
x_14 = l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7___redArg(x_1, x_11, x_10, x_4, x_4, x_13, x_5, x_6, x_7, x_8, x_9);
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
lean_dec_ref(x_17);
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
lean_dec_ref(x_17);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___Lean_Meta_Rewrites_takeListAux_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_15);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_4);
x_18 = l_Lean_Meta_Rewrites_rewriteCandidates(x_1, x_2, x_4, x_5, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l_Lean_getMaxHeartbeats___redArg(x_12, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_48; uint8_t x_49; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_24);
lean_dec(x_16);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_eq(x_22, x_48);
lean_dec(x_22);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = l_Lean_getRemainingHeartbeats___redArg(x_12, x_23);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
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
uint8_t x_56; 
lean_dec_ref(x_24);
lean_dec(x_19);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
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
uint8_t x_60; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_21);
if (x_60 == 0)
{
return x_21;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_21, 0);
x_62 = lean_ctor_get(x_21, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_21);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_18);
if (x_64 == 0)
{
return x_18;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_18, 0);
x_66 = lean_ctor_get(x_18, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_18);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_6);
x_16 = lean_unbox(x_7);
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
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__6____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__6____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__6____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__7____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__8____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__8____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__8____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__9____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__9____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__9____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__10____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__11____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__11____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__11____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__12____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__12____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__12____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__13____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__13____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__13____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__14____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__14____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__14____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__15____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__15____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__15____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__16____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__16____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__16____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__17____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__17____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__17____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__18____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__18____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__18____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__19____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__19____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__19____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__20____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__20____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__20____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__21____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__21____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__21____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__22____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__22____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__22____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__23____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__24____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__25____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__26____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__27____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__28____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__29____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites_2316440083____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__0____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__1____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__2____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__3____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__4____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_ = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn___closed__5____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites_414759425____hygCtx___hyg_2_(lean_io_mk_world());
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
l_Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0 = _init_l_Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0();
lean_mark_persistent(l_Lean_getLocalHyps___at___Lean_Meta_Rewrites_localHypotheses_spec__1___closed__0);
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
if (builtin) {res = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites_1202513136____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default);
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__0 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__0);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState);
if (builtin) {res = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites_3291377554____hygCtx___hyg_2_(lean_io_mk_world());
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
l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__0 = _init_l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__0();
l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__1 = _init_l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__1);
l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__2 = _init_l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_Rewrites_rwLemma_spec__3___closed__2);
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
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Rewrites_takeListAux_spec__7_spec__7___redArg___closed__0);
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
