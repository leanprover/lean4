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
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1___closed__1;
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_1333____lambda__1(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__6;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at_Lean_Meta_Rewrites_rewriteCandidates___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__9;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__18;
static lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__4;
lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__6(lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
static lean_object* l_Lean_Meta_Rewrites_solveByElim___closed__4;
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__3;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__15(lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_findMatchesExt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__2;
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_toCtorIdx___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__16(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__1___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__11;
static lean_object* l_Lean_Meta_Rewrites_solveByElim___closed__3;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__11;
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__3;
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default;
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__12;
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__2(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_solveByElim___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Rewrites_rewriteCandidates___spec__5(size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__13;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Rewrites_takeListAux___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__17;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Meta_Rewrites_localHypotheses___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Meta_Rewrites_takeListAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Rewrites_solveByElim___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___lambda__1(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__4;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Rewrites_takeListAux___spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__3;
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__16___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__7;
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__8(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma___closed__2;
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Meta_Rewrites_localHypotheses___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__2(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_1273_(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__2;
lean_object* l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Rewrites_rewriteCandidates___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__6;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__15___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__8;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__5;
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__15;
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__18(lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__13;
static lean_object* l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__3;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__16;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__12(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__14(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__14___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__1;
static lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__1;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_1333_(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef___closed__1;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getRemainingHeartbeats(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__17___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__9;
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__2___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__2;
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__17(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__12___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Rewrites_rewriteCandidates___spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__1___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_Rewrites_RewriteResult_addSuggestion___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__9;
static lean_object* l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion(lean_object*);
lean_object* l_Lean_MVarId_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Rewrites_solveByElim___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_Rewrites_RewriteResult_addSuggestion___spec__1(lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__16;
lean_object* l_Lean_getLocalHyps___at_Lean_MVarId_symmSaturate___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__9(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__5;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__15;
static lean_object* l_Lean_Meta_Rewrites_solveByElim___lambda__3___closed__2;
lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__20;
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_incPrio(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__13___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__1;
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__6;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__6;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__10(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Rewrites_takeListAux___spec__4(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__4(lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__12;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__10;
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_solveByElim___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Rewrites_takeListAux___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Meta_Rewrites_takeListAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__7;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwFindDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__8;
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Meta_Rewrites_dischargableWithRfl_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__6___closed__1;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__7;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Rewrites_takeListAux___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Rewrites_takeListAux___spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwFindDecls___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Rewrites_rewriteCandidates___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_backwardWeight;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Substring_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__18___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_forwardWeight;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___boxed(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_toCtorIdx___boxed(lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__4;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Rewrites_rwLemma___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__5;
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__1;
lean_object* l_Lean_Expr_getAppFnArgs(lean_object*);
lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__2;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__19;
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__19___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__19(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_solveByElim___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_bracket(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_rwFindDecls___closed__1;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_droppedKeys___closed__7;
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_droppedKeys;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__4;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_getMaxHeartbeats(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__14;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__11___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_toCtorIdx(uint8_t);
lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rewrites", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__1;
x_2 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__5;
x_2 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Rewrites", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__7;
x_2 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__9;
x_2 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__11;
x_2 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__13;
x_2 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__14;
x_2 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__15;
x_2 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__16;
x_2 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__17;
x_2 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__18;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__19;
x_2 = lean_unsigned_to_nat(5u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__3;
x_3 = 0;
x_4 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__20;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lemmas", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__1;
x_2 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__2;
x_3 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__19;
x_2 = lean_unsigned_to_nat(46u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__2;
x_3 = 0;
x_4 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__3;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrArg", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteResultLemma___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteResultLemma(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_Meta_Rewrites_rewriteResultLemma___closed__2;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_7);
x_9 = lean_unsigned_to_nat(5u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = l_Lean_Expr_getRevArg_x21(x_2, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Iff", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__5() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 1;
x_2 = 2;
x_3 = lean_alloc_ctor(0, 0, 5);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, 2, x_2);
lean_ctor_set_uint8(x_3, 3, x_1);
lean_ctor_set_uint8(x_3, 4, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Expr_getAppFnArgs(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__2;
x_17 = lean_string_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__3;
x_19 = lean_string_dec_eq(x_15, x_18);
lean_dec(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_9);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_20 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_array_get_size(x_13);
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_9);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_25 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_fget(x_13, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_array_fget(x_13, x_29);
lean_dec(x_13);
x_31 = 0;
x_32 = lean_box(x_31);
lean_inc(x_1);
lean_ctor_set(x_9, 1, x_32);
lean_ctor_set(x_9, 0, x_1);
x_33 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__5;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_34 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___rarg(x_28, x_9, x_33, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__4;
x_38 = lean_array_push(x_37, x_35);
x_39 = 1;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___rarg(x_30, x_41, x_33, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_array_push(x_38, x_44);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_42);
x_48 = lean_array_push(x_38, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_38);
x_50 = !lean_is_exclusive(x_42);
if (x_50 == 0)
{
return x_42;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_42, 0);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_42);
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
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_34);
if (x_54 == 0)
{
return x_34;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_34, 0);
x_56 = lean_ctor_get(x_34, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_34);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_15);
x_58 = lean_array_get_size(x_13);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_free_object(x_9);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_61 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_8);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_array_fget(x_13, x_63);
x_65 = lean_unsigned_to_nat(2u);
x_66 = lean_array_fget(x_13, x_65);
lean_dec(x_13);
x_67 = 0;
x_68 = lean_box(x_67);
lean_inc(x_1);
lean_ctor_set(x_9, 1, x_68);
lean_ctor_set(x_9, 0, x_1);
x_69 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__5;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_70 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___rarg(x_64, x_9, x_69, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__4;
x_74 = lean_array_push(x_73, x_71);
x_75 = 1;
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___rarg(x_66, x_77, x_69, x_4, x_5, x_6, x_7, x_72);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_array_push(x_74, x_80);
lean_ctor_set(x_78, 0, x_81);
return x_78;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_78, 0);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_78);
x_84 = lean_array_push(x_74, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_74);
x_86 = !lean_is_exclusive(x_78);
if (x_86 == 0)
{
return x_78;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_78, 0);
x_88 = lean_ctor_get(x_78, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_78);
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
lean_dec(x_66);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_70);
if (x_90 == 0)
{
return x_70;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_70, 0);
x_92 = lean_ctor_get(x_70, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_70);
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
x_94 = lean_ctor_get(x_9, 1);
lean_inc(x_94);
lean_dec(x_9);
x_95 = lean_ctor_get(x_10, 1);
lean_inc(x_95);
lean_dec(x_10);
x_96 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__2;
x_97 = lean_string_dec_eq(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__3;
x_99 = lean_string_dec_eq(x_95, x_98);
lean_dec(x_95);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_94);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_100 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_8);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_array_get_size(x_94);
x_103 = lean_unsigned_to_nat(2u);
x_104 = lean_nat_dec_eq(x_102, x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_94);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_105 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_8);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_array_fget(x_94, x_107);
x_109 = lean_unsigned_to_nat(1u);
x_110 = lean_array_fget(x_94, x_109);
lean_dec(x_94);
x_111 = 0;
x_112 = lean_box(x_111);
lean_inc(x_1);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_1);
lean_ctor_set(x_113, 1, x_112);
x_114 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__5;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_115 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___rarg(x_108, x_113, x_114, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__4;
x_119 = lean_array_push(x_118, x_116);
x_120 = 1;
x_121 = lean_box(x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_1);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___rarg(x_110, x_122, x_114, x_4, x_5, x_6, x_7, x_117);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_127 = lean_array_push(x_119, x_124);
if (lean_is_scalar(x_126)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_126;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_119);
x_129 = lean_ctor_get(x_123, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_123, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_131 = x_123;
} else {
 lean_dec_ref(x_123);
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
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_110);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_133 = lean_ctor_get(x_115, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_115, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_135 = x_115;
} else {
 lean_dec_ref(x_115);
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
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_dec(x_95);
x_137 = lean_array_get_size(x_94);
x_138 = lean_unsigned_to_nat(3u);
x_139 = lean_nat_dec_eq(x_137, x_138);
lean_dec(x_137);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_94);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_140 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_8);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_array_fget(x_94, x_142);
x_144 = lean_unsigned_to_nat(2u);
x_145 = lean_array_fget(x_94, x_144);
lean_dec(x_94);
x_146 = 0;
x_147 = lean_box(x_146);
lean_inc(x_1);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_1);
lean_ctor_set(x_148, 1, x_147);
x_149 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__5;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_150 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___rarg(x_143, x_148, x_149, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__4;
x_154 = lean_array_push(x_153, x_151);
x_155 = 1;
x_156 = lean_box(x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_1);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_Meta_LazyDiscrTree_InitEntry_fromExpr___rarg(x_145, x_157, x_149, x_4, x_5, x_6, x_7, x_152);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
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
x_162 = lean_array_push(x_154, x_159);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_160);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_154);
x_164 = lean_ctor_get(x_158, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_158, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_166 = x_158;
} else {
 lean_dec_ref(x_158);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_145);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_168 = lean_ctor_get(x_150, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_150, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_170 = x_150;
} else {
 lean_dec_ref(x_150);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_172 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_8);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_174 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_8);
return x_175;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = 2;
lean_ctor_set_uint8(x_9, 9, x_11);
x_12 = 0;
x_13 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_2, x_12, x_3, x_4, x_5, x_6, x_7);
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
else
{
uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_22 = lean_ctor_get_uint8(x_9, 0);
x_23 = lean_ctor_get_uint8(x_9, 1);
x_24 = lean_ctor_get_uint8(x_9, 2);
x_25 = lean_ctor_get_uint8(x_9, 3);
x_26 = lean_ctor_get_uint8(x_9, 4);
x_27 = lean_ctor_get_uint8(x_9, 5);
x_28 = lean_ctor_get_uint8(x_9, 6);
x_29 = lean_ctor_get_uint8(x_9, 7);
x_30 = lean_ctor_get_uint8(x_9, 8);
x_31 = lean_ctor_get_uint8(x_9, 10);
x_32 = lean_ctor_get_uint8(x_9, 11);
x_33 = lean_ctor_get_uint8(x_9, 12);
lean_dec(x_9);
x_34 = 2;
x_35 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_35, 0, x_22);
lean_ctor_set_uint8(x_35, 1, x_23);
lean_ctor_set_uint8(x_35, 2, x_24);
lean_ctor_set_uint8(x_35, 3, x_25);
lean_ctor_set_uint8(x_35, 4, x_26);
lean_ctor_set_uint8(x_35, 5, x_27);
lean_ctor_set_uint8(x_35, 6, x_28);
lean_ctor_set_uint8(x_35, 7, x_29);
lean_ctor_set_uint8(x_35, 8, x_30);
lean_ctor_set_uint8(x_35, 9, x_34);
lean_ctor_set_uint8(x_35, 10, x_31);
lean_ctor_set_uint8(x_35, 11, x_32);
lean_ctor_set_uint8(x_35, 12, x_33);
lean_ctor_set(x_3, 0, x_35);
x_36 = 0;
x_37 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_2, x_36, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_44 = x_37;
} else {
 lean_dec_ref(x_37);
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
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_46 = lean_ctor_get(x_3, 0);
x_47 = lean_ctor_get(x_3, 1);
x_48 = lean_ctor_get(x_3, 2);
x_49 = lean_ctor_get(x_3, 3);
x_50 = lean_ctor_get(x_3, 4);
x_51 = lean_ctor_get(x_3, 5);
x_52 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_53 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_3);
x_54 = lean_ctor_get_uint8(x_46, 0);
x_55 = lean_ctor_get_uint8(x_46, 1);
x_56 = lean_ctor_get_uint8(x_46, 2);
x_57 = lean_ctor_get_uint8(x_46, 3);
x_58 = lean_ctor_get_uint8(x_46, 4);
x_59 = lean_ctor_get_uint8(x_46, 5);
x_60 = lean_ctor_get_uint8(x_46, 6);
x_61 = lean_ctor_get_uint8(x_46, 7);
x_62 = lean_ctor_get_uint8(x_46, 8);
x_63 = lean_ctor_get_uint8(x_46, 10);
x_64 = lean_ctor_get_uint8(x_46, 11);
x_65 = lean_ctor_get_uint8(x_46, 12);
if (lean_is_exclusive(x_46)) {
 x_66 = x_46;
} else {
 lean_dec_ref(x_46);
 x_66 = lean_box(0);
}
x_67 = 2;
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 0, 13);
} else {
 x_68 = x_66;
}
lean_ctor_set_uint8(x_68, 0, x_54);
lean_ctor_set_uint8(x_68, 1, x_55);
lean_ctor_set_uint8(x_68, 2, x_56);
lean_ctor_set_uint8(x_68, 3, x_57);
lean_ctor_set_uint8(x_68, 4, x_58);
lean_ctor_set_uint8(x_68, 5, x_59);
lean_ctor_set_uint8(x_68, 6, x_60);
lean_ctor_set_uint8(x_68, 7, x_61);
lean_ctor_set_uint8(x_68, 8, x_62);
lean_ctor_set_uint8(x_68, 9, x_67);
lean_ctor_set_uint8(x_68, 10, x_63);
lean_ctor_set_uint8(x_68, 11, x_64);
lean_ctor_set_uint8(x_68, 12, x_65);
x_69 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_47);
lean_ctor_set(x_69, 2, x_48);
lean_ctor_set(x_69, 3, x_49);
lean_ctor_set(x_69, 4, x_50);
lean_ctor_set(x_69, 5, x_51);
lean_ctor_set_uint8(x_69, sizeof(void*)*6, x_52);
lean_ctor_set_uint8(x_69, sizeof(void*)*6 + 1, x_53);
x_70 = 0;
x_71 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_2, x_70, x_69, x_4, x_5, x_6, x_7);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = l_Lean_ConstantInfo_type(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___boxed), 8, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__2), 7, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = 0;
x_13 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(x_11, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inj", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__1;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inj'", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__5;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_string_utf8_byte_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_10);
x_13 = lean_nat_sub(x_10, x_11);
x_14 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__2;
lean_inc(x_13);
x_15 = l_Substring_prevn(x_12, x_14, x_13);
x_16 = lean_nat_add(x_11, x_15);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_10);
x_18 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__4;
x_19 = l_Substring_beq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__6;
x_21 = l_Substring_prevn(x_12, x_20, x_13);
lean_dec(x_12);
x_22 = lean_nat_add(x_11, x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_10);
x_24 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__8;
x_25 = l_Substring_beq(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__3(x_1, x_2, x_26, x_4, x_5, x_6, x_7, x_8);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_28 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_30 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_8);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(0);
x_33 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__3(x_1, x_2, x_32, x_4, x_5, x_6, x_7, x_8);
return x_33;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sizeOf_spec", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__5___closed__1;
x_11 = lean_string_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("injEq", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__6___closed__1;
x_11 = lean_string_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__5(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__5(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_2);
x_14 = l_Lean_Meta_allowCompletion(x_13, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_9);
x_16 = lean_box(0);
x_17 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__6(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_12);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_2);
x_21 = l_Lean_Meta_allowCompletion(x_20, x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_22 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__6(x_1, x_2, x_24, x_4, x_5, x_6, x_7, x_19);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_ConstantInfo_isUnsafe(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__7(x_2, x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
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
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Meta_Rewrites_localHypotheses___spec__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Meta_Rewrites_forwardWeight;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Meta_Rewrites_backwardWeight;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = 1;
x_14 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_10, x_13, x_12, x_14, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = l_Lean_Meta_whnfR(x_20, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_Expr_getAppFnArgs(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_25, 1);
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__2;
x_33 = lean_string_dec_eq(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__3;
x_35 = lean_string_dec_eq(x_31, x_34);
lean_dec(x_31);
if (x_35 == 0)
{
lean_object* x_36; 
lean_free_object(x_25);
lean_dec(x_29);
lean_free_object(x_17);
lean_dec(x_1);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_22, 0, x_36);
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_array_get_size(x_29);
lean_dec(x_29);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_dec_eq(x_37, x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
lean_free_object(x_25);
lean_free_object(x_17);
lean_dec(x_1);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_22, 0, x_40);
return x_22;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__1;
lean_inc(x_1);
lean_ctor_set(x_25, 1, x_41);
lean_ctor_set(x_25, 0, x_1);
x_42 = lean_array_push(x_2, x_25);
x_43 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__2;
lean_ctor_set(x_17, 1, x_43);
lean_ctor_set(x_17, 0, x_1);
x_44 = lean_array_push(x_42, x_17);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_22, 0, x_45);
return x_22;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_31);
x_46 = lean_array_get_size(x_29);
lean_dec(x_29);
x_47 = lean_unsigned_to_nat(3u);
x_48 = lean_nat_dec_eq(x_46, x_47);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_free_object(x_25);
lean_free_object(x_17);
lean_dec(x_1);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_2);
lean_ctor_set(x_22, 0, x_49);
return x_22;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__1;
lean_inc(x_1);
lean_ctor_set(x_25, 1, x_50);
lean_ctor_set(x_25, 0, x_1);
x_51 = lean_array_push(x_2, x_25);
x_52 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__2;
lean_ctor_set(x_17, 1, x_52);
lean_ctor_set(x_17, 0, x_1);
x_53 = lean_array_push(x_51, x_17);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_22, 0, x_54);
return x_22;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_25, 1);
lean_inc(x_55);
lean_dec(x_25);
x_56 = lean_ctor_get(x_26, 1);
lean_inc(x_56);
lean_dec(x_26);
x_57 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__2;
x_58 = lean_string_dec_eq(x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__3;
x_60 = lean_string_dec_eq(x_56, x_59);
lean_dec(x_56);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_55);
lean_free_object(x_17);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_2);
lean_ctor_set(x_22, 0, x_61);
return x_22;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_array_get_size(x_55);
lean_dec(x_55);
x_63 = lean_unsigned_to_nat(2u);
x_64 = lean_nat_dec_eq(x_62, x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; 
lean_free_object(x_17);
lean_dec(x_1);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_22, 0, x_65);
return x_22;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__1;
lean_inc(x_1);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_array_push(x_2, x_67);
x_69 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__2;
lean_ctor_set(x_17, 1, x_69);
lean_ctor_set(x_17, 0, x_1);
x_70 = lean_array_push(x_68, x_17);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_22, 0, x_71);
return x_22;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_56);
x_72 = lean_array_get_size(x_55);
lean_dec(x_55);
x_73 = lean_unsigned_to_nat(3u);
x_74 = lean_nat_dec_eq(x_72, x_73);
lean_dec(x_72);
if (x_74 == 0)
{
lean_object* x_75; 
lean_free_object(x_17);
lean_dec(x_1);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_2);
lean_ctor_set(x_22, 0, x_75);
return x_22;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__1;
lean_inc(x_1);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_array_push(x_2, x_77);
x_79 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__2;
lean_ctor_set(x_17, 1, x_79);
lean_ctor_set(x_17, 0, x_1);
x_80 = lean_array_push(x_78, x_17);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_22, 0, x_81);
return x_22;
}
}
}
}
else
{
lean_object* x_82; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_17);
lean_dec(x_1);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_2);
lean_ctor_set(x_22, 0, x_82);
return x_22;
}
}
else
{
lean_object* x_83; 
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_17);
lean_dec(x_1);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_2);
lean_ctor_set(x_22, 0, x_83);
return x_22;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_22, 0);
x_85 = lean_ctor_get(x_22, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_22);
x_86 = l_Lean_Expr_getAppFnArgs(x_84);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 1)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_90 = x_86;
} else {
 lean_dec_ref(x_86);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_dec(x_87);
x_92 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__2;
x_93 = lean_string_dec_eq(x_91, x_92);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__3;
x_95 = lean_string_dec_eq(x_91, x_94);
lean_dec(x_91);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_90);
lean_dec(x_89);
lean_free_object(x_17);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_2);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_85);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_array_get_size(x_89);
lean_dec(x_89);
x_99 = lean_unsigned_to_nat(2u);
x_100 = lean_nat_dec_eq(x_98, x_99);
lean_dec(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_90);
lean_free_object(x_17);
lean_dec(x_1);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_2);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_85);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__1;
lean_inc(x_1);
if (lean_is_scalar(x_90)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_90;
}
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_array_push(x_2, x_104);
x_106 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__2;
lean_ctor_set(x_17, 1, x_106);
lean_ctor_set(x_17, 0, x_1);
x_107 = lean_array_push(x_105, x_17);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_85);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_91);
x_110 = lean_array_get_size(x_89);
lean_dec(x_89);
x_111 = lean_unsigned_to_nat(3u);
x_112 = lean_nat_dec_eq(x_110, x_111);
lean_dec(x_110);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_90);
lean_free_object(x_17);
lean_dec(x_1);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_2);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_85);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__1;
lean_inc(x_1);
if (lean_is_scalar(x_90)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_90;
}
lean_ctor_set(x_116, 0, x_1);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_array_push(x_2, x_116);
x_118 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__2;
lean_ctor_set(x_17, 1, x_118);
lean_ctor_set(x_17, 0, x_1);
x_119 = lean_array_push(x_117, x_17);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_85);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_free_object(x_17);
lean_dec(x_1);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_2);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_85);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_87);
lean_dec(x_86);
lean_free_object(x_17);
lean_dec(x_1);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_2);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_85);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_free_object(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_22);
if (x_126 == 0)
{
return x_22;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_22, 0);
x_128 = lean_ctor_get(x_22, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_22);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_17, 1);
lean_inc(x_130);
lean_dec(x_17);
x_131 = l_Lean_Meta_whnfR(x_130, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
x_135 = l_Lean_Expr_getAppFnArgs(x_132);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 1)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
lean_dec(x_136);
x_141 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__2;
x_142 = lean_string_dec_eq(x_140, x_141);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__3;
x_144 = lean_string_dec_eq(x_140, x_143);
lean_dec(x_140);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_1);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_2);
if (lean_is_scalar(x_134)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_134;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_133);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_array_get_size(x_138);
lean_dec(x_138);
x_148 = lean_unsigned_to_nat(2u);
x_149 = lean_nat_dec_eq(x_147, x_148);
lean_dec(x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_139);
lean_dec(x_1);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_2);
if (lean_is_scalar(x_134)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_134;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_133);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__1;
lean_inc(x_1);
if (lean_is_scalar(x_139)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_139;
}
lean_ctor_set(x_153, 0, x_1);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_array_push(x_2, x_153);
x_155 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__2;
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_1);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_array_push(x_154, x_156);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
if (lean_is_scalar(x_134)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_134;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_133);
return x_159;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_140);
x_160 = lean_array_get_size(x_138);
lean_dec(x_138);
x_161 = lean_unsigned_to_nat(3u);
x_162 = lean_nat_dec_eq(x_160, x_161);
lean_dec(x_160);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_139);
lean_dec(x_1);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_2);
if (lean_is_scalar(x_134)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_134;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_133);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_165 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__1;
lean_inc(x_1);
if (lean_is_scalar(x_139)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_139;
}
lean_ctor_set(x_166, 0, x_1);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_array_push(x_2, x_166);
x_168 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__2;
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_1);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_array_push(x_167, x_169);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
if (lean_is_scalar(x_134)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_134;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_133);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_1);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_2);
if (lean_is_scalar(x_134)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_134;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_133);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_1);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_2);
if (lean_is_scalar(x_134)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_134;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_133);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_2);
lean_dec(x_1);
x_177 = lean_ctor_get(x_131, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_131, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_179 = x_131;
} else {
 lean_dec_ref(x_131);
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
}
else
{
uint8_t x_181; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_15);
if (x_181 == 0)
{
return x_15;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_15, 0);
x_183 = lean_ctor_get(x_15, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_15);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_9);
if (x_185 == 0)
{
return x_9;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_9, 0);
x_187 = lean_ctor_get(x_9, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_9);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_array_uget(x_4, x_6);
x_16 = l_Lean_Expr_fvarId_x21(x_15);
x_17 = l_List_elem___at_Lean_Meta_Rewrites_localHypotheses___spec__1(x_16, x_1);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1(x_15, x_7, x_18, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = 1;
x_30 = lean_usize_add(x_6, x_29);
x_6 = x_30;
x_7 = x_28;
x_12 = x_27;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
size_t x_36; size_t x_37; 
lean_dec(x_15);
x_36 = 1;
x_37 = lean_usize_add(x_6, x_36);
x_6 = x_37;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_getLocalHyps___at_Lean_MVarId_symmSaturate___spec__1(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_array_size(x_8);
x_12 = 0;
x_13 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2(x_1, x_8, x_10, x_8, x_11, x_12, x_13, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_8);
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
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Meta_Rewrites_localHypotheses___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_Meta_Rewrites_localHypotheses___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
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
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__1() {
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
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_droppedKeys___closed__2;
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l_Lean_Meta_Rewrites_droppedKeys___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(3);
x_2 = l_Lean_Meta_Rewrites_droppedKeys___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_droppedKeys___closed__3;
x_2 = l_Lean_Meta_Rewrites_droppedKeys___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Rewrites_droppedKeys___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_droppedKeys___closed__1;
x_2 = l_Lean_Meta_Rewrites_droppedKeys___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_droppedKeys() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Rewrites_droppedKeys___closed__8;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_createModuleTreeRef___closed__1() {
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
x_6 = l_Lean_Meta_Rewrites_createModuleTreeRef___closed__1;
x_7 = l_Lean_Meta_Rewrites_droppedKeys;
x_8 = l_Lean_Meta_LazyDiscrTree_createModuleTreeRef___rarg(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_1273_(lean_object* x_1) {
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__1() {
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
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_1333____lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_1333_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_1333____lambda__1), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_3, x_1);
return x_4;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_dec(x_7);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_mul(x_8, x_1);
lean_dec(x_1);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_mul(x_14, x_1);
lean_dec(x_1);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
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
static lean_object* _init_l_Lean_Meta_Rewrites_rwFindDecls___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwFindDecls___closed__2() {
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
x_8 = l_Lean_Meta_Rewrites_rwFindDecls___closed__1;
x_9 = l_Lean_Meta_Rewrites_createModuleTreeRef___closed__1;
x_10 = l_Lean_Meta_Rewrites_droppedKeys;
x_11 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask;
x_12 = l_Lean_Meta_Rewrites_rwFindDecls___closed__2;
x_13 = l_Lean_Meta_LazyDiscrTree_findMatchesExt___rarg(x_1, x_8, x_9, x_10, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Meta_Rewrites_dischargableWithRfl_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = 0;
x_8 = lean_box(0);
lean_inc(x_2);
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_mvarId_x21(x_10);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; 
x_16 = 2;
lean_ctor_set_uint8(x_14, 9, x_16);
x_17 = l_Lean_MVarId_refl(x_12, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = 1;
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
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_30 = lean_ctor_get_uint8(x_14, 0);
x_31 = lean_ctor_get_uint8(x_14, 1);
x_32 = lean_ctor_get_uint8(x_14, 2);
x_33 = lean_ctor_get_uint8(x_14, 3);
x_34 = lean_ctor_get_uint8(x_14, 4);
x_35 = lean_ctor_get_uint8(x_14, 5);
x_36 = lean_ctor_get_uint8(x_14, 6);
x_37 = lean_ctor_get_uint8(x_14, 7);
x_38 = lean_ctor_get_uint8(x_14, 8);
x_39 = lean_ctor_get_uint8(x_14, 10);
x_40 = lean_ctor_get_uint8(x_14, 11);
x_41 = lean_ctor_get_uint8(x_14, 12);
lean_dec(x_14);
x_42 = 2;
x_43 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_43, 0, x_30);
lean_ctor_set_uint8(x_43, 1, x_31);
lean_ctor_set_uint8(x_43, 2, x_32);
lean_ctor_set_uint8(x_43, 3, x_33);
lean_ctor_set_uint8(x_43, 4, x_34);
lean_ctor_set_uint8(x_43, 5, x_35);
lean_ctor_set_uint8(x_43, 6, x_36);
lean_ctor_set_uint8(x_43, 7, x_37);
lean_ctor_set_uint8(x_43, 8, x_38);
lean_ctor_set_uint8(x_43, 9, x_42);
lean_ctor_set_uint8(x_43, 10, x_39);
lean_ctor_set_uint8(x_43, 11, x_40);
lean_ctor_set_uint8(x_43, 12, x_41);
lean_ctor_set(x_2, 0, x_43);
x_44 = l_Lean_MVarId_refl(x_12, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = 1;
x_48 = lean_box(x_47);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_52 = x_44;
} else {
 lean_dec_ref(x_44);
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
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_54 = lean_ctor_get(x_2, 0);
x_55 = lean_ctor_get(x_2, 1);
x_56 = lean_ctor_get(x_2, 2);
x_57 = lean_ctor_get(x_2, 3);
x_58 = lean_ctor_get(x_2, 4);
x_59 = lean_ctor_get(x_2, 5);
x_60 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_61 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_2);
x_62 = lean_ctor_get_uint8(x_54, 0);
x_63 = lean_ctor_get_uint8(x_54, 1);
x_64 = lean_ctor_get_uint8(x_54, 2);
x_65 = lean_ctor_get_uint8(x_54, 3);
x_66 = lean_ctor_get_uint8(x_54, 4);
x_67 = lean_ctor_get_uint8(x_54, 5);
x_68 = lean_ctor_get_uint8(x_54, 6);
x_69 = lean_ctor_get_uint8(x_54, 7);
x_70 = lean_ctor_get_uint8(x_54, 8);
x_71 = lean_ctor_get_uint8(x_54, 10);
x_72 = lean_ctor_get_uint8(x_54, 11);
x_73 = lean_ctor_get_uint8(x_54, 12);
if (lean_is_exclusive(x_54)) {
 x_74 = x_54;
} else {
 lean_dec_ref(x_54);
 x_74 = lean_box(0);
}
x_75 = 2;
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 0, 13);
} else {
 x_76 = x_74;
}
lean_ctor_set_uint8(x_76, 0, x_62);
lean_ctor_set_uint8(x_76, 1, x_63);
lean_ctor_set_uint8(x_76, 2, x_64);
lean_ctor_set_uint8(x_76, 3, x_65);
lean_ctor_set_uint8(x_76, 4, x_66);
lean_ctor_set_uint8(x_76, 5, x_67);
lean_ctor_set_uint8(x_76, 6, x_68);
lean_ctor_set_uint8(x_76, 7, x_69);
lean_ctor_set_uint8(x_76, 8, x_70);
lean_ctor_set_uint8(x_76, 9, x_75);
lean_ctor_set_uint8(x_76, 10, x_71);
lean_ctor_set_uint8(x_76, 11, x_72);
lean_ctor_set_uint8(x_76, 12, x_73);
x_77 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_55);
lean_ctor_set(x_77, 2, x_56);
lean_ctor_set(x_77, 3, x_57);
lean_ctor_set(x_77, 4, x_58);
lean_ctor_set(x_77, 5, x_59);
lean_ctor_set_uint8(x_77, sizeof(void*)*6, x_60);
lean_ctor_set_uint8(x_77, sizeof(void*)*6 + 1, x_61);
x_78 = l_Lean_MVarId_refl(x_12, x_77, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = 1;
x_82 = lean_box(x_81);
if (lean_is_scalar(x_80)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_80;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_86 = x_78;
} else {
 lean_dec_ref(x_78);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_dischargableWithRfl_x3f___lambda__1), 6, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg), 7, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_withoutModifyingState___at_Lean_Meta_Rewrites_dischargableWithRfl_x3f___spec__1(x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_Exception_isInterrupt(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Exception_isRuntime(x_13);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; 
lean_dec(x_13);
x_16 = 0;
x_17 = lean_box(x_16);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
return x_11;
}
}
else
{
return x_11;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = l_Lean_Exception_isInterrupt(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_18);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_ppExpr(x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Std_Format_defWidth;
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
x_17 = l_Std_Format_defWidth;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_SideConditions_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_SideConditions_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_Rewrites_SideConditions_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Rewrites_solveByElim___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Rewrites_solveByElim___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_Rewrites_solveByElim___lambda__3___closed__2;
x_8 = l_Lean_throwError___at_Lean_Meta_Rewrites_solveByElim___spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_solveByElim___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_solveByElim___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_solveByElim___lambda__3___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_solveByElim___closed__4() {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = l_Lean_Meta_Rewrites_solveByElim___closed__1;
x_9 = l_Lean_Meta_Rewrites_solveByElim___closed__2;
x_10 = l_Lean_Meta_Rewrites_solveByElim___closed__3;
x_11 = 0;
x_12 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_11);
x_13 = l_Lean_Meta_Rewrites_solveByElim___closed__4;
x_14 = 1;
x_15 = 1;
x_16 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*2 + 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2 + 2, x_11);
x_17 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 2, x_15);
x_18 = lean_box(0);
x_19 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
lean_inc(x_5);
x_20 = l_Lean_Meta_SolveByElim_mkAssumptionSet(x_11, x_11, x_18, x_18, x_19, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l_Lean_Meta_SolveByElim_solveByElim(x_17, x_23, x_24, x_1, x_3, x_4, x_5, x_6, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_26);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = l_Lean_Meta_Rewrites_solveByElim___lambda__3___closed__2;
x_35 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_34, x_3, x_4, x_5, x_6, x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Rewrites_solveByElim___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_Rewrites_solveByElim___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Rewrites_solveByElim___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Rewrites_solveByElim___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_solveByElim___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Rewrites_solveByElim___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_Rewrites_rwLemma___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("symm", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__2;
x_2 = l_Lean_Meta_Rewrites_rwLemma___lambda__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_3 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Rewrites_rewriteResultLemma(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_15, x_4, x_5, x_6, x_7, x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_Rewrites_rwLemma___lambda__1___closed__2;
x_20 = lean_unsigned_to_nat(4u);
x_21 = l_Lean_Expr_isAppOfArity(x_17, x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_st_ref_get(x_5, x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_inc(x_25);
x_27 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_25, x_26, x_4, x_5, x_6, x_7, x_24);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = 0;
x_31 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set(x_31, 2, x_1);
lean_ctor_set(x_31, 3, x_25);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
x_32 = lean_unbox(x_29);
lean_dec(x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4 + 1, x_32);
lean_ctor_set(x_11, 0, x_31);
lean_ctor_set(x_27, 0, x_11);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = 0;
x_36 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_2);
lean_ctor_set(x_36, 2, x_1);
lean_ctor_set(x_36, 3, x_25);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_35);
x_37 = lean_unbox(x_33);
lean_dec(x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*4 + 1, x_37);
lean_ctor_set(x_11, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_11);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_25);
lean_dec(x_17);
lean_free_object(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
return x_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_43 = lean_unsigned_to_nat(0u);
x_44 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_17, x_43);
x_45 = lean_unsigned_to_nat(3u);
x_46 = lean_nat_sub(x_44, x_45);
lean_dec(x_44);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_46, x_47);
lean_dec(x_46);
x_49 = l_Lean_Expr_getRevArg_x21(x_17, x_48);
lean_dec(x_17);
x_50 = lean_st_ref_get(x_5, x_18);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
lean_inc(x_53);
x_55 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_53, x_54, x_4, x_5, x_6, x_7, x_52);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = 1;
x_59 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_2);
lean_ctor_set(x_59, 2, x_1);
lean_ctor_set(x_59, 3, x_53);
lean_ctor_set_uint8(x_59, sizeof(void*)*4, x_58);
x_60 = lean_unbox(x_57);
lean_dec(x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*4 + 1, x_60);
lean_ctor_set(x_11, 0, x_59);
lean_ctor_set(x_55, 0, x_11);
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = 1;
x_64 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_64, 0, x_49);
lean_ctor_set(x_64, 1, x_2);
lean_ctor_set(x_64, 2, x_1);
lean_ctor_set(x_64, 3, x_53);
lean_ctor_set_uint8(x_64, sizeof(void*)*4, x_63);
x_65 = lean_unbox(x_61);
lean_dec(x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 1, x_65);
lean_ctor_set(x_11, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_11);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_53);
lean_dec(x_49);
lean_free_object(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_55);
if (x_67 == 0)
{
return x_55;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_55, 0);
x_69 = lean_ctor_get(x_55, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_55);
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
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_71 = lean_ctor_get(x_11, 0);
lean_inc(x_71);
lean_dec(x_11);
x_72 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_71, x_4, x_5, x_6, x_7, x_8);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Meta_Rewrites_rwLemma___lambda__1___closed__2;
x_76 = lean_unsigned_to_nat(4u);
x_77 = l_Lean_Expr_isAppOfArity(x_73, x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_st_ref_get(x_5, x_74);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_1, 0);
lean_inc(x_82);
lean_inc(x_81);
x_83 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_81, x_82, x_4, x_5, x_6, x_7, x_80);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = 0;
x_88 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_88, 0, x_73);
lean_ctor_set(x_88, 1, x_2);
lean_ctor_set(x_88, 2, x_1);
lean_ctor_set(x_88, 3, x_81);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_87);
x_89 = lean_unbox(x_84);
lean_dec(x_84);
lean_ctor_set_uint8(x_88, sizeof(void*)*4 + 1, x_89);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_88);
if (lean_is_scalar(x_86)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_86;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_85);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_2);
lean_dec(x_1);
x_92 = lean_ctor_get(x_83, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_83, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_94 = x_83;
} else {
 lean_dec_ref(x_83);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_96 = lean_unsigned_to_nat(0u);
x_97 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_73, x_96);
x_98 = lean_unsigned_to_nat(3u);
x_99 = lean_nat_sub(x_97, x_98);
lean_dec(x_97);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_sub(x_99, x_100);
lean_dec(x_99);
x_102 = l_Lean_Expr_getRevArg_x21(x_73, x_101);
lean_dec(x_73);
x_103 = lean_st_ref_get(x_5, x_74);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_1, 0);
lean_inc(x_107);
lean_inc(x_106);
x_108 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_106, x_107, x_4, x_5, x_6, x_7, x_105);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
x_112 = 1;
x_113 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_113, 0, x_102);
lean_ctor_set(x_113, 1, x_2);
lean_ctor_set(x_113, 2, x_1);
lean_ctor_set(x_113, 3, x_106);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_112);
x_114 = lean_unbox(x_109);
lean_dec(x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*4 + 1, x_114);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_113);
if (lean_is_scalar(x_111)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_111;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_110);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_106);
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_117 = lean_ctor_get(x_108, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_108, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_119 = x_108;
} else {
 lean_dec_ref(x_108);
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
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lambda__2___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = 2;
x_2 = 1;
x_3 = lean_box(0);
x_4 = 0;
x_5 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 1, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = l_Lean_Meta_saveState___rarg(x_9, x_10, x_11, x_12);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lean_Meta_Rewrites_rwLemma___lambda__2___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_161 = l_Lean_MVarId_rewrite(x_5, x_6, x_3, x_4, x_160, x_8, x_9, x_10, x_11, x_159);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_158);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_162);
x_13 = x_164;
x_14 = x_163;
goto block_156;
}
else
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_161);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = lean_ctor_get(x_161, 0);
x_167 = lean_ctor_get(x_161, 1);
x_168 = l_Lean_Exception_isInterrupt(x_166);
if (x_168 == 0)
{
uint8_t x_169; 
x_169 = l_Lean_Exception_isRuntime(x_166);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_free_object(x_161);
lean_dec(x_166);
x_170 = l_Lean_Meta_SavedState_restore(x_158, x_8, x_9, x_10, x_11, x_167);
lean_dec(x_158);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_172 = lean_box(0);
x_13 = x_172;
x_14 = x_171;
goto block_156;
}
else
{
lean_dec(x_158);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_161;
}
}
else
{
lean_dec(x_158);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_161;
}
}
else
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_173 = lean_ctor_get(x_161, 0);
x_174 = lean_ctor_get(x_161, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_161);
x_175 = l_Lean_Exception_isInterrupt(x_173);
if (x_175 == 0)
{
uint8_t x_176; 
x_176 = l_Lean_Exception_isRuntime(x_173);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_173);
x_177 = l_Lean_Meta_SavedState_restore(x_158, x_8, x_9, x_10, x_11, x_174);
lean_dec(x_158);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_179 = lean_box(0);
x_13 = x_179;
x_14 = x_178;
goto block_156;
}
else
{
lean_object* x_180; 
lean_dec(x_158);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_173);
lean_ctor_set(x_180, 1, x_174);
return x_180;
}
}
else
{
lean_object* x_181; 
lean_dec(x_158);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_173);
lean_ctor_set(x_181, 1, x_174);
return x_181;
}
}
}
block_156:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
x_20 = l_List_isEmpty___rarg(x_19);
if (x_20 == 0)
{
lean_free_object(x_13);
lean_dec(x_3);
switch (x_2) {
case 0:
{
uint8_t x_21; lean_object* x_22; 
lean_dec(x_19);
x_21 = 0;
x_22 = l_Lean_Meta_Rewrites_rwLemma___lambda__1(x_18, x_1, x_21, x_8, x_9, x_10, x_11, x_14);
return x_22;
}
case 1:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_box(0);
x_24 = l_Lean_Meta_saveState___rarg(x_9, x_10, x_11, x_14);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_27 = l_List_mapM_loop___at_Lean_Meta_Rewrites_rwLemma___spec__1(x_19, x_23, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = 1;
x_30 = l_Lean_Meta_Rewrites_rwLemma___lambda__1(x_18, x_1, x_29, x_8, x_9, x_10, x_11, x_28);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
x_34 = l_Lean_Exception_isInterrupt(x_32);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Exception_isRuntime(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
lean_free_object(x_27);
lean_dec(x_32);
x_36 = l_Lean_Meta_SavedState_restore(x_25, x_8, x_9, x_10, x_11, x_33);
lean_dec(x_25);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = 0;
x_39 = l_Lean_Meta_Rewrites_rwLemma___lambda__1(x_18, x_1, x_38, x_8, x_9, x_10, x_11, x_37);
return x_39;
}
else
{
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_27;
}
}
else
{
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_27;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
x_42 = l_Lean_Exception_isInterrupt(x_40);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Exception_isRuntime(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
lean_dec(x_40);
x_44 = l_Lean_Meta_SavedState_restore(x_25, x_8, x_9, x_10, x_11, x_41);
lean_dec(x_25);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = 0;
x_47 = l_Lean_Meta_Rewrites_rwLemma___lambda__1(x_18, x_1, x_46, x_8, x_9, x_10, x_11, x_45);
return x_47;
}
else
{
lean_object* x_48; 
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_41);
return x_48;
}
}
else
{
lean_object* x_49; 
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_41);
return x_49;
}
}
}
}
default: 
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = l_Lean_Meta_saveState___rarg(x_9, x_10, x_11, x_14);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unsigned_to_nat(6u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_54 = l_Lean_Meta_Rewrites_solveByElim(x_19, x_53, x_8, x_9, x_10, x_11, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; 
lean_dec(x_51);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = 1;
x_57 = l_Lean_Meta_Rewrites_rwLemma___lambda__1(x_18, x_1, x_56, x_8, x_9, x_10, x_11, x_55);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_54, 0);
x_60 = lean_ctor_get(x_54, 1);
x_61 = l_Lean_Exception_isInterrupt(x_59);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = l_Lean_Exception_isRuntime(x_59);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
lean_free_object(x_54);
lean_dec(x_59);
x_63 = l_Lean_Meta_SavedState_restore(x_51, x_8, x_9, x_10, x_11, x_60);
lean_dec(x_51);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = 0;
x_66 = l_Lean_Meta_Rewrites_rwLemma___lambda__1(x_18, x_1, x_65, x_8, x_9, x_10, x_11, x_64);
return x_66;
}
else
{
lean_dec(x_51);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_54;
}
}
else
{
lean_dec(x_51);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_54;
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_54, 0);
x_68 = lean_ctor_get(x_54, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_54);
x_69 = l_Lean_Exception_isInterrupt(x_67);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Exception_isRuntime(x_67);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
lean_dec(x_67);
x_71 = l_Lean_Meta_SavedState_restore(x_51, x_8, x_9, x_10, x_11, x_68);
lean_dec(x_51);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = 0;
x_74 = l_Lean_Meta_Rewrites_rwLemma___lambda__1(x_18, x_1, x_73, x_8, x_9, x_10, x_11, x_72);
return x_74;
}
else
{
lean_object* x_75; 
lean_dec(x_51);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_68);
return x_75;
}
}
else
{
lean_object* x_76; 
lean_dec(x_51);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_68);
return x_76;
}
}
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_19);
x_77 = lean_st_ref_get(x_9, x_14);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_18, 0);
lean_inc(x_81);
lean_inc(x_80);
x_82 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_80, x_81, x_8, x_9, x_10, x_11, x_79);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_85, 0, x_3);
lean_ctor_set(x_85, 1, x_1);
lean_ctor_set(x_85, 2, x_18);
lean_ctor_set(x_85, 3, x_80);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_4);
x_86 = lean_unbox(x_84);
lean_dec(x_84);
lean_ctor_set_uint8(x_85, sizeof(void*)*4 + 1, x_86);
lean_ctor_set(x_13, 0, x_85);
lean_ctor_set(x_82, 0, x_13);
return x_82;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_82, 0);
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_82);
x_89 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_89, 0, x_3);
lean_ctor_set(x_89, 1, x_1);
lean_ctor_set(x_89, 2, x_18);
lean_ctor_set(x_89, 3, x_80);
lean_ctor_set_uint8(x_89, sizeof(void*)*4, x_4);
x_90 = lean_unbox(x_87);
lean_dec(x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*4 + 1, x_90);
lean_ctor_set(x_13, 0, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_13);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
}
else
{
uint8_t x_92; 
lean_dec(x_80);
lean_free_object(x_13);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_82);
if (x_92 == 0)
{
return x_82;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_82, 0);
x_94 = lean_ctor_get(x_82, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_82);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_13, 0);
lean_inc(x_96);
lean_dec(x_13);
x_97 = lean_ctor_get(x_96, 2);
lean_inc(x_97);
x_98 = l_List_isEmpty___rarg(x_97);
if (x_98 == 0)
{
lean_dec(x_3);
switch (x_2) {
case 0:
{
uint8_t x_99; lean_object* x_100; 
lean_dec(x_97);
x_99 = 0;
x_100 = l_Lean_Meta_Rewrites_rwLemma___lambda__1(x_96, x_1, x_99, x_8, x_9, x_10, x_11, x_14);
return x_100;
}
case 1:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_box(0);
x_102 = l_Lean_Meta_saveState___rarg(x_9, x_10, x_11, x_14);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_105 = l_List_mapM_loop___at_Lean_Meta_Rewrites_rwLemma___spec__1(x_97, x_101, x_8, x_9, x_10, x_11, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; uint8_t x_107; lean_object* x_108; 
lean_dec(x_103);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = 1;
x_108 = l_Lean_Meta_Rewrites_rwLemma___lambda__1(x_96, x_1, x_107, x_8, x_9, x_10, x_11, x_106);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_105, 0);
lean_inc(x_109);
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
x_112 = l_Lean_Exception_isInterrupt(x_109);
if (x_112 == 0)
{
uint8_t x_113; 
x_113 = l_Lean_Exception_isRuntime(x_109);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; 
lean_dec(x_111);
lean_dec(x_109);
x_114 = l_Lean_Meta_SavedState_restore(x_103, x_8, x_9, x_10, x_11, x_110);
lean_dec(x_103);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = 0;
x_117 = l_Lean_Meta_Rewrites_rwLemma___lambda__1(x_96, x_1, x_116, x_8, x_9, x_10, x_11, x_115);
return x_117;
}
else
{
lean_object* x_118; 
lean_dec(x_103);
lean_dec(x_96);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
if (lean_is_scalar(x_111)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_111;
}
lean_ctor_set(x_118, 0, x_109);
lean_ctor_set(x_118, 1, x_110);
return x_118;
}
}
else
{
lean_object* x_119; 
lean_dec(x_103);
lean_dec(x_96);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
if (lean_is_scalar(x_111)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_111;
}
lean_ctor_set(x_119, 0, x_109);
lean_ctor_set(x_119, 1, x_110);
return x_119;
}
}
}
default: 
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = l_Lean_Meta_saveState___rarg(x_9, x_10, x_11, x_14);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_unsigned_to_nat(6u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_124 = l_Lean_Meta_Rewrites_solveByElim(x_97, x_123, x_8, x_9, x_10, x_11, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; uint8_t x_126; lean_object* x_127; 
lean_dec(x_121);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = 1;
x_127 = l_Lean_Meta_Rewrites_rwLemma___lambda__1(x_96, x_1, x_126, x_8, x_9, x_10, x_11, x_125);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_128 = lean_ctor_get(x_124, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_130 = x_124;
} else {
 lean_dec_ref(x_124);
 x_130 = lean_box(0);
}
x_131 = l_Lean_Exception_isInterrupt(x_128);
if (x_131 == 0)
{
uint8_t x_132; 
x_132 = l_Lean_Exception_isRuntime(x_128);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; 
lean_dec(x_130);
lean_dec(x_128);
x_133 = l_Lean_Meta_SavedState_restore(x_121, x_8, x_9, x_10, x_11, x_129);
lean_dec(x_121);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = 0;
x_136 = l_Lean_Meta_Rewrites_rwLemma___lambda__1(x_96, x_1, x_135, x_8, x_9, x_10, x_11, x_134);
return x_136;
}
else
{
lean_object* x_137; 
lean_dec(x_121);
lean_dec(x_96);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
if (lean_is_scalar(x_130)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_130;
}
lean_ctor_set(x_137, 0, x_128);
lean_ctor_set(x_137, 1, x_129);
return x_137;
}
}
else
{
lean_object* x_138; 
lean_dec(x_121);
lean_dec(x_96);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
if (lean_is_scalar(x_130)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_130;
}
lean_ctor_set(x_138, 0, x_128);
lean_ctor_set(x_138, 1, x_129);
return x_138;
}
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_97);
x_139 = lean_st_ref_get(x_9, x_14);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_ctor_get(x_96, 0);
lean_inc(x_143);
lean_inc(x_142);
x_144 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_142, x_143, x_8, x_9, x_10, x_11, x_141);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
x_148 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_148, 0, x_3);
lean_ctor_set(x_148, 1, x_1);
lean_ctor_set(x_148, 2, x_96);
lean_ctor_set(x_148, 3, x_142);
lean_ctor_set_uint8(x_148, sizeof(void*)*4, x_4);
x_149 = lean_unbox(x_145);
lean_dec(x_145);
lean_ctor_set_uint8(x_148, sizeof(void*)*4 + 1, x_149);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_148);
if (lean_is_scalar(x_147)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_147;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_146);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_142);
lean_dec(x_96);
lean_dec(x_3);
lean_dec(x_1);
x_152 = lean_ctor_get(x_144, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_144, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_154 = x_144;
} else {
 lean_dec_ref(x_144);
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
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("considering ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__2;
x_2 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__5;
x_2 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("← ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__2;
x_2 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__8;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__9;
x_2 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__3(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_6);
if (x_61 == 0)
{
lean_ctor_set_tag(x_6, 1);
x_12 = x_6;
x_13 = x_11;
goto block_60;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_6, 0);
lean_inc(x_62);
lean_dec(x_6);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_12 = x_63;
x_13 = x_11;
goto block_60;
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_6);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_6, 0);
x_66 = l_Lean_Meta_saveState___rarg(x_8, x_9, x_10, x_11);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_65, x_7, x_8, x_9, x_10, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_ctor_set(x_6, 0, x_70);
x_12 = x_6;
x_13 = x_71;
goto block_60;
}
else
{
uint8_t x_72; 
lean_free_object(x_6);
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
x_75 = l_Lean_Exception_isInterrupt(x_73);
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = l_Lean_Exception_isRuntime(x_73);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_free_object(x_69);
lean_dec(x_73);
x_77 = l_Lean_Meta_SavedState_restore(x_67, x_7, x_8, x_9, x_10, x_74);
lean_dec(x_67);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_box(0);
x_12 = x_79;
x_13 = x_78;
goto block_60;
}
else
{
lean_dec(x_67);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_69;
}
}
else
{
lean_dec(x_67);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_69;
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_69, 0);
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_69);
x_82 = l_Lean_Exception_isInterrupt(x_80);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = l_Lean_Exception_isRuntime(x_80);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_80);
x_84 = l_Lean_Meta_SavedState_restore(x_67, x_7, x_8, x_9, x_10, x_81);
lean_dec(x_67);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_box(0);
x_12 = x_86;
x_13 = x_85;
goto block_60;
}
else
{
lean_object* x_87; 
lean_dec(x_67);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_81);
return x_87;
}
}
else
{
lean_object* x_88; 
lean_dec(x_67);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_80);
lean_ctor_set(x_88, 1, x_81);
return x_88;
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_6, 0);
lean_inc(x_89);
lean_dec(x_6);
x_90 = l_Lean_Meta_saveState___rarg(x_8, x_9, x_10, x_11);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_89, x_7, x_8, x_9, x_10, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_91);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_94);
x_12 = x_96;
x_13 = x_95;
goto block_60;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_99 = x_93;
} else {
 lean_dec_ref(x_93);
 x_99 = lean_box(0);
}
x_100 = l_Lean_Exception_isInterrupt(x_97);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = l_Lean_Exception_isRuntime(x_97);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_99);
lean_dec(x_97);
x_102 = l_Lean_Meta_SavedState_restore(x_91, x_7, x_8, x_9, x_10, x_98);
lean_dec(x_91);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_box(0);
x_12 = x_104;
x_13 = x_103;
goto block_60;
}
else
{
lean_object* x_105; 
lean_dec(x_91);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_99)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_99;
}
lean_ctor_set(x_105, 0, x_97);
lean_ctor_set(x_105, 1, x_98);
return x_105;
}
}
else
{
lean_object* x_106; 
lean_dec(x_91);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_99)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_99;
}
lean_ctor_set(x_106, 0, x_97);
lean_ctor_set(x_106, 1, x_98);
return x_106;
}
}
}
}
block_60:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__3;
x_18 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_17, x_7, x_8, x_9, x_10, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Lean_Meta_Rewrites_rwLemma___lambda__2(x_1, x_2, x_16, x_3, x_4, x_5, x_22, x_7, x_8, x_9, x_10, x_21);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 1);
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
lean_inc(x_16);
x_27 = l_Lean_MessageData_ofExpr(x_16);
if (x_3 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__6;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_28);
x_29 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__4;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_17, x_30, x_7, x_8, x_9, x_10, x_25);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_Rewrites_rwLemma___lambda__2(x_1, x_2, x_16, x_3, x_4, x_5, x_32, x_7, x_8, x_9, x_10, x_33);
lean_dec(x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__10;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_35);
x_36 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__4;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_18);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_17, x_37, x_7, x_8, x_9, x_10, x_25);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_Rewrites_rwLemma___lambda__2(x_1, x_2, x_16, x_3, x_4, x_5, x_39, x_7, x_8, x_9, x_10, x_40);
lean_dec(x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_dec(x_18);
lean_inc(x_16);
x_43 = l_Lean_MessageData_ofExpr(x_16);
if (x_3 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__6;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__4;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_17, x_47, x_7, x_8, x_9, x_10, x_42);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Meta_Rewrites_rwLemma___lambda__2(x_1, x_2, x_16, x_3, x_4, x_5, x_49, x_7, x_8, x_9, x_10, x_50);
lean_dec(x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__10;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_43);
x_54 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__4;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_17, x_55, x_7, x_8, x_9, x_10, x_42);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Meta_Rewrites_rwLemma___lambda__2(x_1, x_2, x_16, x_3, x_4, x_5, x_57, x_7, x_8, x_9, x_10, x_58);
lean_dec(x_57);
return x_59;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(x_4);
x_14 = lean_box(x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___lambda__3___boxed), 11, 6);
lean_closure_set(x_15, 0, x_7);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_5);
x_16 = l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg(x_1, x_15, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_Rewrites_rwLemma___lambda__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Meta_Rewrites_rwLemma___lambda__2(x_1, x_13, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rwLemma___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Meta_Rewrites_rwLemma___lambda__3(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_11 = lean_apply_7(x_1, x_3, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_10);
x_14 = lean_apply_7(x_1, x_12, x_10, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ptr_addr(x_9);
x_18 = lean_usize_dec_eq(x_17, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = l_Lean_Expr_app___override(x_9, x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
size_t x_21; uint8_t x_22; 
x_21 = lean_ptr_addr(x_10);
x_22 = lean_usize_dec_eq(x_21, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = l_Lean_Expr_app___override(x_9, x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_ptr_addr(x_9);
x_29 = lean_usize_dec_eq(x_28, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = l_Lean_Expr_app___override(x_9, x_10);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
size_t x_33; uint8_t x_34; 
x_33 = lean_ptr_addr(x_10);
x_34 = lean_usize_dec_eq(x_33, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_35 = l_Lean_Expr_app___override(x_9, x_10);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_10);
lean_dec(x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_26);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_49);
x_52 = lean_apply_7(x_1, x_3, x_49, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_50);
x_55 = lean_apply_7(x_1, x_53, x_50, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_55, 0, x_59);
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
return x_55;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_55, 0);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_55);
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
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_52);
if (x_69 == 0)
{
return x_52;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_52, 0);
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_52);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
case 7:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 2);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_74);
x_77 = lean_apply_7(x_1, x_3, x_74, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_75);
x_80 = lean_apply_7(x_1, x_78, x_75, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_80, 0, x_84);
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_80, 0);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_80);
x_87 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
x_90 = !lean_is_exclusive(x_80);
if (x_90 == 0)
{
return x_80;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_80, 0);
x_92 = lean_ctor_get(x_80, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_80);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_77);
if (x_94 == 0)
{
return x_77;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_77, 0);
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_77);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_99);
x_103 = lean_apply_7(x_1, x_3, x_99, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_100);
x_106 = lean_apply_7(x_1, x_104, x_100, x_4, x_5, x_6, x_7, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_101);
x_109 = lean_apply_7(x_1, x_107, x_101, x_4, x_5, x_6, x_7, x_108);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; size_t x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ptr_addr(x_99);
x_113 = lean_usize_dec_eq(x_112, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_2);
x_114 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
lean_ctor_set(x_109, 0, x_115);
return x_109;
}
else
{
size_t x_116; uint8_t x_117; 
x_116 = lean_ptr_addr(x_100);
x_117 = lean_usize_dec_eq(x_116, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_2);
x_118 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
lean_ctor_set(x_109, 0, x_119);
return x_109;
}
else
{
size_t x_120; uint8_t x_121; 
x_120 = lean_ptr_addr(x_101);
x_121 = lean_usize_dec_eq(x_120, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_2);
x_122 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_111);
lean_ctor_set(x_109, 0, x_123);
return x_109;
}
else
{
lean_object* x_124; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_2);
lean_ctor_set(x_124, 1, x_111);
lean_ctor_set(x_109, 0, x_124);
return x_109;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; size_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_109, 0);
x_126 = lean_ctor_get(x_109, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_109);
x_127 = lean_ptr_addr(x_99);
x_128 = lean_usize_dec_eq(x_127, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_2);
x_129 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_126);
return x_131;
}
else
{
size_t x_132; uint8_t x_133; 
x_132 = lean_ptr_addr(x_100);
x_133 = lean_usize_dec_eq(x_132, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_2);
x_134 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_125);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_126);
return x_136;
}
else
{
size_t x_137; uint8_t x_138; 
x_137 = lean_ptr_addr(x_101);
x_138 = lean_usize_dec_eq(x_137, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_2);
x_139 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_125);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_126);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_2);
lean_ctor_set(x_142, 1, x_125);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_126);
return x_143;
}
}
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_109);
if (x_144 == 0)
{
return x_109;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_109, 0);
x_146 = lean_ctor_get(x_109, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_109);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
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
x_148 = !lean_is_exclusive(x_106);
if (x_148 == 0)
{
return x_106;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_106, 0);
x_150 = lean_ctor_get(x_106, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_106);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
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
x_152 = !lean_is_exclusive(x_103);
if (x_152 == 0)
{
return x_103;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_103, 0);
x_154 = lean_ctor_get(x_103, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_103);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
case 10:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_2, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_2, 1);
lean_inc(x_157);
lean_inc(x_157);
x_158 = lean_apply_7(x_1, x_3, x_157, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; size_t x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = lean_ptr_addr(x_157);
x_162 = lean_usize_dec_eq(x_161, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_2);
x_163 = l_Lean_Expr_mdata___override(x_156, x_157);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set(x_158, 0, x_164);
return x_158;
}
else
{
lean_object* x_165; 
lean_dec(x_157);
lean_dec(x_156);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_2);
lean_ctor_set(x_165, 1, x_160);
lean_ctor_set(x_158, 0, x_165);
return x_158;
}
}
else
{
lean_object* x_166; lean_object* x_167; size_t x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_158, 0);
x_167 = lean_ctor_get(x_158, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_158);
x_168 = lean_ptr_addr(x_157);
x_169 = lean_usize_dec_eq(x_168, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_2);
x_170 = l_Lean_Expr_mdata___override(x_156, x_157);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_166);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_167);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_157);
lean_dec(x_156);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_2);
lean_ctor_set(x_173, 1, x_166);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_167);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_158);
if (x_175 == 0)
{
return x_158;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_158, 0);
x_177 = lean_ctor_get(x_158, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_158);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
case 11:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_2, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_2, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_2, 2);
lean_inc(x_181);
lean_inc(x_181);
x_182 = lean_apply_7(x_1, x_3, x_181, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; size_t x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_182, 0);
x_185 = lean_ptr_addr(x_181);
x_186 = lean_usize_dec_eq(x_185, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_2);
x_187 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_182, 0, x_188);
return x_182;
}
else
{
lean_object* x_189; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_2);
lean_ctor_set(x_189, 1, x_184);
lean_ctor_set(x_182, 0, x_189);
return x_182;
}
}
else
{
lean_object* x_190; lean_object* x_191; size_t x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_182, 0);
x_191 = lean_ctor_get(x_182, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_182);
x_192 = lean_ptr_addr(x_181);
x_193 = lean_usize_dec_eq(x_192, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_2);
x_194 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_190);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_191);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_2);
lean_ctor_set(x_197, 1, x_190);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_191);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_2);
x_199 = !lean_is_exclusive(x_182);
if (x_199 == 0)
{
return x_182;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_182, 0);
x_201 = lean_ctor_get(x_182, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_182);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
default: 
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_2);
lean_ctor_set(x_203, 1, x_3);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_8);
return x_204;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__2___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__2___rarg(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__1___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_11 = lean_apply_7(x_1, x_3, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_10);
x_14 = lean_apply_7(x_1, x_12, x_10, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ptr_addr(x_9);
x_18 = lean_usize_dec_eq(x_17, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = l_Lean_Expr_app___override(x_9, x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
size_t x_21; uint8_t x_22; 
x_21 = lean_ptr_addr(x_10);
x_22 = lean_usize_dec_eq(x_21, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = l_Lean_Expr_app___override(x_9, x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_ptr_addr(x_9);
x_29 = lean_usize_dec_eq(x_28, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = l_Lean_Expr_app___override(x_9, x_10);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
size_t x_33; uint8_t x_34; 
x_33 = lean_ptr_addr(x_10);
x_34 = lean_usize_dec_eq(x_33, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_35 = l_Lean_Expr_app___override(x_9, x_10);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_10);
lean_dec(x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_26);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_49);
x_52 = lean_apply_7(x_1, x_3, x_49, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_50);
x_55 = lean_apply_7(x_1, x_53, x_50, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_55, 0, x_59);
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
return x_55;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_55, 0);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_55);
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
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_52);
if (x_69 == 0)
{
return x_52;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_52, 0);
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_52);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
case 7:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 2);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_74);
x_77 = lean_apply_7(x_1, x_3, x_74, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_75);
x_80 = lean_apply_7(x_1, x_78, x_75, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_80, 0, x_84);
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_80, 0);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_80);
x_87 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
x_90 = !lean_is_exclusive(x_80);
if (x_90 == 0)
{
return x_80;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_80, 0);
x_92 = lean_ctor_get(x_80, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_80);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_77);
if (x_94 == 0)
{
return x_77;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_77, 0);
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_77);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_99);
x_103 = lean_apply_7(x_1, x_3, x_99, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_100);
x_106 = lean_apply_7(x_1, x_104, x_100, x_4, x_5, x_6, x_7, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_101);
x_109 = lean_apply_7(x_1, x_107, x_101, x_4, x_5, x_6, x_7, x_108);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; size_t x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ptr_addr(x_99);
x_113 = lean_usize_dec_eq(x_112, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_2);
x_114 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
lean_ctor_set(x_109, 0, x_115);
return x_109;
}
else
{
size_t x_116; uint8_t x_117; 
x_116 = lean_ptr_addr(x_100);
x_117 = lean_usize_dec_eq(x_116, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_2);
x_118 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
lean_ctor_set(x_109, 0, x_119);
return x_109;
}
else
{
size_t x_120; uint8_t x_121; 
x_120 = lean_ptr_addr(x_101);
x_121 = lean_usize_dec_eq(x_120, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_2);
x_122 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_111);
lean_ctor_set(x_109, 0, x_123);
return x_109;
}
else
{
lean_object* x_124; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_2);
lean_ctor_set(x_124, 1, x_111);
lean_ctor_set(x_109, 0, x_124);
return x_109;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; size_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_109, 0);
x_126 = lean_ctor_get(x_109, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_109);
x_127 = lean_ptr_addr(x_99);
x_128 = lean_usize_dec_eq(x_127, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_2);
x_129 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_126);
return x_131;
}
else
{
size_t x_132; uint8_t x_133; 
x_132 = lean_ptr_addr(x_100);
x_133 = lean_usize_dec_eq(x_132, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_2);
x_134 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_125);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_126);
return x_136;
}
else
{
size_t x_137; uint8_t x_138; 
x_137 = lean_ptr_addr(x_101);
x_138 = lean_usize_dec_eq(x_137, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_2);
x_139 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_125);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_126);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_2);
lean_ctor_set(x_142, 1, x_125);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_126);
return x_143;
}
}
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_109);
if (x_144 == 0)
{
return x_109;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_109, 0);
x_146 = lean_ctor_get(x_109, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_109);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
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
x_148 = !lean_is_exclusive(x_106);
if (x_148 == 0)
{
return x_106;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_106, 0);
x_150 = lean_ctor_get(x_106, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_106);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
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
x_152 = !lean_is_exclusive(x_103);
if (x_152 == 0)
{
return x_103;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_103, 0);
x_154 = lean_ctor_get(x_103, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_103);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
case 10:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_2, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_2, 1);
lean_inc(x_157);
lean_inc(x_157);
x_158 = lean_apply_7(x_1, x_3, x_157, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; size_t x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = lean_ptr_addr(x_157);
x_162 = lean_usize_dec_eq(x_161, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_2);
x_163 = l_Lean_Expr_mdata___override(x_156, x_157);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set(x_158, 0, x_164);
return x_158;
}
else
{
lean_object* x_165; 
lean_dec(x_157);
lean_dec(x_156);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_2);
lean_ctor_set(x_165, 1, x_160);
lean_ctor_set(x_158, 0, x_165);
return x_158;
}
}
else
{
lean_object* x_166; lean_object* x_167; size_t x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_158, 0);
x_167 = lean_ctor_get(x_158, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_158);
x_168 = lean_ptr_addr(x_157);
x_169 = lean_usize_dec_eq(x_168, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_2);
x_170 = l_Lean_Expr_mdata___override(x_156, x_157);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_166);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_167);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_157);
lean_dec(x_156);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_2);
lean_ctor_set(x_173, 1, x_166);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_167);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_158);
if (x_175 == 0)
{
return x_158;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_158, 0);
x_177 = lean_ctor_get(x_158, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_158);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
case 11:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_2, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_2, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_2, 2);
lean_inc(x_181);
lean_inc(x_181);
x_182 = lean_apply_7(x_1, x_3, x_181, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; size_t x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_182, 0);
x_185 = lean_ptr_addr(x_181);
x_186 = lean_usize_dec_eq(x_185, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_2);
x_187 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_182, 0, x_188);
return x_182;
}
else
{
lean_object* x_189; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_2);
lean_ctor_set(x_189, 1, x_184);
lean_ctor_set(x_182, 0, x_189);
return x_182;
}
}
else
{
lean_object* x_190; lean_object* x_191; size_t x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_182, 0);
x_191 = lean_ctor_get(x_182, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_182);
x_192 = lean_ptr_addr(x_181);
x_193 = lean_usize_dec_eq(x_192, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_2);
x_194 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_190);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_191);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_2);
lean_ctor_set(x_197, 1, x_190);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_191);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_2);
x_199 = !lean_is_exclusive(x_182);
if (x_199 == 0)
{
return x_182;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_182, 0);
x_201 = lean_ctor_get(x_182, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_182);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
default: 
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_2);
lean_ctor_set(x_203, 1, x_3);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_8);
return x_204;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__4___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__4___rarg(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__3___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_11 = lean_apply_7(x_1, x_3, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_10);
x_14 = lean_apply_7(x_1, x_12, x_10, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ptr_addr(x_9);
x_18 = lean_usize_dec_eq(x_17, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = l_Lean_Expr_app___override(x_9, x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
size_t x_21; uint8_t x_22; 
x_21 = lean_ptr_addr(x_10);
x_22 = lean_usize_dec_eq(x_21, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = l_Lean_Expr_app___override(x_9, x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_ptr_addr(x_9);
x_29 = lean_usize_dec_eq(x_28, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = l_Lean_Expr_app___override(x_9, x_10);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
size_t x_33; uint8_t x_34; 
x_33 = lean_ptr_addr(x_10);
x_34 = lean_usize_dec_eq(x_33, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_35 = l_Lean_Expr_app___override(x_9, x_10);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_10);
lean_dec(x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_26);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_49);
x_52 = lean_apply_7(x_1, x_3, x_49, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_50);
x_55 = lean_apply_7(x_1, x_53, x_50, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_55, 0, x_59);
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
return x_55;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_55, 0);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_55);
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
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_52);
if (x_69 == 0)
{
return x_52;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_52, 0);
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_52);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
case 7:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 2);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_74);
x_77 = lean_apply_7(x_1, x_3, x_74, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_75);
x_80 = lean_apply_7(x_1, x_78, x_75, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_80, 0, x_84);
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_80, 0);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_80);
x_87 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
x_90 = !lean_is_exclusive(x_80);
if (x_90 == 0)
{
return x_80;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_80, 0);
x_92 = lean_ctor_get(x_80, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_80);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_77);
if (x_94 == 0)
{
return x_77;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_77, 0);
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_77);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_99);
x_103 = lean_apply_7(x_1, x_3, x_99, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_100);
x_106 = lean_apply_7(x_1, x_104, x_100, x_4, x_5, x_6, x_7, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_101);
x_109 = lean_apply_7(x_1, x_107, x_101, x_4, x_5, x_6, x_7, x_108);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; size_t x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ptr_addr(x_99);
x_113 = lean_usize_dec_eq(x_112, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_2);
x_114 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
lean_ctor_set(x_109, 0, x_115);
return x_109;
}
else
{
size_t x_116; uint8_t x_117; 
x_116 = lean_ptr_addr(x_100);
x_117 = lean_usize_dec_eq(x_116, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_2);
x_118 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
lean_ctor_set(x_109, 0, x_119);
return x_109;
}
else
{
size_t x_120; uint8_t x_121; 
x_120 = lean_ptr_addr(x_101);
x_121 = lean_usize_dec_eq(x_120, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_2);
x_122 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_111);
lean_ctor_set(x_109, 0, x_123);
return x_109;
}
else
{
lean_object* x_124; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_2);
lean_ctor_set(x_124, 1, x_111);
lean_ctor_set(x_109, 0, x_124);
return x_109;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; size_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_109, 0);
x_126 = lean_ctor_get(x_109, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_109);
x_127 = lean_ptr_addr(x_99);
x_128 = lean_usize_dec_eq(x_127, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_2);
x_129 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_126);
return x_131;
}
else
{
size_t x_132; uint8_t x_133; 
x_132 = lean_ptr_addr(x_100);
x_133 = lean_usize_dec_eq(x_132, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_2);
x_134 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_125);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_126);
return x_136;
}
else
{
size_t x_137; uint8_t x_138; 
x_137 = lean_ptr_addr(x_101);
x_138 = lean_usize_dec_eq(x_137, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_2);
x_139 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_125);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_126);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_2);
lean_ctor_set(x_142, 1, x_125);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_126);
return x_143;
}
}
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_109);
if (x_144 == 0)
{
return x_109;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_109, 0);
x_146 = lean_ctor_get(x_109, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_109);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
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
x_148 = !lean_is_exclusive(x_106);
if (x_148 == 0)
{
return x_106;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_106, 0);
x_150 = lean_ctor_get(x_106, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_106);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
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
x_152 = !lean_is_exclusive(x_103);
if (x_152 == 0)
{
return x_103;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_103, 0);
x_154 = lean_ctor_get(x_103, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_103);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
case 10:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_2, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_2, 1);
lean_inc(x_157);
lean_inc(x_157);
x_158 = lean_apply_7(x_1, x_3, x_157, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; size_t x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = lean_ptr_addr(x_157);
x_162 = lean_usize_dec_eq(x_161, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_2);
x_163 = l_Lean_Expr_mdata___override(x_156, x_157);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set(x_158, 0, x_164);
return x_158;
}
else
{
lean_object* x_165; 
lean_dec(x_157);
lean_dec(x_156);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_2);
lean_ctor_set(x_165, 1, x_160);
lean_ctor_set(x_158, 0, x_165);
return x_158;
}
}
else
{
lean_object* x_166; lean_object* x_167; size_t x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_158, 0);
x_167 = lean_ctor_get(x_158, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_158);
x_168 = lean_ptr_addr(x_157);
x_169 = lean_usize_dec_eq(x_168, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_2);
x_170 = l_Lean_Expr_mdata___override(x_156, x_157);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_166);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_167);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_157);
lean_dec(x_156);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_2);
lean_ctor_set(x_173, 1, x_166);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_167);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_158);
if (x_175 == 0)
{
return x_158;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_158, 0);
x_177 = lean_ctor_get(x_158, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_158);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
case 11:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_2, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_2, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_2, 2);
lean_inc(x_181);
lean_inc(x_181);
x_182 = lean_apply_7(x_1, x_3, x_181, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; size_t x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_182, 0);
x_185 = lean_ptr_addr(x_181);
x_186 = lean_usize_dec_eq(x_185, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_2);
x_187 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_182, 0, x_188);
return x_182;
}
else
{
lean_object* x_189; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_2);
lean_ctor_set(x_189, 1, x_184);
lean_ctor_set(x_182, 0, x_189);
return x_182;
}
}
else
{
lean_object* x_190; lean_object* x_191; size_t x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_182, 0);
x_191 = lean_ctor_get(x_182, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_182);
x_192 = lean_ptr_addr(x_181);
x_193 = lean_usize_dec_eq(x_192, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_2);
x_194 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_190);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_191);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_2);
lean_ctor_set(x_197, 1, x_190);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_191);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_2);
x_199 = !lean_is_exclusive(x_182);
if (x_199 == 0)
{
return x_182;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_182, 0);
x_201 = lean_ctor_get(x_182, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_182);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
default: 
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_2);
lean_ctor_set(x_203, 1, x_3);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_8);
return x_204;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__6___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__6___rarg(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__5___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_11 = lean_apply_7(x_1, x_3, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_10);
x_14 = lean_apply_7(x_1, x_12, x_10, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ptr_addr(x_9);
x_18 = lean_usize_dec_eq(x_17, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = l_Lean_Expr_app___override(x_9, x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
size_t x_21; uint8_t x_22; 
x_21 = lean_ptr_addr(x_10);
x_22 = lean_usize_dec_eq(x_21, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = l_Lean_Expr_app___override(x_9, x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_ptr_addr(x_9);
x_29 = lean_usize_dec_eq(x_28, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = l_Lean_Expr_app___override(x_9, x_10);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
size_t x_33; uint8_t x_34; 
x_33 = lean_ptr_addr(x_10);
x_34 = lean_usize_dec_eq(x_33, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_35 = l_Lean_Expr_app___override(x_9, x_10);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_10);
lean_dec(x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_26);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_49);
x_52 = lean_apply_7(x_1, x_3, x_49, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_50);
x_55 = lean_apply_7(x_1, x_53, x_50, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_55, 0, x_59);
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
return x_55;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_55, 0);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_55);
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
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_52);
if (x_69 == 0)
{
return x_52;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_52, 0);
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_52);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
case 7:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 2);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_74);
x_77 = lean_apply_7(x_1, x_3, x_74, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_75);
x_80 = lean_apply_7(x_1, x_78, x_75, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_80, 0, x_84);
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_80, 0);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_80);
x_87 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
x_90 = !lean_is_exclusive(x_80);
if (x_90 == 0)
{
return x_80;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_80, 0);
x_92 = lean_ctor_get(x_80, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_80);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_77);
if (x_94 == 0)
{
return x_77;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_77, 0);
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_77);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_99);
x_103 = lean_apply_7(x_1, x_3, x_99, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_100);
x_106 = lean_apply_7(x_1, x_104, x_100, x_4, x_5, x_6, x_7, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_101);
x_109 = lean_apply_7(x_1, x_107, x_101, x_4, x_5, x_6, x_7, x_108);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; size_t x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ptr_addr(x_99);
x_113 = lean_usize_dec_eq(x_112, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_2);
x_114 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
lean_ctor_set(x_109, 0, x_115);
return x_109;
}
else
{
size_t x_116; uint8_t x_117; 
x_116 = lean_ptr_addr(x_100);
x_117 = lean_usize_dec_eq(x_116, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_2);
x_118 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
lean_ctor_set(x_109, 0, x_119);
return x_109;
}
else
{
size_t x_120; uint8_t x_121; 
x_120 = lean_ptr_addr(x_101);
x_121 = lean_usize_dec_eq(x_120, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_2);
x_122 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_111);
lean_ctor_set(x_109, 0, x_123);
return x_109;
}
else
{
lean_object* x_124; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_2);
lean_ctor_set(x_124, 1, x_111);
lean_ctor_set(x_109, 0, x_124);
return x_109;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; size_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_109, 0);
x_126 = lean_ctor_get(x_109, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_109);
x_127 = lean_ptr_addr(x_99);
x_128 = lean_usize_dec_eq(x_127, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_2);
x_129 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_126);
return x_131;
}
else
{
size_t x_132; uint8_t x_133; 
x_132 = lean_ptr_addr(x_100);
x_133 = lean_usize_dec_eq(x_132, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_2);
x_134 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_125);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_126);
return x_136;
}
else
{
size_t x_137; uint8_t x_138; 
x_137 = lean_ptr_addr(x_101);
x_138 = lean_usize_dec_eq(x_137, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_2);
x_139 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_125);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_126);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_2);
lean_ctor_set(x_142, 1, x_125);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_126);
return x_143;
}
}
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_109);
if (x_144 == 0)
{
return x_109;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_109, 0);
x_146 = lean_ctor_get(x_109, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_109);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
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
x_148 = !lean_is_exclusive(x_106);
if (x_148 == 0)
{
return x_106;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_106, 0);
x_150 = lean_ctor_get(x_106, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_106);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
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
x_152 = !lean_is_exclusive(x_103);
if (x_152 == 0)
{
return x_103;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_103, 0);
x_154 = lean_ctor_get(x_103, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_103);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
case 10:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_2, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_2, 1);
lean_inc(x_157);
lean_inc(x_157);
x_158 = lean_apply_7(x_1, x_3, x_157, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; size_t x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = lean_ptr_addr(x_157);
x_162 = lean_usize_dec_eq(x_161, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_2);
x_163 = l_Lean_Expr_mdata___override(x_156, x_157);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set(x_158, 0, x_164);
return x_158;
}
else
{
lean_object* x_165; 
lean_dec(x_157);
lean_dec(x_156);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_2);
lean_ctor_set(x_165, 1, x_160);
lean_ctor_set(x_158, 0, x_165);
return x_158;
}
}
else
{
lean_object* x_166; lean_object* x_167; size_t x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_158, 0);
x_167 = lean_ctor_get(x_158, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_158);
x_168 = lean_ptr_addr(x_157);
x_169 = lean_usize_dec_eq(x_168, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_2);
x_170 = l_Lean_Expr_mdata___override(x_156, x_157);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_166);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_167);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_157);
lean_dec(x_156);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_2);
lean_ctor_set(x_173, 1, x_166);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_167);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_158);
if (x_175 == 0)
{
return x_158;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_158, 0);
x_177 = lean_ctor_get(x_158, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_158);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
case 11:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_2, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_2, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_2, 2);
lean_inc(x_181);
lean_inc(x_181);
x_182 = lean_apply_7(x_1, x_3, x_181, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; size_t x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_182, 0);
x_185 = lean_ptr_addr(x_181);
x_186 = lean_usize_dec_eq(x_185, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_2);
x_187 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_182, 0, x_188);
return x_182;
}
else
{
lean_object* x_189; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_2);
lean_ctor_set(x_189, 1, x_184);
lean_ctor_set(x_182, 0, x_189);
return x_182;
}
}
else
{
lean_object* x_190; lean_object* x_191; size_t x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_182, 0);
x_191 = lean_ctor_get(x_182, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_182);
x_192 = lean_ptr_addr(x_181);
x_193 = lean_usize_dec_eq(x_192, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_2);
x_194 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_190);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_191);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_2);
lean_ctor_set(x_197, 1, x_190);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_191);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_2);
x_199 = !lean_is_exclusive(x_182);
if (x_199 == 0)
{
return x_182;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_182, 0);
x_201 = lean_ctor_get(x_182, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_182);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
default: 
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_2);
lean_ctor_set(x_203, 1, x_3);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_8);
return x_204;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__8___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__8___rarg(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__7___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_11 = lean_apply_7(x_1, x_3, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_10);
x_14 = lean_apply_7(x_1, x_12, x_10, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ptr_addr(x_9);
x_18 = lean_usize_dec_eq(x_17, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = l_Lean_Expr_app___override(x_9, x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
size_t x_21; uint8_t x_22; 
x_21 = lean_ptr_addr(x_10);
x_22 = lean_usize_dec_eq(x_21, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = l_Lean_Expr_app___override(x_9, x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_ptr_addr(x_9);
x_29 = lean_usize_dec_eq(x_28, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = l_Lean_Expr_app___override(x_9, x_10);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
size_t x_33; uint8_t x_34; 
x_33 = lean_ptr_addr(x_10);
x_34 = lean_usize_dec_eq(x_33, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_35 = l_Lean_Expr_app___override(x_9, x_10);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_10);
lean_dec(x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_26);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_49);
x_52 = lean_apply_7(x_1, x_3, x_49, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_50);
x_55 = lean_apply_7(x_1, x_53, x_50, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_55, 0, x_59);
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
return x_55;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_55, 0);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_55);
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
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_52);
if (x_69 == 0)
{
return x_52;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_52, 0);
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_52);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
case 7:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 2);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_74);
x_77 = lean_apply_7(x_1, x_3, x_74, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_75);
x_80 = lean_apply_7(x_1, x_78, x_75, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_80, 0, x_84);
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_80, 0);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_80);
x_87 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
x_90 = !lean_is_exclusive(x_80);
if (x_90 == 0)
{
return x_80;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_80, 0);
x_92 = lean_ctor_get(x_80, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_80);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_77);
if (x_94 == 0)
{
return x_77;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_77, 0);
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_77);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_99);
x_103 = lean_apply_7(x_1, x_3, x_99, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_100);
x_106 = lean_apply_7(x_1, x_104, x_100, x_4, x_5, x_6, x_7, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_101);
x_109 = lean_apply_7(x_1, x_107, x_101, x_4, x_5, x_6, x_7, x_108);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; size_t x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ptr_addr(x_99);
x_113 = lean_usize_dec_eq(x_112, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_2);
x_114 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
lean_ctor_set(x_109, 0, x_115);
return x_109;
}
else
{
size_t x_116; uint8_t x_117; 
x_116 = lean_ptr_addr(x_100);
x_117 = lean_usize_dec_eq(x_116, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_2);
x_118 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
lean_ctor_set(x_109, 0, x_119);
return x_109;
}
else
{
size_t x_120; uint8_t x_121; 
x_120 = lean_ptr_addr(x_101);
x_121 = lean_usize_dec_eq(x_120, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_2);
x_122 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_111);
lean_ctor_set(x_109, 0, x_123);
return x_109;
}
else
{
lean_object* x_124; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_2);
lean_ctor_set(x_124, 1, x_111);
lean_ctor_set(x_109, 0, x_124);
return x_109;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; size_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_109, 0);
x_126 = lean_ctor_get(x_109, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_109);
x_127 = lean_ptr_addr(x_99);
x_128 = lean_usize_dec_eq(x_127, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_2);
x_129 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_126);
return x_131;
}
else
{
size_t x_132; uint8_t x_133; 
x_132 = lean_ptr_addr(x_100);
x_133 = lean_usize_dec_eq(x_132, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_2);
x_134 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_125);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_126);
return x_136;
}
else
{
size_t x_137; uint8_t x_138; 
x_137 = lean_ptr_addr(x_101);
x_138 = lean_usize_dec_eq(x_137, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_2);
x_139 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_125);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_126);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_2);
lean_ctor_set(x_142, 1, x_125);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_126);
return x_143;
}
}
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_109);
if (x_144 == 0)
{
return x_109;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_109, 0);
x_146 = lean_ctor_get(x_109, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_109);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
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
x_148 = !lean_is_exclusive(x_106);
if (x_148 == 0)
{
return x_106;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_106, 0);
x_150 = lean_ctor_get(x_106, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_106);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
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
x_152 = !lean_is_exclusive(x_103);
if (x_152 == 0)
{
return x_103;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_103, 0);
x_154 = lean_ctor_get(x_103, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_103);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
case 10:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_2, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_2, 1);
lean_inc(x_157);
lean_inc(x_157);
x_158 = lean_apply_7(x_1, x_3, x_157, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; size_t x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = lean_ptr_addr(x_157);
x_162 = lean_usize_dec_eq(x_161, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_2);
x_163 = l_Lean_Expr_mdata___override(x_156, x_157);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set(x_158, 0, x_164);
return x_158;
}
else
{
lean_object* x_165; 
lean_dec(x_157);
lean_dec(x_156);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_2);
lean_ctor_set(x_165, 1, x_160);
lean_ctor_set(x_158, 0, x_165);
return x_158;
}
}
else
{
lean_object* x_166; lean_object* x_167; size_t x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_158, 0);
x_167 = lean_ctor_get(x_158, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_158);
x_168 = lean_ptr_addr(x_157);
x_169 = lean_usize_dec_eq(x_168, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_2);
x_170 = l_Lean_Expr_mdata___override(x_156, x_157);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_166);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_167);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_157);
lean_dec(x_156);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_2);
lean_ctor_set(x_173, 1, x_166);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_167);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_158);
if (x_175 == 0)
{
return x_158;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_158, 0);
x_177 = lean_ctor_get(x_158, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_158);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
case 11:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_2, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_2, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_2, 2);
lean_inc(x_181);
lean_inc(x_181);
x_182 = lean_apply_7(x_1, x_3, x_181, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; size_t x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_182, 0);
x_185 = lean_ptr_addr(x_181);
x_186 = lean_usize_dec_eq(x_185, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_2);
x_187 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_182, 0, x_188);
return x_182;
}
else
{
lean_object* x_189; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_2);
lean_ctor_set(x_189, 1, x_184);
lean_ctor_set(x_182, 0, x_189);
return x_182;
}
}
else
{
lean_object* x_190; lean_object* x_191; size_t x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_182, 0);
x_191 = lean_ctor_get(x_182, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_182);
x_192 = lean_ptr_addr(x_181);
x_193 = lean_usize_dec_eq(x_192, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_2);
x_194 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_190);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_191);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_2);
lean_ctor_set(x_197, 1, x_190);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_191);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_2);
x_199 = !lean_is_exclusive(x_182);
if (x_199 == 0)
{
return x_182;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_182, 0);
x_201 = lean_ctor_get(x_182, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_182);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
default: 
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_2);
lean_ctor_set(x_203, 1, x_3);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_8);
return x_204;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__10___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__10___rarg(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__9___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__11___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = lean_infer_type(x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg(x_1, x_14, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Array_append___rarg(x_5, x_17);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_19;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_10);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__11___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__12___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = lean_infer_type(x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg(x_1, x_14, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Array_append___rarg(x_5, x_17);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_19;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_10);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__12___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__13___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = lean_infer_type(x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg(x_1, x_14, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Array_append___rarg(x_5, x_17);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_19;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_10);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__13___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__15___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_11 = lean_apply_7(x_1, x_3, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_10);
x_14 = lean_apply_7(x_1, x_12, x_10, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ptr_addr(x_9);
x_18 = lean_usize_dec_eq(x_17, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = l_Lean_Expr_app___override(x_9, x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
size_t x_21; uint8_t x_22; 
x_21 = lean_ptr_addr(x_10);
x_22 = lean_usize_dec_eq(x_21, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = l_Lean_Expr_app___override(x_9, x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_ptr_addr(x_9);
x_29 = lean_usize_dec_eq(x_28, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = l_Lean_Expr_app___override(x_9, x_10);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
size_t x_33; uint8_t x_34; 
x_33 = lean_ptr_addr(x_10);
x_34 = lean_usize_dec_eq(x_33, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_35 = l_Lean_Expr_app___override(x_9, x_10);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_10);
lean_dec(x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_26);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_49);
x_52 = lean_apply_7(x_1, x_3, x_49, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_50);
x_55 = lean_apply_7(x_1, x_53, x_50, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_55, 0, x_59);
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
return x_55;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_55, 0);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_55);
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
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_52);
if (x_69 == 0)
{
return x_52;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_52, 0);
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_52);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
case 7:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 2);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_74);
x_77 = lean_apply_7(x_1, x_3, x_74, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_75);
x_80 = lean_apply_7(x_1, x_78, x_75, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_80, 0, x_84);
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_80, 0);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_80);
x_87 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
x_90 = !lean_is_exclusive(x_80);
if (x_90 == 0)
{
return x_80;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_80, 0);
x_92 = lean_ctor_get(x_80, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_80);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_77);
if (x_94 == 0)
{
return x_77;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_77, 0);
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_77);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_99);
x_103 = lean_apply_7(x_1, x_3, x_99, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_100);
x_106 = lean_apply_7(x_1, x_104, x_100, x_4, x_5, x_6, x_7, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_101);
x_109 = lean_apply_7(x_1, x_107, x_101, x_4, x_5, x_6, x_7, x_108);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; size_t x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ptr_addr(x_99);
x_113 = lean_usize_dec_eq(x_112, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_2);
x_114 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
lean_ctor_set(x_109, 0, x_115);
return x_109;
}
else
{
size_t x_116; uint8_t x_117; 
x_116 = lean_ptr_addr(x_100);
x_117 = lean_usize_dec_eq(x_116, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_2);
x_118 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
lean_ctor_set(x_109, 0, x_119);
return x_109;
}
else
{
size_t x_120; uint8_t x_121; 
x_120 = lean_ptr_addr(x_101);
x_121 = lean_usize_dec_eq(x_120, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_2);
x_122 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_111);
lean_ctor_set(x_109, 0, x_123);
return x_109;
}
else
{
lean_object* x_124; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_2);
lean_ctor_set(x_124, 1, x_111);
lean_ctor_set(x_109, 0, x_124);
return x_109;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; size_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_109, 0);
x_126 = lean_ctor_get(x_109, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_109);
x_127 = lean_ptr_addr(x_99);
x_128 = lean_usize_dec_eq(x_127, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_2);
x_129 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_126);
return x_131;
}
else
{
size_t x_132; uint8_t x_133; 
x_132 = lean_ptr_addr(x_100);
x_133 = lean_usize_dec_eq(x_132, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_2);
x_134 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_125);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_126);
return x_136;
}
else
{
size_t x_137; uint8_t x_138; 
x_137 = lean_ptr_addr(x_101);
x_138 = lean_usize_dec_eq(x_137, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_2);
x_139 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_125);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_126);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_2);
lean_ctor_set(x_142, 1, x_125);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_126);
return x_143;
}
}
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_109);
if (x_144 == 0)
{
return x_109;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_109, 0);
x_146 = lean_ctor_get(x_109, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_109);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
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
x_148 = !lean_is_exclusive(x_106);
if (x_148 == 0)
{
return x_106;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_106, 0);
x_150 = lean_ctor_get(x_106, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_106);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
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
x_152 = !lean_is_exclusive(x_103);
if (x_152 == 0)
{
return x_103;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_103, 0);
x_154 = lean_ctor_get(x_103, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_103);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
case 10:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_2, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_2, 1);
lean_inc(x_157);
lean_inc(x_157);
x_158 = lean_apply_7(x_1, x_3, x_157, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; size_t x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = lean_ptr_addr(x_157);
x_162 = lean_usize_dec_eq(x_161, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_2);
x_163 = l_Lean_Expr_mdata___override(x_156, x_157);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set(x_158, 0, x_164);
return x_158;
}
else
{
lean_object* x_165; 
lean_dec(x_157);
lean_dec(x_156);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_2);
lean_ctor_set(x_165, 1, x_160);
lean_ctor_set(x_158, 0, x_165);
return x_158;
}
}
else
{
lean_object* x_166; lean_object* x_167; size_t x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_158, 0);
x_167 = lean_ctor_get(x_158, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_158);
x_168 = lean_ptr_addr(x_157);
x_169 = lean_usize_dec_eq(x_168, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_2);
x_170 = l_Lean_Expr_mdata___override(x_156, x_157);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_166);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_167);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_157);
lean_dec(x_156);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_2);
lean_ctor_set(x_173, 1, x_166);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_167);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_158);
if (x_175 == 0)
{
return x_158;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_158, 0);
x_177 = lean_ctor_get(x_158, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_158);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
case 11:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_2, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_2, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_2, 2);
lean_inc(x_181);
lean_inc(x_181);
x_182 = lean_apply_7(x_1, x_3, x_181, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; size_t x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_182, 0);
x_185 = lean_ptr_addr(x_181);
x_186 = lean_usize_dec_eq(x_185, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_2);
x_187 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_182, 0, x_188);
return x_182;
}
else
{
lean_object* x_189; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_2);
lean_ctor_set(x_189, 1, x_184);
lean_ctor_set(x_182, 0, x_189);
return x_182;
}
}
else
{
lean_object* x_190; lean_object* x_191; size_t x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_182, 0);
x_191 = lean_ctor_get(x_182, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_182);
x_192 = lean_ptr_addr(x_181);
x_193 = lean_usize_dec_eq(x_192, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_2);
x_194 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_190);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_191);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_2);
lean_ctor_set(x_197, 1, x_190);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_191);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_2);
x_199 = !lean_is_exclusive(x_182);
if (x_199 == 0)
{
return x_182;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_182, 0);
x_201 = lean_ctor_get(x_182, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_182);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
default: 
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_2);
lean_ctor_set(x_203, 1, x_3);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_8);
return x_204;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__15___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__14___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__15___rarg(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__14___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__17___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_11 = lean_apply_7(x_1, x_3, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_10);
x_14 = lean_apply_7(x_1, x_12, x_10, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ptr_addr(x_9);
x_18 = lean_usize_dec_eq(x_17, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = l_Lean_Expr_app___override(x_9, x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
size_t x_21; uint8_t x_22; 
x_21 = lean_ptr_addr(x_10);
x_22 = lean_usize_dec_eq(x_21, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = l_Lean_Expr_app___override(x_9, x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_ptr_addr(x_9);
x_29 = lean_usize_dec_eq(x_28, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = l_Lean_Expr_app___override(x_9, x_10);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
size_t x_33; uint8_t x_34; 
x_33 = lean_ptr_addr(x_10);
x_34 = lean_usize_dec_eq(x_33, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_35 = l_Lean_Expr_app___override(x_9, x_10);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_10);
lean_dec(x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_26);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_49);
x_52 = lean_apply_7(x_1, x_3, x_49, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_50);
x_55 = lean_apply_7(x_1, x_53, x_50, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_55, 0, x_59);
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
return x_55;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_55, 0);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_55);
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
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_52);
if (x_69 == 0)
{
return x_52;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_52, 0);
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_52);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
case 7:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 2);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_74);
x_77 = lean_apply_7(x_1, x_3, x_74, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_75);
x_80 = lean_apply_7(x_1, x_78, x_75, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_80, 0, x_84);
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_80, 0);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_80);
x_87 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
x_90 = !lean_is_exclusive(x_80);
if (x_90 == 0)
{
return x_80;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_80, 0);
x_92 = lean_ctor_get(x_80, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_80);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_77);
if (x_94 == 0)
{
return x_77;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_77, 0);
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_77);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_99);
x_103 = lean_apply_7(x_1, x_3, x_99, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_100);
x_106 = lean_apply_7(x_1, x_104, x_100, x_4, x_5, x_6, x_7, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_101);
x_109 = lean_apply_7(x_1, x_107, x_101, x_4, x_5, x_6, x_7, x_108);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; size_t x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ptr_addr(x_99);
x_113 = lean_usize_dec_eq(x_112, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_2);
x_114 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
lean_ctor_set(x_109, 0, x_115);
return x_109;
}
else
{
size_t x_116; uint8_t x_117; 
x_116 = lean_ptr_addr(x_100);
x_117 = lean_usize_dec_eq(x_116, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_2);
x_118 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
lean_ctor_set(x_109, 0, x_119);
return x_109;
}
else
{
size_t x_120; uint8_t x_121; 
x_120 = lean_ptr_addr(x_101);
x_121 = lean_usize_dec_eq(x_120, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_2);
x_122 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_111);
lean_ctor_set(x_109, 0, x_123);
return x_109;
}
else
{
lean_object* x_124; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_2);
lean_ctor_set(x_124, 1, x_111);
lean_ctor_set(x_109, 0, x_124);
return x_109;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; size_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_109, 0);
x_126 = lean_ctor_get(x_109, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_109);
x_127 = lean_ptr_addr(x_99);
x_128 = lean_usize_dec_eq(x_127, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_2);
x_129 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_126);
return x_131;
}
else
{
size_t x_132; uint8_t x_133; 
x_132 = lean_ptr_addr(x_100);
x_133 = lean_usize_dec_eq(x_132, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_2);
x_134 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_125);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_126);
return x_136;
}
else
{
size_t x_137; uint8_t x_138; 
x_137 = lean_ptr_addr(x_101);
x_138 = lean_usize_dec_eq(x_137, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_2);
x_139 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_125);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_126);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_2);
lean_ctor_set(x_142, 1, x_125);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_126);
return x_143;
}
}
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_109);
if (x_144 == 0)
{
return x_109;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_109, 0);
x_146 = lean_ctor_get(x_109, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_109);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
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
x_148 = !lean_is_exclusive(x_106);
if (x_148 == 0)
{
return x_106;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_106, 0);
x_150 = lean_ctor_get(x_106, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_106);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
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
x_152 = !lean_is_exclusive(x_103);
if (x_152 == 0)
{
return x_103;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_103, 0);
x_154 = lean_ctor_get(x_103, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_103);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
case 10:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_2, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_2, 1);
lean_inc(x_157);
lean_inc(x_157);
x_158 = lean_apply_7(x_1, x_3, x_157, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; size_t x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = lean_ptr_addr(x_157);
x_162 = lean_usize_dec_eq(x_161, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_2);
x_163 = l_Lean_Expr_mdata___override(x_156, x_157);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set(x_158, 0, x_164);
return x_158;
}
else
{
lean_object* x_165; 
lean_dec(x_157);
lean_dec(x_156);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_2);
lean_ctor_set(x_165, 1, x_160);
lean_ctor_set(x_158, 0, x_165);
return x_158;
}
}
else
{
lean_object* x_166; lean_object* x_167; size_t x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_158, 0);
x_167 = lean_ctor_get(x_158, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_158);
x_168 = lean_ptr_addr(x_157);
x_169 = lean_usize_dec_eq(x_168, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_2);
x_170 = l_Lean_Expr_mdata___override(x_156, x_157);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_166);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_167);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_157);
lean_dec(x_156);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_2);
lean_ctor_set(x_173, 1, x_166);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_167);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_158);
if (x_175 == 0)
{
return x_158;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_158, 0);
x_177 = lean_ctor_get(x_158, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_158);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
case 11:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_2, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_2, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_2, 2);
lean_inc(x_181);
lean_inc(x_181);
x_182 = lean_apply_7(x_1, x_3, x_181, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; size_t x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_182, 0);
x_185 = lean_ptr_addr(x_181);
x_186 = lean_usize_dec_eq(x_185, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_2);
x_187 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_182, 0, x_188);
return x_182;
}
else
{
lean_object* x_189; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_2);
lean_ctor_set(x_189, 1, x_184);
lean_ctor_set(x_182, 0, x_189);
return x_182;
}
}
else
{
lean_object* x_190; lean_object* x_191; size_t x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_182, 0);
x_191 = lean_ctor_get(x_182, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_182);
x_192 = lean_ptr_addr(x_181);
x_193 = lean_usize_dec_eq(x_192, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_2);
x_194 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_190);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_191);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_2);
lean_ctor_set(x_197, 1, x_190);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_191);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_2);
x_199 = !lean_is_exclusive(x_182);
if (x_199 == 0)
{
return x_182;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_182, 0);
x_201 = lean_ctor_get(x_182, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_182);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
default: 
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_2);
lean_ctor_set(x_203, 1, x_3);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_8);
return x_204;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__17(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__17___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__16___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__17___rarg(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__16(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__16___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__19___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_11 = lean_apply_7(x_1, x_3, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_10);
x_14 = lean_apply_7(x_1, x_12, x_10, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ptr_addr(x_9);
x_18 = lean_usize_dec_eq(x_17, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = l_Lean_Expr_app___override(x_9, x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
size_t x_21; uint8_t x_22; 
x_21 = lean_ptr_addr(x_10);
x_22 = lean_usize_dec_eq(x_21, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = l_Lean_Expr_app___override(x_9, x_10);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_ptr_addr(x_9);
x_29 = lean_usize_dec_eq(x_28, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = l_Lean_Expr_app___override(x_9, x_10);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
size_t x_33; uint8_t x_34; 
x_33 = lean_ptr_addr(x_10);
x_34 = lean_usize_dec_eq(x_33, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_35 = l_Lean_Expr_app___override(x_9, x_10);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_10);
lean_dec(x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_26);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_49);
x_52 = lean_apply_7(x_1, x_3, x_49, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_50);
x_55 = lean_apply_7(x_1, x_53, x_50, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_55, 0, x_59);
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = l_Lean_Expr_lam___override(x_48, x_49, x_50, x_51);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
return x_55;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_55, 0);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_55);
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
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_52);
if (x_69 == 0)
{
return x_52;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_52, 0);
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_52);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
case 7:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 2);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_74);
x_77 = lean_apply_7(x_1, x_3, x_74, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_75);
x_80 = lean_apply_7(x_1, x_78, x_75, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_80, 0, x_84);
return x_80;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_80, 0);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_80);
x_87 = l_Lean_Expr_forallE___override(x_73, x_74, x_75, x_76);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
x_90 = !lean_is_exclusive(x_80);
if (x_90 == 0)
{
return x_80;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_80, 0);
x_92 = lean_ctor_get(x_80, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_80);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_77);
if (x_94 == 0)
{
return x_77;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_77, 0);
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_77);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
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
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_99);
x_103 = lean_apply_7(x_1, x_3, x_99, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_100);
x_106 = lean_apply_7(x_1, x_104, x_100, x_4, x_5, x_6, x_7, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_101);
x_109 = lean_apply_7(x_1, x_107, x_101, x_4, x_5, x_6, x_7, x_108);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; size_t x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ptr_addr(x_99);
x_113 = lean_usize_dec_eq(x_112, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_2);
x_114 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
lean_ctor_set(x_109, 0, x_115);
return x_109;
}
else
{
size_t x_116; uint8_t x_117; 
x_116 = lean_ptr_addr(x_100);
x_117 = lean_usize_dec_eq(x_116, x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_2);
x_118 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_111);
lean_ctor_set(x_109, 0, x_119);
return x_109;
}
else
{
size_t x_120; uint8_t x_121; 
x_120 = lean_ptr_addr(x_101);
x_121 = lean_usize_dec_eq(x_120, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_2);
x_122 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_111);
lean_ctor_set(x_109, 0, x_123);
return x_109;
}
else
{
lean_object* x_124; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_2);
lean_ctor_set(x_124, 1, x_111);
lean_ctor_set(x_109, 0, x_124);
return x_109;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; size_t x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_109, 0);
x_126 = lean_ctor_get(x_109, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_109);
x_127 = lean_ptr_addr(x_99);
x_128 = lean_usize_dec_eq(x_127, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_2);
x_129 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_126);
return x_131;
}
else
{
size_t x_132; uint8_t x_133; 
x_132 = lean_ptr_addr(x_100);
x_133 = lean_usize_dec_eq(x_132, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_2);
x_134 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_125);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_126);
return x_136;
}
else
{
size_t x_137; uint8_t x_138; 
x_137 = lean_ptr_addr(x_101);
x_138 = lean_usize_dec_eq(x_137, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_2);
x_139 = l_Lean_Expr_letE___override(x_98, x_99, x_100, x_101, x_102);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_125);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_126);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_2);
lean_ctor_set(x_142, 1, x_125);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_126);
return x_143;
}
}
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_109);
if (x_144 == 0)
{
return x_109;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_109, 0);
x_146 = lean_ctor_get(x_109, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_109);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
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
x_148 = !lean_is_exclusive(x_106);
if (x_148 == 0)
{
return x_106;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_106, 0);
x_150 = lean_ctor_get(x_106, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_106);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
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
x_152 = !lean_is_exclusive(x_103);
if (x_152 == 0)
{
return x_103;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_103, 0);
x_154 = lean_ctor_get(x_103, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_103);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
case 10:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_2, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_2, 1);
lean_inc(x_157);
lean_inc(x_157);
x_158 = lean_apply_7(x_1, x_3, x_157, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; size_t x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = lean_ptr_addr(x_157);
x_162 = lean_usize_dec_eq(x_161, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_2);
x_163 = l_Lean_Expr_mdata___override(x_156, x_157);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set(x_158, 0, x_164);
return x_158;
}
else
{
lean_object* x_165; 
lean_dec(x_157);
lean_dec(x_156);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_2);
lean_ctor_set(x_165, 1, x_160);
lean_ctor_set(x_158, 0, x_165);
return x_158;
}
}
else
{
lean_object* x_166; lean_object* x_167; size_t x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_158, 0);
x_167 = lean_ctor_get(x_158, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_158);
x_168 = lean_ptr_addr(x_157);
x_169 = lean_usize_dec_eq(x_168, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_2);
x_170 = l_Lean_Expr_mdata___override(x_156, x_157);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_166);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_167);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_157);
lean_dec(x_156);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_2);
lean_ctor_set(x_173, 1, x_166);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_167);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_158);
if (x_175 == 0)
{
return x_158;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_158, 0);
x_177 = lean_ctor_get(x_158, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_158);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
case 11:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_2, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_2, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_2, 2);
lean_inc(x_181);
lean_inc(x_181);
x_182 = lean_apply_7(x_1, x_3, x_181, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; size_t x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_182, 0);
x_185 = lean_ptr_addr(x_181);
x_186 = lean_usize_dec_eq(x_185, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_2);
x_187 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_182, 0, x_188);
return x_182;
}
else
{
lean_object* x_189; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_2);
lean_ctor_set(x_189, 1, x_184);
lean_ctor_set(x_182, 0, x_189);
return x_182;
}
}
else
{
lean_object* x_190; lean_object* x_191; size_t x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_182, 0);
x_191 = lean_ctor_get(x_182, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_182);
x_192 = lean_ptr_addr(x_181);
x_193 = lean_usize_dec_eq(x_192, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_2);
x_194 = l_Lean_Expr_proj___override(x_179, x_180, x_181);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_190);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_191);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_2);
lean_ctor_set(x_197, 1, x_190);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_191);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_2);
x_199 = !lean_is_exclusive(x_182);
if (x_199 == 0)
{
return x_182;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_182, 0);
x_201 = lean_ctor_get(x_182, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_182);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
default: 
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_2);
lean_ctor_set(x_203, 1, x_3);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_8);
return x_204;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__19(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__19___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__18___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_traverseChildren___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__19___rarg(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__18(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__18___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Array_append___rarg(x_2, x_11);
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
x_15 = l_Array_append___rarg(x_2, x_13);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Array_reverse___rarg(x_11);
x_14 = lean_array_get_size(x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
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
x_17 = lean_nat_dec_le(x_14, x_14);
if (x_17 == 0)
{
lean_dec(x_14);
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
x_19 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__11___rarg(x_1, x_2, x_18, x_19, x_13, x_4, x_5, x_6, x_7, x_12);
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
x_23 = l_Array_reverse___rarg(x_21);
x_24 = lean_array_get_size(x_2);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
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
x_28 = lean_nat_dec_le(x_24, x_24);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_24);
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
x_31 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__11___rarg(x_1, x_2, x_30, x_31, x_23, x_4, x_5, x_6, x_7, x_22);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_9);
if (x_33 == 0)
{
return x_9;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Array_reverse___rarg(x_11);
x_14 = lean_array_get_size(x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
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
x_17 = lean_nat_dec_le(x_14, x_14);
if (x_17 == 0)
{
lean_dec(x_14);
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
x_19 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__12___rarg(x_1, x_2, x_18, x_19, x_13, x_4, x_5, x_6, x_7, x_12);
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
x_23 = l_Array_reverse___rarg(x_21);
x_24 = lean_array_get_size(x_2);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
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
x_28 = lean_nat_dec_le(x_24, x_24);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_24);
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
x_31 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__12___rarg(x_1, x_2, x_30, x_31, x_23, x_4, x_5, x_6, x_7, x_22);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_9);
if (x_33 == 0)
{
return x_9;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Array_reverse___rarg(x_11);
x_14 = lean_array_get_size(x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
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
x_17 = lean_nat_dec_le(x_14, x_14);
if (x_17 == 0)
{
lean_dec(x_14);
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
x_19 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__13___rarg(x_1, x_2, x_18, x_19, x_13, x_4, x_5, x_6, x_7, x_12);
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
x_23 = l_Array_reverse___rarg(x_21);
x_24 = lean_array_get_size(x_2);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
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
x_28 = lean_nat_dec_le(x_24, x_24);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_24);
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
x_31 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__13___rarg(x_1, x_2, x_30, x_31, x_23, x_4, x_5, x_6, x_7, x_22);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_9);
if (x_33 == 0)
{
return x_9;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_8 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Array_reverse___rarg(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__1), 8, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__1___rarg(x_14, x_13, x_2, x_3, x_4, x_5, x_6, x_12);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
case 2:
{
lean_object* x_20; 
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_20 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Array_reverse___rarg(x_21);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__1), 8, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__3___rarg(x_24, x_23, x_2, x_3, x_4, x_5, x_6, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
case 3:
{
lean_object* x_30; 
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_30 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Array_reverse___rarg(x_31);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__1), 8, 1);
lean_closure_set(x_34, 0, x_1);
x_35 = l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__5___rarg(x_34, x_33, x_2, x_3, x_4, x_5, x_6, x_32);
return x_35;
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
case 4:
{
lean_object* x_40; 
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_40 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Array_reverse___rarg(x_41);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__1), 8, 1);
lean_closure_set(x_44, 0, x_1);
x_45 = l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__7___rarg(x_44, x_43, x_2, x_3, x_4, x_5, x_6, x_42);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
return x_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_40, 0);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_40);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
case 5:
{
lean_object* x_50; 
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_50 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Array_reverse___rarg(x_51);
x_54 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__1), 8, 1);
lean_closure_set(x_54, 0, x_1);
x_55 = l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__9___rarg(x_54, x_53, x_2, x_3, x_4, x_5, x_6, x_52);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
case 6:
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_60 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__2___boxed), 8, 1);
lean_closure_set(x_60, 0, x_1);
x_61 = 0;
x_62 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_2, x_60, x_61, x_3, x_4, x_5, x_6, x_7);
return x_62;
}
case 7:
{
lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_63 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__3___boxed), 8, 1);
lean_closure_set(x_63, 0, x_1);
x_64 = 0;
x_65 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_2, x_63, x_64, x_3, x_4, x_5, x_6, x_7);
return x_65;
}
case 8:
{
lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_66 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__4___boxed), 8, 1);
lean_closure_set(x_66, 0, x_1);
x_67 = 0;
x_68 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_2, x_66, x_67, x_3, x_4, x_5, x_6, x_7);
return x_68;
}
case 9:
{
lean_object* x_69; 
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_69 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Array_reverse___rarg(x_70);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__1), 8, 1);
lean_closure_set(x_73, 0, x_1);
x_74 = l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__14___rarg(x_73, x_72, x_2, x_3, x_4, x_5, x_6, x_71);
return x_74;
}
else
{
uint8_t x_75; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_69);
if (x_75 == 0)
{
return x_69;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_69, 0);
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_69);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
case 10:
{
lean_object* x_79; 
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_79 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Array_reverse___rarg(x_80);
x_83 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__1), 8, 1);
lean_closure_set(x_83, 0, x_1);
x_84 = l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__16___rarg(x_83, x_82, x_2, x_3, x_4, x_5, x_6, x_81);
return x_84;
}
else
{
uint8_t x_85; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_79);
if (x_85 == 0)
{
return x_79;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_79, 0);
x_87 = lean_ctor_get(x_79, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_79);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
default: 
{
lean_object* x_89; 
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_89 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Array_reverse___rarg(x_90);
x_93 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__1), 8, 1);
lean_closure_set(x_93, 0, x_1);
x_94 = l_Lean_Expr_foldlM___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__18___rarg(x_93, x_92, x_2, x_3, x_4, x_5, x_6, x_91);
return x_94;
}
else
{
uint8_t x_95; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_89);
if (x_95 == 0)
{
return x_89;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_89, 0);
x_97 = lean_ctor_get(x_89, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_89);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__11___rarg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__12___rarg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Rewrites_getSubexpressionMatches___spec__13___rarg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_array_fget(x_1, x_2);
x_9 = lean_array_fget(x_1, x_7);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_nat_dec_lt(x_13, x_12);
lean_dec(x_12);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_15; 
x_15 = lean_array_fswap(x_1, x_2, x_7);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_7;
x_3 = lean_box(0);
goto _start;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at_Lean_Meta_Rewrites_rewriteCandidates___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_10 = l_Array_insertionSort_swapLoop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__2(x_1, x_2, lean_box(0));
x_11 = lean_nat_add(x_2, x_6);
lean_dec(x_2);
x_1 = x_10;
x_2 = x_11;
x_3 = x_7;
goto _start;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
static uint8_t _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 0;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static uint8_t _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 1;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (x_1 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_NameSet_contains(x_6, x_2);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1___closed__1;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_box(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
lean_inc(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_push(x_5, x_21);
x_23 = lean_box(0);
x_24 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_6, x_2, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_12);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1___closed__2;
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_6);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_12);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_box(x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
lean_inc(x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_array_push(x_5, x_36);
x_38 = lean_box(0);
x_39 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_6, x_2, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_12);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = l_Lean_NameSet_contains(x_4, x_2);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1___closed__1;
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_5);
lean_ctor_set(x_46, 1, x_6);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_12);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_box(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_3);
lean_inc(x_2);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_push(x_5, x_52);
x_54 = lean_box(0);
x_55 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_2, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_6);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_12);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1___closed__2;
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_5);
lean_ctor_set(x_61, 1, x_6);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_4);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_12);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_65 = lean_box(x_1);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_3);
lean_inc(x_2);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_2);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_array_push(x_5, x_67);
x_69 = lean_box(0);
x_70 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_2, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_6);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_12);
return x_74;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_array_uget(x_4, x_6);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
x_27 = l_Lean_NameSet_contains(x_1, x_18);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
lean_free_object(x_17);
lean_free_object(x_7);
x_28 = lean_box(0);
x_29 = lean_unbox(x_19);
lean_dec(x_19);
x_30 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1(x_29, x_18, x_20, x_22, x_25, x_26, x_28, x_8, x_9, x_10, x_11, x_12);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 1;
x_35 = lean_usize_add(x_6, x_34);
x_6 = x_35;
x_7 = x_33;
x_12 = x_32;
goto _start;
}
else
{
size_t x_37; size_t x_38; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_37 = 1;
x_38 = lean_usize_add(x_6, x_37);
x_6 = x_38;
goto _start;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = l_Lean_NameSet_contains(x_1, x_18);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; 
lean_free_object(x_7);
x_43 = lean_box(0);
x_44 = lean_unbox(x_19);
lean_dec(x_19);
x_45 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1(x_44, x_18, x_20, x_22, x_40, x_41, x_43, x_8, x_9, x_10, x_11, x_12);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = 1;
x_50 = lean_usize_add(x_6, x_49);
x_6 = x_50;
x_7 = x_48;
x_12 = x_47;
goto _start;
}
else
{
lean_object* x_52; size_t x_53; size_t x_54; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_40);
lean_ctor_set(x_52, 1, x_41);
lean_ctor_set(x_7, 1, x_52);
x_53 = 1;
x_54 = lean_usize_add(x_6, x_53);
x_6 = x_54;
goto _start;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_7, 0);
lean_inc(x_56);
lean_dec(x_7);
x_57 = lean_ctor_get(x_17, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_17, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_59 = x_17;
} else {
 lean_dec_ref(x_17);
 x_59 = lean_box(0);
}
x_60 = l_Lean_NameSet_contains(x_1, x_18);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; 
lean_dec(x_59);
x_61 = lean_box(0);
x_62 = lean_unbox(x_19);
lean_dec(x_19);
x_63 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1(x_62, x_18, x_20, x_56, x_57, x_58, x_61, x_8, x_9, x_10, x_11, x_12);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_67 = 1;
x_68 = lean_usize_add(x_6, x_67);
x_6 = x_68;
x_7 = x_66;
x_12 = x_65;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
if (lean_is_scalar(x_59)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_59;
}
lean_ctor_set(x_70, 0, x_57);
lean_ctor_set(x_70, 1, x_58);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_56);
lean_ctor_set(x_71, 1, x_70);
x_72 = 1;
x_73 = lean_usize_add(x_6, x_72);
x_6 = x_73;
x_7 = x_71;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Rewrites_rewriteCandidates___spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_5, 1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_5, 0, x_14);
x_15 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_5, 1, x_21);
lean_ctor_set(x_5, 0, x_20);
x_22 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_22;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_inc(x_25);
lean_dec(x_5);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_28 = x_24;
} else {
 lean_dec_ref(x_24);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_25);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_uset(x_7, x_2, x_31);
x_2 = x_9;
x_3 = x_32;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Rewrites_rewriteCandidates___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_5, 1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_5, 0, x_14);
x_15 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_5, 1, x_21);
lean_ctor_set(x_5, 0, x_20);
x_22 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_22;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_inc(x_25);
lean_dec(x_5);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_28 = x_24;
} else {
 lean_dec_ref(x_24);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_25);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_uset(x_7, x_2, x_31);
x_2 = x_9;
x_3 = x_32;
goto _start;
}
}
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__6;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__7;
x_2 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__3;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__8;
x_2 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__13;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__14;
x_2 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__3;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__15;
x_2 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = l_Lean_MessageData_ofName(x_8);
x_11 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__3;
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_10);
x_12 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__4;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
x_17 = l___private_Init_Data_Repr_0__Nat_reprFast(x_16);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
x_20 = lean_unbox(x_15);
lean_dec(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__9;
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_19);
lean_ctor_set(x_9, 0, x_21);
x_22 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__10;
x_23 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__11;
x_24 = l_Lean_MessageData_bracket(x_22, x_9, x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_MessageData_bracket(x_22, x_25, x_23);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_26);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__16;
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_19);
lean_ctor_set(x_9, 0, x_28);
x_29 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__10;
x_30 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__11;
x_31 = l_Lean_MessageData_bracket(x_29, x_9, x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_MessageData_bracket(x_29, x_32, x_30);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_33);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_9, 0);
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_9);
x_37 = l___private_Init_Data_Repr_0__Nat_reprFast(x_36);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_MessageData_ofFormat(x_38);
x_40 = lean_unbox(x_35);
lean_dec(x_35);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__9;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
x_43 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__10;
x_44 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__11;
x_45 = l_Lean_MessageData_bracket(x_43, x_42, x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_13);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_MessageData_bracket(x_43, x_46, x_44);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_47);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__16;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_39);
x_51 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__10;
x_52 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__11;
x_53 = l_Lean_MessageData_bracket(x_51, x_50, x_52);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_13);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_MessageData_bracket(x_51, x_54, x_52);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_55);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_57 = lean_ctor_get(x_1, 1);
x_58 = lean_ctor_get(x_5, 0);
x_59 = lean_ctor_get(x_5, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_5);
x_60 = l_Lean_MessageData_ofName(x_58);
x_61 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__3;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__4;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_67 = x_59;
} else {
 lean_dec_ref(x_59);
 x_67 = lean_box(0);
}
x_68 = l___private_Init_Data_Repr_0__Nat_reprFast(x_66);
x_69 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lean_MessageData_ofFormat(x_69);
x_71 = lean_unbox(x_65);
lean_dec(x_65);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__9;
if (lean_is_scalar(x_67)) {
 x_73 = lean_alloc_ctor(7, 2, 0);
} else {
 x_73 = x_67;
 lean_ctor_set_tag(x_73, 7);
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
x_74 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__10;
x_75 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__11;
x_76 = l_Lean_MessageData_bracket(x_74, x_73, x_75);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_MessageData_bracket(x_74, x_77, x_75);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_78);
{
lean_object* _tmp_0 = x_57;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_80 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__16;
if (lean_is_scalar(x_67)) {
 x_81 = lean_alloc_ctor(7, 2, 0);
} else {
 x_81 = x_67;
 lean_ctor_set_tag(x_81, 7);
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_70);
x_82 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__10;
x_83 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__11;
x_84 = l_Lean_MessageData_bracket(x_82, x_81, x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_64);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_MessageData_bracket(x_82, x_85, x_83);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_86);
{
lean_object* _tmp_0 = x_57;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_88 = lean_ctor_get(x_1, 0);
x_89 = lean_ctor_get(x_1, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_1);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_92 = x_88;
} else {
 lean_dec_ref(x_88);
 x_92 = lean_box(0);
}
x_93 = l_Lean_MessageData_ofName(x_90);
x_94 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__3;
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(7, 2, 0);
} else {
 x_95 = x_92;
 lean_ctor_set_tag(x_95, 7);
}
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__4;
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_ctor_get(x_91, 0);
lean_inc(x_98);
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
x_101 = l___private_Init_Data_Repr_0__Nat_reprFast(x_99);
x_102 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = l_Lean_MessageData_ofFormat(x_102);
x_104 = lean_unbox(x_98);
lean_dec(x_98);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_105 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__9;
if (lean_is_scalar(x_100)) {
 x_106 = lean_alloc_ctor(7, 2, 0);
} else {
 x_106 = x_100;
 lean_ctor_set_tag(x_106, 7);
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
x_107 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__10;
x_108 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__11;
x_109 = l_Lean_MessageData_bracket(x_107, x_106, x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_97);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_MessageData_bracket(x_107, x_110, x_108);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_2);
x_1 = x_89;
x_2 = x_112;
goto _start;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_114 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__16;
if (lean_is_scalar(x_100)) {
 x_115 = lean_alloc_ctor(7, 2, 0);
} else {
 x_115 = x_100;
 lean_ctor_set_tag(x_115, 7);
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_103);
x_116 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__10;
x_117 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__11;
x_118 = l_Lean_MessageData_bracket(x_116, x_115, x_117);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_97);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_MessageData_bracket(x_116, x_119, x_117);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_2);
x_1 = x_89;
x_2 = x_121;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_size(x_1);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_Rewrites_rewriteCandidates___spec__4(x_10, x_2, x_1);
x_12 = lean_array_size(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Meta_Rewrites_rewriteCandidates___spec__5(x_12, x_2, x_3);
x_14 = l_Array_append___rarg(x_11, x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1;
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l_Lean_Meta_Rewrites_rewriteCandidates___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
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
x_11 = l_Lean_Meta_Rewrites_getSubexpressionMatches___rarg(x_10, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_get_size(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_insertionSort_traverse___at_Lean_Meta_Rewrites_rewriteCandidates___spec__1(x_12, x_15, x_14);
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = lean_array_size(x_16);
x_20 = 0;
x_21 = l_Lean_Meta_Rewrites_rewriteCandidates___closed__2;
x_22 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3(x_4, x_16, x_18, x_16, x_19, x_20, x_21, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
lean_dec(x_28);
x_29 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__2;
x_30 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_29, x_5, x_6, x_7, x_8, x_25);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_24);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_box(0);
x_35 = l_Lean_Meta_Rewrites_rewriteCandidates___lambda__1(x_1, x_20, x_27, x_34, x_5, x_6, x_7, x_8, x_33);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_30, 1);
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
lean_inc(x_27);
x_39 = lean_array_to_list(x_27);
x_40 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6(x_39, x_17);
x_41 = l_Lean_MessageData_ofList(x_40);
x_42 = l_Lean_Meta_Rewrites_rewriteCandidates___closed__4;
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_41);
lean_ctor_set(x_30, 0, x_42);
x_43 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__4;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_43);
lean_ctor_set(x_24, 0, x_30);
x_44 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_29, x_24, x_5, x_6, x_7, x_8, x_37);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_Rewrites_rewriteCandidates___lambda__1(x_1, x_20, x_27, x_45, x_5, x_6, x_7, x_8, x_46);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_dec(x_30);
lean_inc(x_27);
x_49 = lean_array_to_list(x_27);
x_50 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6(x_49, x_17);
x_51 = l_Lean_MessageData_ofList(x_50);
x_52 = l_Lean_Meta_Rewrites_rewriteCandidates___closed__4;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__4;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_54);
lean_ctor_set(x_24, 0, x_53);
x_55 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_29, x_24, x_5, x_6, x_7, x_8, x_48);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Meta_Rewrites_rewriteCandidates___lambda__1(x_1, x_20, x_27, x_56, x_5, x_6, x_7, x_8, x_57);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_56);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_24, 0);
lean_inc(x_59);
lean_dec(x_24);
x_60 = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__2;
x_61 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_60, x_5, x_6, x_7, x_8, x_25);
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
x_66 = l_Lean_Meta_Rewrites_rewriteCandidates___lambda__1(x_1, x_20, x_59, x_65, x_5, x_6, x_7, x_8, x_64);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
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
x_69 = lean_array_to_list(x_59);
x_70 = l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6(x_69, x_17);
x_71 = l_Lean_MessageData_ofList(x_70);
x_72 = l_Lean_Meta_Rewrites_rewriteCandidates___closed__4;
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(7, 2, 0);
} else {
 x_73 = x_68;
 lean_ctor_set_tag(x_73, 7);
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__4;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_60, x_75, x_5, x_6, x_7, x_8, x_67);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Meta_Rewrites_rewriteCandidates___lambda__1(x_1, x_20, x_59, x_77, x_5, x_6, x_7, x_8, x_78);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_77);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_11);
if (x_80 == 0)
{
return x_11;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_11, 0);
x_82 = lean_ctor_get(x_11, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_11);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Rewrites_rewriteCandidates___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_Rewrites_rewriteCandidates___spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Rewrites_rewriteCandidates___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_Rewrites_rewriteCandidates___spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_rewriteCandidates___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; lean_object* x_11; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_Rewrites_rewriteCandidates___lambda__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
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
static lean_object* _init_l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no goals", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__2;
x_2 = l_Lean_Expr_lit___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
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
x_6 = l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_Rewrites_RewriteResult_addSuggestion___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_2, x_3, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at_Lean_Meta_Rewrites_RewriteResult_addSuggestion___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at_Lean_Meta_Rewrites_RewriteResult_addSuggestion___spec__1___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_7, 5);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_13 = lean_box(x_12);
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Meta_Rewrites_RewriteResult_newGoal(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_10);
x_20 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(x_2, x_16, x_17, x_18, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lambda__1___boxed), 9, 2);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_1);
x_12 = l_Lean_Meta_withMCtx___at_Lean_Meta_Rewrites_RewriteResult_addSuggestion___spec__1___rarg(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Meta_Rewrites_takeListAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Meta_Rewrites_takeListAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Rewrites_takeListAux___spec__3(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Rewrites_takeListAux___spec__6(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Rewrites_takeListAux___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Meta_Rewrites_takeListAux___spec__6(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Rewrites_takeListAux___spec__4(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Meta_Rewrites_takeListAux___spec__5(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Rewrites_takeListAux___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = lean_string_dec_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Rewrites_takeListAux___spec__7(x_1, x_2, x_8);
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
x_14 = lean_string_dec_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Rewrites_takeListAux___spec__7(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Meta_Rewrites_dischargableWithRfl_x3f(x_2, x_15, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = lean_ctor_get_uint8(x_3, sizeof(void*)*5);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_array_push(x_6, x_1);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; lean_object* x_37; uint8_t x_38; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
x_24 = lean_array_get_size(x_23);
x_25 = lean_string_hash(x_4);
x_26 = 32;
x_27 = lean_uint64_shift_right(x_25, x_26);
x_28 = lean_uint64_xor(x_25, x_27);
x_29 = 16;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_34 = 1;
x_35 = lean_usize_sub(x_33, x_34);
x_36 = lean_usize_land(x_32, x_35);
x_37 = lean_array_uget(x_23, x_36);
x_38 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Rewrites_takeListAux___spec__3(x_4, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_22, x_39);
lean_dec(x_22);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_37);
x_43 = lean_array_uset(x_23, x_36, x_42);
x_44 = lean_unsigned_to_nat(4u);
x_45 = lean_nat_mul(x_40, x_44);
x_46 = lean_unsigned_to_nat(3u);
x_47 = lean_nat_div(x_45, x_46);
lean_dec(x_45);
x_48 = lean_array_get_size(x_43);
x_49 = lean_nat_dec_le(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Rewrites_takeListAux___spec__4(x_43);
lean_ctor_set(x_7, 1, x_50);
lean_ctor_set(x_7, 0, x_40);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_20);
lean_ctor_set(x_51, 1, x_7);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_5);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_16, 0, x_53);
return x_16;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_ctor_set(x_7, 1, x_43);
lean_ctor_set(x_7, 0, x_40);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_20);
lean_ctor_set(x_54, 1, x_7);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_5);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_16, 0, x_56);
return x_16;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_box(0);
x_58 = lean_array_uset(x_23, x_36, x_57);
x_59 = lean_box(0);
x_60 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Rewrites_takeListAux___spec__7(x_4, x_59, x_37);
x_61 = lean_array_uset(x_58, x_36, x_60);
lean_ctor_set(x_7, 1, x_61);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_20);
lean_ctor_set(x_62, 1, x_7);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_5);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_16, 0, x_64);
return x_16;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; size_t x_75; size_t x_76; size_t x_77; size_t x_78; size_t x_79; lean_object* x_80; uint8_t x_81; 
x_65 = lean_ctor_get(x_7, 0);
x_66 = lean_ctor_get(x_7, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_7);
x_67 = lean_array_get_size(x_66);
x_68 = lean_string_hash(x_4);
x_69 = 32;
x_70 = lean_uint64_shift_right(x_68, x_69);
x_71 = lean_uint64_xor(x_68, x_70);
x_72 = 16;
x_73 = lean_uint64_shift_right(x_71, x_72);
x_74 = lean_uint64_xor(x_71, x_73);
x_75 = lean_uint64_to_usize(x_74);
x_76 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_77 = 1;
x_78 = lean_usize_sub(x_76, x_77);
x_79 = lean_usize_land(x_75, x_78);
x_80 = lean_array_uget(x_66, x_79);
x_81 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Rewrites_takeListAux___spec__3(x_4, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_65, x_82);
lean_dec(x_65);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_4);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_80);
x_86 = lean_array_uset(x_66, x_79, x_85);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_mul(x_83, x_87);
x_89 = lean_unsigned_to_nat(3u);
x_90 = lean_nat_div(x_88, x_89);
lean_dec(x_88);
x_91 = lean_array_get_size(x_86);
x_92 = lean_nat_dec_le(x_90, x_91);
lean_dec(x_91);
lean_dec(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Rewrites_takeListAux___spec__4(x_86);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_83);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_20);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_5);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_16, 0, x_97);
return x_16;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_83);
lean_ctor_set(x_98, 1, x_86);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_20);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_5);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_16, 0, x_101);
return x_16;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_box(0);
x_103 = lean_array_uset(x_66, x_79, x_102);
x_104 = lean_box(0);
x_105 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Rewrites_takeListAux___spec__7(x_4, x_104, x_80);
x_106 = lean_array_uset(x_103, x_79, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_65);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_20);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_5);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_16, 0, x_110);
return x_16;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint64_t x_117; uint64_t x_118; uint64_t x_119; uint64_t x_120; uint64_t x_121; uint64_t x_122; uint64_t x_123; size_t x_124; size_t x_125; size_t x_126; size_t x_127; size_t x_128; lean_object* x_129; uint8_t x_130; 
x_111 = lean_ctor_get(x_16, 1);
lean_inc(x_111);
lean_dec(x_16);
x_112 = lean_array_push(x_6, x_1);
x_113 = lean_ctor_get(x_7, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_7, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_115 = x_7;
} else {
 lean_dec_ref(x_7);
 x_115 = lean_box(0);
}
x_116 = lean_array_get_size(x_114);
x_117 = lean_string_hash(x_4);
x_118 = 32;
x_119 = lean_uint64_shift_right(x_117, x_118);
x_120 = lean_uint64_xor(x_117, x_119);
x_121 = 16;
x_122 = lean_uint64_shift_right(x_120, x_121);
x_123 = lean_uint64_xor(x_120, x_122);
x_124 = lean_uint64_to_usize(x_123);
x_125 = lean_usize_of_nat(x_116);
lean_dec(x_116);
x_126 = 1;
x_127 = lean_usize_sub(x_125, x_126);
x_128 = lean_usize_land(x_124, x_127);
x_129 = lean_array_uget(x_114, x_128);
x_130 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Rewrites_takeListAux___spec__3(x_4, x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_nat_add(x_113, x_131);
lean_dec(x_113);
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_134, 0, x_4);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_129);
x_135 = lean_array_uset(x_114, x_128, x_134);
x_136 = lean_unsigned_to_nat(4u);
x_137 = lean_nat_mul(x_132, x_136);
x_138 = lean_unsigned_to_nat(3u);
x_139 = lean_nat_div(x_137, x_138);
lean_dec(x_137);
x_140 = lean_array_get_size(x_135);
x_141 = lean_nat_dec_le(x_139, x_140);
lean_dec(x_140);
lean_dec(x_139);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Rewrites_takeListAux___spec__4(x_135);
if (lean_is_scalar(x_115)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_115;
}
lean_ctor_set(x_143, 0, x_132);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_112);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_5);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_111);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
if (lean_is_scalar(x_115)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_115;
}
lean_ctor_set(x_148, 0, x_132);
lean_ctor_set(x_148, 1, x_135);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_112);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_5);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_111);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_153 = lean_box(0);
x_154 = lean_array_uset(x_114, x_128, x_153);
x_155 = lean_box(0);
x_156 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Rewrites_takeListAux___spec__7(x_4, x_155, x_129);
x_157 = lean_array_uset(x_154, x_128, x_156);
if (lean_is_scalar(x_115)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_115;
}
lean_ctor_set(x_158, 0, x_113);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_112);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_5);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_111);
return x_162;
}
}
}
else
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_16, 0);
lean_inc(x_163);
x_164 = lean_unbox(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_16);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = lean_ctor_get(x_16, 0);
lean_dec(x_166);
x_167 = lean_array_push(x_6, x_1);
x_168 = !lean_is_exclusive(x_7);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint64_t x_172; uint64_t x_173; uint64_t x_174; uint64_t x_175; uint64_t x_176; uint64_t x_177; uint64_t x_178; size_t x_179; size_t x_180; size_t x_181; size_t x_182; size_t x_183; lean_object* x_184; uint8_t x_185; 
x_169 = lean_ctor_get(x_7, 0);
x_170 = lean_ctor_get(x_7, 1);
x_171 = lean_array_get_size(x_170);
x_172 = lean_string_hash(x_4);
x_173 = 32;
x_174 = lean_uint64_shift_right(x_172, x_173);
x_175 = lean_uint64_xor(x_172, x_174);
x_176 = 16;
x_177 = lean_uint64_shift_right(x_175, x_176);
x_178 = lean_uint64_xor(x_175, x_177);
x_179 = lean_uint64_to_usize(x_178);
x_180 = lean_usize_of_nat(x_171);
lean_dec(x_171);
x_181 = 1;
x_182 = lean_usize_sub(x_180, x_181);
x_183 = lean_usize_land(x_179, x_182);
x_184 = lean_array_uget(x_170, x_183);
x_185 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Rewrites_takeListAux___spec__3(x_4, x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_nat_add(x_169, x_186);
lean_dec(x_169);
x_188 = lean_box(0);
x_189 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_189, 0, x_4);
lean_ctor_set(x_189, 1, x_188);
lean_ctor_set(x_189, 2, x_184);
x_190 = lean_array_uset(x_170, x_183, x_189);
x_191 = lean_unsigned_to_nat(4u);
x_192 = lean_nat_mul(x_187, x_191);
x_193 = lean_unsigned_to_nat(3u);
x_194 = lean_nat_div(x_192, x_193);
lean_dec(x_192);
x_195 = lean_array_get_size(x_190);
x_196 = lean_nat_dec_le(x_194, x_195);
lean_dec(x_195);
lean_dec(x_194);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_197 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Rewrites_takeListAux___spec__4(x_190);
lean_ctor_set(x_7, 1, x_197);
lean_ctor_set(x_7, 0, x_187);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_167);
lean_ctor_set(x_198, 1, x_7);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_5);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_16, 0, x_200);
return x_16;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_ctor_set(x_7, 1, x_190);
lean_ctor_set(x_7, 0, x_187);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_167);
lean_ctor_set(x_201, 1, x_7);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_5);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_16, 0, x_203);
return x_16;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_204 = lean_box(0);
x_205 = lean_array_uset(x_170, x_183, x_204);
x_206 = lean_box(0);
x_207 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Rewrites_takeListAux___spec__7(x_4, x_206, x_184);
x_208 = lean_array_uset(x_205, x_183, x_207);
lean_ctor_set(x_7, 1, x_208);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_167);
lean_ctor_set(x_209, 1, x_7);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_5);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_16, 0, x_211);
return x_16;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; uint64_t x_215; uint64_t x_216; uint64_t x_217; uint64_t x_218; uint64_t x_219; uint64_t x_220; uint64_t x_221; size_t x_222; size_t x_223; size_t x_224; size_t x_225; size_t x_226; lean_object* x_227; uint8_t x_228; 
x_212 = lean_ctor_get(x_7, 0);
x_213 = lean_ctor_get(x_7, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_7);
x_214 = lean_array_get_size(x_213);
x_215 = lean_string_hash(x_4);
x_216 = 32;
x_217 = lean_uint64_shift_right(x_215, x_216);
x_218 = lean_uint64_xor(x_215, x_217);
x_219 = 16;
x_220 = lean_uint64_shift_right(x_218, x_219);
x_221 = lean_uint64_xor(x_218, x_220);
x_222 = lean_uint64_to_usize(x_221);
x_223 = lean_usize_of_nat(x_214);
lean_dec(x_214);
x_224 = 1;
x_225 = lean_usize_sub(x_223, x_224);
x_226 = lean_usize_land(x_222, x_225);
x_227 = lean_array_uget(x_213, x_226);
x_228 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Rewrites_takeListAux___spec__3(x_4, x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_229 = lean_unsigned_to_nat(1u);
x_230 = lean_nat_add(x_212, x_229);
lean_dec(x_212);
x_231 = lean_box(0);
x_232 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_232, 0, x_4);
lean_ctor_set(x_232, 1, x_231);
lean_ctor_set(x_232, 2, x_227);
x_233 = lean_array_uset(x_213, x_226, x_232);
x_234 = lean_unsigned_to_nat(4u);
x_235 = lean_nat_mul(x_230, x_234);
x_236 = lean_unsigned_to_nat(3u);
x_237 = lean_nat_div(x_235, x_236);
lean_dec(x_235);
x_238 = lean_array_get_size(x_233);
x_239 = lean_nat_dec_le(x_237, x_238);
lean_dec(x_238);
lean_dec(x_237);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_240 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Rewrites_takeListAux___spec__4(x_233);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_230);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_167);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_5);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_16, 0, x_244);
return x_16;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_230);
lean_ctor_set(x_245, 1, x_233);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_167);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_5);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_16, 0, x_248);
return x_16;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_249 = lean_box(0);
x_250 = lean_array_uset(x_213, x_226, x_249);
x_251 = lean_box(0);
x_252 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Rewrites_takeListAux___spec__7(x_4, x_251, x_227);
x_253 = lean_array_uset(x_250, x_226, x_252);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_212);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_167);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_5);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_16, 0, x_257);
return x_16;
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint64_t x_264; uint64_t x_265; uint64_t x_266; uint64_t x_267; uint64_t x_268; uint64_t x_269; uint64_t x_270; size_t x_271; size_t x_272; size_t x_273; size_t x_274; size_t x_275; lean_object* x_276; uint8_t x_277; 
x_258 = lean_ctor_get(x_16, 1);
lean_inc(x_258);
lean_dec(x_16);
x_259 = lean_array_push(x_6, x_1);
x_260 = lean_ctor_get(x_7, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_7, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_262 = x_7;
} else {
 lean_dec_ref(x_7);
 x_262 = lean_box(0);
}
x_263 = lean_array_get_size(x_261);
x_264 = lean_string_hash(x_4);
x_265 = 32;
x_266 = lean_uint64_shift_right(x_264, x_265);
x_267 = lean_uint64_xor(x_264, x_266);
x_268 = 16;
x_269 = lean_uint64_shift_right(x_267, x_268);
x_270 = lean_uint64_xor(x_267, x_269);
x_271 = lean_uint64_to_usize(x_270);
x_272 = lean_usize_of_nat(x_263);
lean_dec(x_263);
x_273 = 1;
x_274 = lean_usize_sub(x_272, x_273);
x_275 = lean_usize_land(x_271, x_274);
x_276 = lean_array_uget(x_261, x_275);
x_277 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Rewrites_takeListAux___spec__3(x_4, x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_278 = lean_unsigned_to_nat(1u);
x_279 = lean_nat_add(x_260, x_278);
lean_dec(x_260);
x_280 = lean_box(0);
x_281 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_281, 0, x_4);
lean_ctor_set(x_281, 1, x_280);
lean_ctor_set(x_281, 2, x_276);
x_282 = lean_array_uset(x_261, x_275, x_281);
x_283 = lean_unsigned_to_nat(4u);
x_284 = lean_nat_mul(x_279, x_283);
x_285 = lean_unsigned_to_nat(3u);
x_286 = lean_nat_div(x_284, x_285);
lean_dec(x_284);
x_287 = lean_array_get_size(x_282);
x_288 = lean_nat_dec_le(x_286, x_287);
lean_dec(x_287);
lean_dec(x_286);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_289 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Meta_Rewrites_takeListAux___spec__4(x_282);
if (lean_is_scalar(x_262)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_262;
}
lean_ctor_set(x_290, 0, x_279);
lean_ctor_set(x_290, 1, x_289);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_259);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_5);
lean_ctor_set(x_292, 1, x_291);
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_292);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_258);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
if (lean_is_scalar(x_262)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_262;
}
lean_ctor_set(x_295, 0, x_279);
lean_ctor_set(x_295, 1, x_282);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_259);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_5);
lean_ctor_set(x_297, 1, x_296);
x_298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_298, 0, x_297);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_258);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_300 = lean_box(0);
x_301 = lean_array_uset(x_261, x_275, x_300);
x_302 = lean_box(0);
x_303 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Meta_Rewrites_takeListAux___spec__7(x_4, x_302, x_276);
x_304 = lean_array_uset(x_301, x_275, x_303);
if (lean_is_scalar(x_262)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_262;
}
lean_ctor_set(x_305, 0, x_260);
lean_ctor_set(x_305, 1, x_304);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_259);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_5);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_307);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_258);
return x_309;
}
}
}
else
{
uint8_t x_310; 
lean_dec(x_5);
lean_dec(x_4);
x_310 = !lean_is_exclusive(x_16);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_311 = lean_ctor_get(x_16, 0);
lean_dec(x_311);
x_312 = lean_box(0);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_1);
lean_ctor_set(x_313, 1, x_312);
x_314 = lean_array_mk(x_313);
x_315 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_315, 0, x_314);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_6);
lean_ctor_set(x_316, 1, x_7);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_16, 0, x_318);
return x_16;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_319 = lean_ctor_get(x_16, 1);
lean_inc(x_319);
lean_dec(x_16);
x_320 = lean_box(0);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_1);
lean_ctor_set(x_321, 1, x_320);
x_322 = lean_array_mk(x_321);
x_323 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_323, 0, x_322);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_6);
lean_ctor_set(x_324, 1, x_7);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
x_326 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_319);
return x_327;
}
}
}
}
else
{
uint8_t x_328; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_328 = !lean_is_exclusive(x_16);
if (x_328 == 0)
{
return x_16;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_16, 0);
x_330 = lean_ctor_get(x_16, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_16);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
return x_331;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_18 = lean_box(x_17);
x_19 = lean_box(x_3);
lean_inc(x_14);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Rewrites_rwLemma___boxed), 12, 7);
lean_closure_set(x_20, 0, x_14);
lean_closure_set(x_20, 1, x_15);
lean_closure_set(x_20, 2, x_16);
lean_closure_set(x_20, 3, x_18);
lean_closure_set(x_20, 4, x_2);
lean_closure_set(x_20, 5, x_19);
lean_closure_set(x_20, 6, x_4);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg), 7, 2);
lean_closure_set(x_21, 0, x_14);
lean_closure_set(x_21, 1, x_20);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_22 = l_Lean_withoutModifyingState___at_Lean_Meta_Rewrites_takeListAux___spec__1(x_21, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_22, 0, x_28);
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_7);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec(x_22);
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_36, 3);
lean_inc(x_37);
lean_inc(x_36);
x_38 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_38, 0, x_36);
lean_inc(x_37);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg), 7, 2);
lean_closure_set(x_39, 0, x_37);
lean_closure_set(x_39, 1, x_38);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_40 = l_Lean_withoutModifyingState___at_Lean_Meta_Rewrites_takeListAux___spec__2(x_39, x_9, x_10, x_11, x_12, x_34);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; uint8_t x_59; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
x_45 = lean_array_get_size(x_44);
x_46 = lean_string_hash(x_42);
x_47 = 32;
x_48 = lean_uint64_shift_right(x_46, x_47);
x_49 = lean_uint64_xor(x_46, x_48);
x_50 = 16;
x_51 = lean_uint64_shift_right(x_49, x_50);
x_52 = lean_uint64_xor(x_49, x_51);
x_53 = lean_uint64_to_usize(x_52);
x_54 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_55 = 1;
x_56 = lean_usize_sub(x_54, x_55);
x_57 = lean_usize_land(x_53, x_56);
x_58 = lean_array_uget(x_44, x_57);
lean_dec(x_44);
x_59 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Rewrites_takeListAux___spec__3(x_42, x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_free_object(x_40);
lean_free_object(x_23);
x_60 = lean_box(0);
x_61 = l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__1(x_36, x_37, x_1, x_42, x_5, x_6, x_7, x_60, x_9, x_10, x_11, x_12, x_43);
lean_dec(x_1);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_42);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_6);
lean_ctor_set(x_62, 1, x_7);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_5);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_23, 0, x_63);
lean_ctor_set(x_40, 0, x_23);
return x_40;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; size_t x_75; size_t x_76; size_t x_77; size_t x_78; size_t x_79; lean_object* x_80; uint8_t x_81; 
x_64 = lean_ctor_get(x_40, 0);
x_65 = lean_ctor_get(x_40, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_40);
x_66 = lean_ctor_get(x_7, 1);
lean_inc(x_66);
x_67 = lean_array_get_size(x_66);
x_68 = lean_string_hash(x_64);
x_69 = 32;
x_70 = lean_uint64_shift_right(x_68, x_69);
x_71 = lean_uint64_xor(x_68, x_70);
x_72 = 16;
x_73 = lean_uint64_shift_right(x_71, x_72);
x_74 = lean_uint64_xor(x_71, x_73);
x_75 = lean_uint64_to_usize(x_74);
x_76 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_77 = 1;
x_78 = lean_usize_sub(x_76, x_77);
x_79 = lean_usize_land(x_75, x_78);
x_80 = lean_array_uget(x_66, x_79);
lean_dec(x_66);
x_81 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Rewrites_takeListAux___spec__3(x_64, x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_free_object(x_23);
x_82 = lean_box(0);
x_83 = l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__1(x_36, x_37, x_1, x_64, x_5, x_6, x_7, x_82, x_9, x_10, x_11, x_12, x_65);
lean_dec(x_1);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_64);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_6);
lean_ctor_set(x_84, 1, x_7);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_5);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_23, 0, x_85);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_23);
lean_ctor_set(x_86, 1, x_65);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_37);
lean_free_object(x_23);
lean_dec(x_36);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_40);
if (x_87 == 0)
{
return x_40;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_40, 0);
x_89 = lean_ctor_get(x_40, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_40);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_23, 0);
lean_inc(x_91);
lean_dec(x_23);
x_92 = lean_ctor_get(x_91, 3);
lean_inc(x_92);
lean_inc(x_91);
x_93 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_RewriteResult_ppResult___boxed), 6, 1);
lean_closure_set(x_93, 0, x_91);
lean_inc(x_92);
x_94 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at_Lean_Meta_SynthInstance_tryResolve___spec__1___rarg), 7, 2);
lean_closure_set(x_94, 0, x_92);
lean_closure_set(x_94, 1, x_93);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_95 = l_Lean_withoutModifyingState___at_Lean_Meta_Rewrites_takeListAux___spec__2(x_94, x_9, x_10, x_11, x_12, x_34);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; size_t x_108; size_t x_109; size_t x_110; size_t x_111; size_t x_112; lean_object* x_113; uint8_t x_114; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_7, 1);
lean_inc(x_99);
x_100 = lean_array_get_size(x_99);
x_101 = lean_string_hash(x_96);
x_102 = 32;
x_103 = lean_uint64_shift_right(x_101, x_102);
x_104 = lean_uint64_xor(x_101, x_103);
x_105 = 16;
x_106 = lean_uint64_shift_right(x_104, x_105);
x_107 = lean_uint64_xor(x_104, x_106);
x_108 = lean_uint64_to_usize(x_107);
x_109 = lean_usize_of_nat(x_100);
lean_dec(x_100);
x_110 = 1;
x_111 = lean_usize_sub(x_109, x_110);
x_112 = lean_usize_land(x_108, x_111);
x_113 = lean_array_uget(x_99, x_112);
lean_dec(x_99);
x_114 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Rewrites_takeListAux___spec__3(x_96, x_113);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_98);
x_115 = lean_box(0);
x_116 = l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__1(x_91, x_92, x_1, x_96, x_5, x_6, x_7, x_115, x_9, x_10, x_11, x_12, x_97);
lean_dec(x_1);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_96);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_6);
lean_ctor_set(x_117, 1, x_7);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_5);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
if (lean_is_scalar(x_98)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_98;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_97);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_121 = lean_ctor_get(x_95, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_95, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_123 = x_95;
} else {
 lean_dec_ref(x_95);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_22);
if (x_125 == 0)
{
return x_22;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_22, 0);
x_127 = lean_ctor_get(x_22, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_22);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_array_get_size(x_6);
x_16 = lean_nat_dec_le(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_6);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
x_26 = l_Lean_getRemainingHeartbeats(x_11, x_12, x_13);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_nat_dec_lt(x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_free_object(x_26);
lean_free_object(x_17);
lean_free_object(x_16);
x_32 = lean_box(0);
x_33 = lean_unbox(x_22);
lean_dec(x_22);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_34 = l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__3(x_1, x_19, x_33, x_23, x_4, x_24, x_25, x_32, x_9, x_10, x_11, x_12, x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_6 = x_18;
x_7 = x_43;
x_8 = lean_box(0);
x_13 = x_42;
goto _start;
}
}
else
{
uint8_t x_45; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
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
lean_object* x_49; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
lean_inc(x_24);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_24);
lean_ctor_set(x_16, 1, x_17);
lean_ctor_set(x_16, 0, x_49);
lean_ctor_set(x_26, 0, x_16);
return x_26;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_26, 0);
x_51 = lean_ctor_get(x_26, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_26);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
x_53 = lean_nat_dec_lt(x_50, x_52);
lean_dec(x_52);
lean_dec(x_50);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; 
lean_free_object(x_17);
lean_free_object(x_16);
x_54 = lean_box(0);
x_55 = lean_unbox(x_22);
lean_dec(x_22);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_56 = l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__3(x_1, x_19, x_55, x_23, x_4, x_24, x_25, x_54, x_9, x_10, x_11, x_12, x_51);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
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
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
lean_dec(x_57);
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
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_dec(x_56);
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
lean_dec(x_57);
x_6 = x_18;
x_7 = x_63;
x_8 = lean_box(0);
x_13 = x_62;
goto _start;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
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
lean_object* x_69; lean_object* x_70; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
lean_inc(x_24);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_24);
lean_ctor_set(x_16, 1, x_17);
lean_ctor_set(x_16, 0, x_69);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_16);
lean_ctor_set(x_70, 1, x_51);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_71 = lean_ctor_get(x_16, 0);
x_72 = lean_ctor_get(x_16, 1);
x_73 = lean_ctor_get(x_17, 0);
x_74 = lean_ctor_get(x_17, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_17);
x_75 = l_Lean_getRemainingHeartbeats(x_11, x_12, x_13);
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
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
x_80 = lean_nat_dec_lt(x_76, x_79);
lean_dec(x_79);
lean_dec(x_76);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; 
lean_dec(x_78);
lean_free_object(x_16);
x_81 = lean_box(0);
x_82 = lean_unbox(x_71);
lean_dec(x_71);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_83 = l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__3(x_1, x_19, x_82, x_72, x_4, x_73, x_74, x_81, x_9, x_10, x_11, x_12, x_77);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_dec(x_84);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
lean_dec(x_84);
x_6 = x_18;
x_7 = x_90;
x_8 = lean_box(0);
x_13 = x_89;
goto _start;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_92 = lean_ctor_get(x_83, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_83, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_94 = x_83;
} else {
 lean_dec_ref(x_83);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
lean_inc(x_73);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_73);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_73);
lean_ctor_set(x_97, 1, x_74);
lean_ctor_set(x_16, 1, x_97);
lean_ctor_set(x_16, 0, x_96);
if (lean_is_scalar(x_78)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_78;
}
lean_ctor_set(x_98, 0, x_16);
lean_ctor_set(x_98, 1, x_77);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_99 = lean_ctor_get(x_16, 0);
x_100 = lean_ctor_get(x_16, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_16);
x_101 = lean_ctor_get(x_17, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_17, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_103 = x_17;
} else {
 lean_dec_ref(x_17);
 x_103 = lean_box(0);
}
x_104 = l_Lean_getRemainingHeartbeats(x_11, x_12, x_13);
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
x_108 = lean_ctor_get(x_1, 1);
lean_inc(x_108);
x_109 = lean_nat_dec_lt(x_105, x_108);
lean_dec(x_108);
lean_dec(x_105);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; lean_object* x_112; 
lean_dec(x_107);
lean_dec(x_103);
x_110 = lean_box(0);
x_111 = lean_unbox(x_99);
lean_dec(x_99);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_112 = l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__3(x_1, x_19, x_111, x_100, x_4, x_101, x_102, x_110, x_9, x_10, x_11, x_12, x_106);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
lean_dec(x_113);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
lean_dec(x_112);
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
lean_dec(x_113);
x_6 = x_18;
x_7 = x_119;
x_8 = lean_box(0);
x_13 = x_118;
goto _start;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_121 = lean_ctor_get(x_112, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_112, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_123 = x_112;
} else {
 lean_dec_ref(x_112);
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
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
lean_inc(x_101);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_101);
if (lean_is_scalar(x_103)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_103;
}
lean_ctor_set(x_126, 0, x_101);
lean_ctor_set(x_126, 1, x_102);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
if (lean_is_scalar(x_107)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_107;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_106);
return x_128;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_inc(x_4);
x_14 = l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8(x_1, x_4, x_10, x_11, x_4, x_4, x_13, lean_box(0), x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Rewrites_takeListAux___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Meta_Rewrites_takeListAux___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__2(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___lambda__3(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at_Lean_Meta_Rewrites_takeListAux___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_takeListAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Rewrites_takeListAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_2);
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_4);
lean_ctor_set(x_14, 4, x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_1);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_5);
x_15 = lean_mk_empty_array_with_capacity(x_2);
lean_dec(x_2);
x_16 = lean_array_to_list(x_7);
x_17 = l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__3;
x_18 = l_Lean_Meta_Rewrites_takeListAux(x_14, x_17, x_15, x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_array_to_list(x_20);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_array_to_list(x_22);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_st_ref_get(x_11, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
x_19 = l_Lean_Meta_Rewrites_rewriteCandidates(x_1, x_2, x_4, x_5, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_getMaxHeartbeats(x_12, x_13, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_23, x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = l_Lean_getRemainingHeartbeats(x_12, x_13, x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_nat_mul(x_9, x_28);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(100u);
x_32 = lean_nat_div(x_30, x_31);
lean_dec(x_30);
x_33 = l_Lean_Meta_Rewrites_findRewrites___lambda__1(x_7, x_8, x_3, x_4, x_6, x_18, x_20, x_32, x_10, x_11, x_12, x_13, x_29);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = l_Lean_Meta_Rewrites_findRewrites___lambda__1(x_7, x_8, x_3, x_4, x_6, x_18, x_20, x_25, x_10, x_11, x_12, x_13, x_24);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_19, 0);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_19);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Rewrites_findRewrites___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Meta_Rewrites_findRewrites___lambda__1(x_14, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
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
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__1 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__1);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__2 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__2();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__2);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__3 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__3();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__3);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__4 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__4();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__4);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__5 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__5();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__5);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__6 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__6();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__6);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__7 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__7();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__7);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__8 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__8();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__8);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__9 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__9();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__9);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__10 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__10();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__10);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__11 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__11();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__11);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__12 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__12();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__12);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__13 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__13();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__13);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__14 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__14();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__14);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__15 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__15();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__15);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__16 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__16();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__16);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__17 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__17();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__17);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__18 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__18();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__18);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__19 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__19();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__19);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__20 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__20();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5____closed__20);
if (builtin) {res = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__1 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__1);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__2 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__2();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__2);
l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__3 = _init_l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__3();
lean_mark_persistent(l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46____closed__3);
if (builtin) {res = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_46_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1 = _init_l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_rewriteResultLemma___closed__1);
l_Lean_Meta_Rewrites_rewriteResultLemma___closed__2 = _init_l_Lean_Meta_Rewrites_rewriteResultLemma___closed__2();
lean_mark_persistent(l_Lean_Meta_Rewrites_rewriteResultLemma___closed__2);
l_Lean_Meta_Rewrites_forwardWeight = _init_l_Lean_Meta_Rewrites_forwardWeight();
lean_mark_persistent(l_Lean_Meta_Rewrites_forwardWeight);
l_Lean_Meta_Rewrites_backwardWeight = _init_l_Lean_Meta_Rewrites_backwardWeight();
lean_mark_persistent(l_Lean_Meta_Rewrites_backwardWeight);
l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___closed__1 = _init_l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_RwDirection_noConfusion___rarg___closed__1);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__4 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__4);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__5 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__1___closed__5);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__1 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__1);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__2 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__2);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__3 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__3);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__4 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__4);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__5 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__5);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__6 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__6);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__7 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__7);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__8 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__4___closed__8);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__5___closed__1 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__5___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__5___closed__1);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__6___closed__1 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__6___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_addImport___lambda__6___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_localHypotheses___spec__2___lambda__1___closed__2);
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
l_Lean_Meta_Rewrites_droppedKeys___closed__8 = _init_l_Lean_Meta_Rewrites_droppedKeys___closed__8();
lean_mark_persistent(l_Lean_Meta_Rewrites_droppedKeys___closed__8);
l_Lean_Meta_Rewrites_droppedKeys = _init_l_Lean_Meta_Rewrites_droppedKeys();
lean_mark_persistent(l_Lean_Meta_Rewrites_droppedKeys);
l_Lean_Meta_Rewrites_createModuleTreeRef___closed__1 = _init_l_Lean_Meta_Rewrites_createModuleTreeRef___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_createModuleTreeRef___closed__1);
if (builtin) {res = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_1273_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ExtState_default);
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__1 = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState___closed__1);
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_instInhabitedExtState);
if (builtin) {res = l_Lean_Meta_Rewrites_initFn____x40_Lean_Meta_Tactic_Rewrites___hyg_1333_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_ext);
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask = _init_l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Rewrites_0__Lean_Meta_Rewrites_constantsPerImportTask);
l_Lean_Meta_Rewrites_rwFindDecls___closed__1 = _init_l_Lean_Meta_Rewrites_rwFindDecls___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwFindDecls___closed__1);
l_Lean_Meta_Rewrites_rwFindDecls___closed__2 = _init_l_Lean_Meta_Rewrites_rwFindDecls___closed__2();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwFindDecls___closed__2);
l_Lean_Meta_Rewrites_solveByElim___lambda__3___closed__1 = _init_l_Lean_Meta_Rewrites_solveByElim___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_solveByElim___lambda__3___closed__1);
l_Lean_Meta_Rewrites_solveByElim___lambda__3___closed__2 = _init_l_Lean_Meta_Rewrites_solveByElim___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Rewrites_solveByElim___lambda__3___closed__2);
l_Lean_Meta_Rewrites_solveByElim___closed__1 = _init_l_Lean_Meta_Rewrites_solveByElim___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_solveByElim___closed__1);
l_Lean_Meta_Rewrites_solveByElim___closed__2 = _init_l_Lean_Meta_Rewrites_solveByElim___closed__2();
lean_mark_persistent(l_Lean_Meta_Rewrites_solveByElim___closed__2);
l_Lean_Meta_Rewrites_solveByElim___closed__3 = _init_l_Lean_Meta_Rewrites_solveByElim___closed__3();
lean_mark_persistent(l_Lean_Meta_Rewrites_solveByElim___closed__3);
l_Lean_Meta_Rewrites_solveByElim___closed__4 = _init_l_Lean_Meta_Rewrites_solveByElim___closed__4();
lean_mark_persistent(l_Lean_Meta_Rewrites_solveByElim___closed__4);
l_Lean_Meta_Rewrites_rwLemma___lambda__1___closed__1 = _init_l_Lean_Meta_Rewrites_rwLemma___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lambda__1___closed__1);
l_Lean_Meta_Rewrites_rwLemma___lambda__1___closed__2 = _init_l_Lean_Meta_Rewrites_rwLemma___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lambda__1___closed__2);
l_Lean_Meta_Rewrites_rwLemma___lambda__2___closed__1 = _init_l_Lean_Meta_Rewrites_rwLemma___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lambda__2___closed__1);
l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__1 = _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__1);
l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__2 = _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__2);
l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__3 = _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__3);
l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__4 = _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__4);
l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__5 = _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__5);
l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__6 = _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__6);
l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__7 = _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__7);
l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__8 = _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__8);
l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__9 = _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__9);
l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__10 = _init_l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__10();
lean_mark_persistent(l_Lean_Meta_Rewrites_rwLemma___lambda__3___closed__10);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1___closed__1();
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__3___lambda__1___closed__2();
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__1 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__1();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__1);
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__2 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__2();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__2);
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__3 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__3();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__3);
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__4 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__4();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__4);
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__5 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__5();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__5);
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__6 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__6();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__6);
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__7 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__7();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__7);
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__8 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__8();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__8);
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__9 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__9();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__9);
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__10 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__10();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__10);
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__11 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__11();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__11);
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__12 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__12();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__12);
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__13 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__13();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__13);
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__14 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__14();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__14);
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__15 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__15();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__15);
l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__16 = _init_l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__16();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Rewrites_rewriteCandidates___spec__6___closed__16);
l_Lean_Meta_Rewrites_rewriteCandidates___closed__1 = _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_rewriteCandidates___closed__1);
l_Lean_Meta_Rewrites_rewriteCandidates___closed__2 = _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__2();
lean_mark_persistent(l_Lean_Meta_Rewrites_rewriteCandidates___closed__2);
l_Lean_Meta_Rewrites_rewriteCandidates___closed__3 = _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__3();
lean_mark_persistent(l_Lean_Meta_Rewrites_rewriteCandidates___closed__3);
l_Lean_Meta_Rewrites_rewriteCandidates___closed__4 = _init_l_Lean_Meta_Rewrites_rewriteCandidates___closed__4();
lean_mark_persistent(l_Lean_Meta_Rewrites_rewriteCandidates___closed__4);
l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__1 = _init_l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__1);
l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__2 = _init_l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__2();
lean_mark_persistent(l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__2);
l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__3 = _init_l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__3();
lean_mark_persistent(l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__3);
l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__4 = _init_l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__4();
lean_mark_persistent(l_Lean_Meta_Rewrites_RewriteResult_newGoal___closed__4);
l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__1 = _init_l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__1);
l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__2 = _init_l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__2);
l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__3 = _init_l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Rewrites_findRewrites___lambda__1___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
