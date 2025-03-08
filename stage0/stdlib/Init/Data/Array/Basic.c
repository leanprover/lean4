// Lean compiler output
// Module: Init.Data.Array.Basic
// Imports: Init.WFTactics Init.Data.Nat.Basic Init.Data.Fin.Basic Init.Data.UInt.BasicAux Init.Data.Repr Init.Data.ToString.Basic Init.GetElem Init.Data.List.ToArrayImpl Init.Data.Array.Set
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
static lean_object* l_Array_swapAt_x21___rarg___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
static lean_object* l_Array_insertIdx_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_leftpad___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_eraseIdx_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_concatMapM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_takeWhile(lean_object*);
LEAN_EXPORT lean_object* l_Array_firstM_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_reduceOption___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_isPrefixOf(lean_object*);
LEAN_EXPORT lean_object* l_Array_take___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_foldl___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__15;
LEAN_EXPORT lean_object* l_Array_findRev_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrM_fold___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instAppend(lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithIndex(lean_object*);
LEAN_EXPORT lean_object* l_Array_uget___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Array_swapAt_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAll___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux(lean_object*);
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembership(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__5;
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds(lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx_loop(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_contains___spec__1(lean_object*);
static lean_object* l_Array_instRepr___rarg___closed__5;
static lean_object* l_term_x23_x5b___x2c_x5d___closed__14;
LEAN_EXPORT lean_object* l_Array_instLE___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlM_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_data(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx(lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseReps___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Array_filterMap___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6;
LEAN_EXPORT lean_object* l_Array_findSome_x21___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_instFunctor___closed__1;
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_leftpad(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatten___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapFinIdx___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f_loop(lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAll___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFn_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findM_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseP(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__3;
LEAN_EXPORT lean_object* l_Array_all(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatten___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_filter___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_foldl___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_replace(lean_object*);
LEAN_EXPORT lean_object* l_Array_getMax_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__12;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_getEvenElems___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_2765_;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__2___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__7;
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_erase___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseReps___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_swapAt_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instBEq___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_flatten(lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__4;
LEAN_EXPORT lean_object* l_Array_zip___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx_loop___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_swap_x21(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_popWhile(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_map(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_uset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_drop(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Array_any___spec__2___rarg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_reverse(lean_object*);
LEAN_EXPORT lean_object* l_Array_swap_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRev_x3f___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_allDiff___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_flatten___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_flatMap___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instLT___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterMap___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___lambda__2(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instFunctor___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_append___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_allDiff(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyM_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_swapAt_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_find_x3f___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize(lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAll_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Array_swapAt_x21___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_reduceOption___spec__2___rarg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getIdx_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_elem___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_indexOf_x3f___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4;
LEAN_EXPORT lean_object* l_Array_sum(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Array_contains___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Array_instRepr___rarg___closed__8;
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__2___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseP___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_swapIfInBounds___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyM_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRev_x3f___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_all___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_unzip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_sum___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Array_reduceOption___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop(lean_object*);
LEAN_EXPORT lean_object* l_Array_shrink(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x21___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Array_insertIdx_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFn(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqv___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_drop___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWith___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_sum___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM(lean_object*, lean_object*, lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__4;
LEAN_EXPORT lean_object* l_Array_back(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findSomeRev_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mkArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_swapAt(lean_object*);
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembership___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyM_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Array_reduceOption___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_any___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds(lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__5;
LEAN_EXPORT lean_object* l_Array_getIdx_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
static lean_object* l_Array_instFunctor___closed__2;
LEAN_EXPORT lean_object* l_Array_findSome_x3f___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSome_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_firstM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFn___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_all___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Array_instRepr___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_count___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_find_x3f___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_reduceOption___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forRevM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_split___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1;
LEAN_EXPORT lean_object* l_Array_instMembership(lean_object*);
LEAN_EXPORT lean_object* l_Array_concatMap___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__10;
LEAN_EXPORT lean_object* l_Array_instRepr___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instBEq(lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqv(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_unzip___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_foldrM_fold(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modify(lean_object*);
LEAN_EXPORT lean_object* l_Array_take___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_split___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlM_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instHAppendList(lean_object*);
LEAN_EXPORT lean_object* l_Array_take(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlM_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_foldl___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_swapAt_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdx___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_partition___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_12376_;
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_2860_;
LEAN_EXPORT lean_object* l_Array_mapM_map___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_singleton(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_flatMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_range___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f_loop___rarg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_map(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findRev_x3f___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_concatMapM___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_eraseIdx_x21___rarg___closed__3;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
lean_object* l_panic___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_append___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instToString(lean_object*);
LEAN_EXPORT lean_object* l_Array_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_all___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_data___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findSomeRev_x3f___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_any(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_map___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Array_instRepr___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___lambda__2(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSome_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_elem___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlM_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getMax_x3f(lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__10;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_eraseReps___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_unzip___rarg(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT uint8_t l_Array_instBEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_contains___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__2___rarg(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__14;
LEAN_EXPORT uint8_t l_Array_isPrefixOf___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_partition___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toListAppend___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Array_range___closed__1;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqv___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_appendList(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_takeWhile___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFn___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_allM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyM_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Array_eraseIdx_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findSomeRev_x3f___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__7;
LEAN_EXPORT lean_object* l_Array_indexOf_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_append___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modifyOp(lean_object*);
LEAN_EXPORT lean_object* l_Array_takeWhile_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_eraseReps___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filter___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_findSomeM_x3f___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_rightpad___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_indexOfAux(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertAt_x21(lean_object*);
static lean_object* l_Array_instGetElemUSizeLtNatToNatSize___closed__1;
LEAN_EXPORT lean_object* l_Array_back_x3f___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdx___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_drop___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_partition___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instFunctor;
LEAN_EXPORT lean_object* l_Array_findSome_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapFinIdx___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_back_x3f___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_replace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__19;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_findSome_x21___rarg___closed__3;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_11923_;
LEAN_EXPORT lean_object* l_Array_instLT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMap___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_back_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMap___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFn_go(lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAll_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13;
LEAN_EXPORT lean_object* l_Array_modifyOp___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_unzip___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldr___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipIdx(lean_object*);
static lean_object* l_Array_insertIdx_x21___rarg___closed__2;
static lean_object* l_term_x23_x5b___x2c_x5d___closed__12;
LEAN_EXPORT lean_object* l_Array_foldl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_concatMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMap___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_count___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Array_all___spec__2___rarg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertAt_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_find_x3f___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_firstM___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_instHAppendList___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterMap___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_Array_data___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__2___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, uint8_t);
LEAN_EXPORT lean_object* lean_array_to_list_impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_countP___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWith___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__11;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_rightpad(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Array_eraseIdx_x21___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipIdx___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modify___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_count___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAux___at_Array_zip___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__9;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_find_x3f___spec__1(lean_object*);
static lean_object* l_Array_findIdxM_x3f___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1(lean_object*, lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__1;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__2___rarg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_filter(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_findSome_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMap___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_findRevM_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Array_insertIdx_x21___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_range(lean_object*);
LEAN_EXPORT lean_object* l_Array_forRevM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_back_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_indexOfAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reverse_loop(lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__11;
LEAN_EXPORT lean_object* l_Array_foldl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg___lambda__2(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_count___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_sequenceMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_range___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertAt(lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_partition(lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithIndex___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_rightpad___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Array_eraseIdx_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_forM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_partition___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_get_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_back_x21___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSome_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_sum___spec__2___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Array_getEvenElems___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_range_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_range_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Array_appendList___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Array_findSome_x21___rarg___closed__1;
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__14;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_find_x3f___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_instRepr___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_zipIdx___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, uint8_t);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__10;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__13;
LEAN_EXPORT lean_object* l_Array_pop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdx___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Array_instRepr___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_erase(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_zipIdx___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_countP(lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_instFunctor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceOption___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_getEvenElems___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__16;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_countP___spec__2___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_countP___spec__2(lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__2;
static lean_object* l_term_x23_x5b___x2c_x5d___closed__13;
static lean_object* l_Array_instRepr___rarg___closed__3;
LEAN_EXPORT lean_object* l_Array_reduceOption___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_modify___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__11;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_countP___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_unzip___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEmpty___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_instForM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_append___rarg___boxed(lean_object*, lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__16;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_sum___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipIdx___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_split___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instForM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdx___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Array_filterMap___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_any___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatten___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_filter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Array_appendCore___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMap___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapFinIdx___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__8;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x21___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__8;
LEAN_EXPORT lean_object* l_Array_reverse_loop___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__2(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_elem(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filter___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterRevM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_count___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_eraseReps___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterRevM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_sum___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filter___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_instAppend___closed__1;
LEAN_EXPORT lean_object* l_Array_filterRevM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlM_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__6;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg___lambda__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_count___spec__2___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_usize___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findRev_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_zipIdx___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_map___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instToString___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAux___at_Array_zip___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_range_x27___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_filterRevM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instRepr___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_map___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMap___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x3f___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_takeWhile_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__3;
LEAN_EXPORT lean_object* l_Array_appendList___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___rarg___lambda__1(lean_object*, size_t, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getMax_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_getEvenElems___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Array_instRepr___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_singleton___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_swapAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx_x3f(lean_object*);
static lean_object* l_Array_swapAt_x21___rarg___closed__4;
LEAN_EXPORT lean_object* l_Array_append(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_countP___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Id_instMonad;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux(lean_object*);
LEAN_EXPORT lean_object* l_Array_shrink_loop___rarg(lean_object*, lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Array_filterMap___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertAt_x21___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_instRepr___rarg___closed__6;
LEAN_EXPORT lean_object* l_Array_toListAppend(lean_object*);
LEAN_EXPORT lean_object* l_Array_shrink_loop(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_firstM_go___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_flatMapM___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17;
LEAN_EXPORT lean_object* l_Array_getEvenElems___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(lean_object*);
LEAN_EXPORT lean_object* l_Array_swap_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_allDiff___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_firstM_go___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAll(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_back___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_back_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Array_appendList___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_get_x3f___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_Array_data(lean_object*);
LEAN_EXPORT lean_object* l_Array_zip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux(lean_object*);
LEAN_EXPORT lean_object* l_Array_isPrefixOf___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_find_x3f___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_concatMap___rarg(lean_object*, lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__17;
LEAN_EXPORT lean_object* l_Array_back___rarg(lean_object*, lean_object*);
static lean_object* l_Array_swapAt_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_findIdx___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__20;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_count___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_flatten___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_partition___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_any___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT uint8_t l_Array_all___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Array_firstM_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_takeWhile_go(lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modifyOp___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_map___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_any___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_flatMap___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Array_instRepr___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_instRepr___rarg___closed__7;
static lean_object* l_Array_instFunctor___closed__3;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_split___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMap___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_idxOfAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_flatMapM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__6;
LEAN_EXPORT lean_object* l_Array_sum___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_instRepr___rarg___closed__4;
LEAN_EXPORT lean_object* l_Array_ofFn_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAll_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_countP___spec__1(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Array_all___spec__1___rarg(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__2;
LEAN_EXPORT lean_object* l_Array_findM_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739_;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_countP___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_swapAt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__12;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRev_x3f___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_all___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_all___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__15;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_sum___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_count___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertAt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithIndex___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__16;
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_shrink___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__2___rarg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_indexOfAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toListAppend___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithAux___at_Array_zip___spec__1(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_count(lean_object*);
LEAN_EXPORT lean_object* l_Array_findM_x3f(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getIdx_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_instToString___rarg___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_any___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1747_;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_countP___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseReps(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_unzip___spec__1___rarg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_range___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_map___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_instRepr(lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__9;
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findIdx(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_swap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdx___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWith(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_sum___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrM_fold___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_allM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_find_x3f___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_split___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_any___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x21___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_indexOf_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_leftpad___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_find_x3f___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Array_takeWhile___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__17;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMap___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_getEvenElems(lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__8;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Array_any___spec__1___rarg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_allM(lean_object*, lean_object*);
static lean_object* l_term_x23_x5b___x2c_x5d___closed__18;
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdx___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdx___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_popWhile___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_term_x23_x5b___x2c_x5d;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_reduceOption(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Array_reduceOption___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__15;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forRevM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdx_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___lambda__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterMap___spec__2___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains(lean_object*);
LEAN_EXPORT lean_object* l_Array_eraseIdx(lean_object*);
LEAN_EXPORT lean_object* l_Array_find_x3f___rarg(lean_object*, lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__7;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_split(lean_object*);
static lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x3f___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_partition___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_unzip___rarg___boxed(lean_object*);
static lean_object* l_Array_getEvenElems___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__1;
static lean_object* l_term_x23_x5b___x2c_x5d___closed__21;
LEAN_EXPORT lean_object* l_Array_mapM_map___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_range_x27___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_find_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_get_x3f___rarg(lean_object*, lean_object*);
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term#[_,]", 9, 9);
return x_1;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_term_x23_x5b___x2c_x5d___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_term_x23_x5b___x2c_x5d___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_x23_x5b___x2c_x5d___closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withoutPosition", 15, 15);
return x_1;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_term_x23_x5b___x2c_x5d___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_term_x23_x5b___x2c_x5d___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_term_x23_x5b___x2c_x5d___closed__10;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_x23_x5b___x2c_x5d___closed__12;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_term_x23_x5b___x2c_x5d___closed__11;
x_2 = l_term_x23_x5b___x2c_x5d___closed__14;
x_3 = l_term_x23_x5b___x2c_x5d___closed__13;
x_4 = 1;
x_5 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_term_x23_x5b___x2c_x5d___closed__8;
x_2 = l_term_x23_x5b___x2c_x5d___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_term_x23_x5b___x2c_x5d___closed__4;
x_2 = l_term_x23_x5b___x2c_x5d___closed__6;
x_3 = l_term_x23_x5b___x2c_x5d___closed__16;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_x23_x5b___x2c_x5d___closed__18;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_term_x23_x5b___x2c_x5d___closed__4;
x_2 = l_term_x23_x5b___x2c_x5d___closed__17;
x_3 = l_term_x23_x5b___x2c_x5d___closed__19;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_term_x23_x5b___x2c_x5d___closed__2;
x_2 = lean_unsigned_to_nat(1024u);
x_3 = l_term_x23_x5b___x2c_x5d___closed__20;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_term_x23_x5b___x2c_x5d() {
_start:
{
lean_object* x_1; 
x_1 = l_term_x23_x5b___x2c_x5d___closed__21;
return x_1;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1;
x_2 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2;
x_3 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__3;
x_4 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("List.toArray", 12, 12);
return x_1;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("List", 4, 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toArray", 7, 7);
return x_1;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__8;
x_2 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term[_]", 7, 7);
return x_1;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_term_x23_x5b___x2c_x5d___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 5);
lean_inc(x_11);
x_12 = 0;
x_13 = l_Lean_SourceInfo_fromRef(x_11, x_12);
lean_dec(x_11);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__10;
x_17 = l_Lean_addMacroScope(x_15, x_16, x_14);
x_18 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__7;
x_19 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__12;
lean_inc(x_13);
x_20 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_19);
x_21 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17;
lean_inc(x_13);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_24 = l_Array_appendCore___rarg(x_23, x_10);
lean_dec(x_10);
x_25 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__14;
lean_inc(x_13);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_24);
x_27 = l_term_x23_x5b___x2c_x5d___closed__18;
lean_inc(x_13);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_27);
x_29 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__16;
lean_inc(x_13);
x_30 = l_Lean_Syntax_node3(x_13, x_29, x_22, x_26, x_28);
lean_inc(x_13);
x_31 = l_Lean_Syntax_node1(x_13, x_25, x_30);
x_32 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__5;
x_33 = l_Lean_Syntax_node2(x_13, x_32, x_20, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Array_data___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_to_list(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_data(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_data___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_4, x_6, x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__List_toArrayAux_match__1_splitter___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_instMembership(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_Basic_0__GetElem_x3f_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_Array_data___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_to_list(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_Array_data(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_Array_data___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_usize___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_array_size(x_2);
lean_dec(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_uget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_array_uget(x_2, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_uset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_array_uset(x_2, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_pop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_pop(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mkArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_mk_array(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1;
x_2 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2;
x_3 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__1;
x_4 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1;
x_2 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2;
x_3 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__1;
x_4 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticGet_elem_tactic", 21, 21);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("get_elem_tactic", 15, 15);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__8;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_2 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__9;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__7;
x_3 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__10;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_2 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__14;
x_3 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__12;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_2 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__5;
x_3 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__14;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_2 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__15;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__3;
x_3 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__16;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__17;
return x_1;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_1747_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__17;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_swap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_array_fswap(x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_swapIfInBounds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_swap(x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_swap_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_swap(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_swap_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_swap_x21___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_swap_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_swap_x21___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Array_instGetElemUSizeLtNatToNatSize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_uget___boxed), 4, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_instGetElemUSizeLtNatToNatSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_instGetElemUSizeLtNatToNatSize___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_instEmptyCollection(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_instInhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_isEmpty___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_isEmpty___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_5, x_9);
lean_dec(x_5);
x_11 = lean_array_fget(x_1, x_10);
x_12 = lean_array_fget(x_2, x_10);
lean_inc(x_4);
x_13 = lean_apply_2(x_4, x_11, x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_4);
x_15 = 0;
return x_15;
}
else
{
x_3 = lean_box(0);
x_5 = x_10;
x_6 = lean_box(0);
goto _start;
}
}
else
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = 1;
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_isEqvAux___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_isEqv___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = l_Array_isEqvAux___rarg(x_1, x_2, lean_box(0), x_3, x_4, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_isEqv___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_isEqv___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqv___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_instBEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
lean_dec(x_1);
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = l_Array_isEqvAux___rarg(x_2, x_3, lean_box(0), x_1, x_4, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_instBEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_instBEq___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_instBEq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_instBEq___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_1);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
lean_inc(x_2);
x_8 = lean_apply_1(x_2, x_3);
x_9 = lean_array_push(x_4, x_8);
x_3 = x_7;
x_4 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_ofFn_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_ofFn_go___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_ofFn_go___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_mk_empty_array_with_capacity(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_ofFn_go___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_ofFn___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_ofFn___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_ofFn___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_range___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Array_range___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_range___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_range(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_range___closed__1;
x_3 = l_Array_ofFn___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_range___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_range___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_range___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_range(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_mul(x_1, x_3);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Array_range_x27___lambda__1___boxed), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = l_Array_ofFn___rarg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_range_x27___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_range_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_range_x27(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_singleton___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_array_mk(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_singleton(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_singleton___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_3, x_4);
lean_dec(x_3);
x_6 = lean_array_get(x_1, x_2, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_back_x21___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_back_x21___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_back_x21___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_2765_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__17;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_back___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_3, x_4);
lean_dec(x_3);
x_6 = lean_array_fget(x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_back(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_back___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_back___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_back___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
x_5 = lean_nat_dec_lt(x_4, x_2);
lean_dec(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_fget(x_1, x_4);
lean_dec(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_back_x3f___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_back_x3f___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back_x3f___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_get_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_get_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_get_x3f___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_get_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_get_x3f___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_2860_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__17;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_array_fget(x_1, x_2);
x_6 = lean_array_fset(x_1, x_2, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_swapAt___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_swapAt___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at_Array_swapAt_x21___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_panic_fn(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at_Array_swapAt_x21___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panic___at_Array_swapAt_x21___spec__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Array_swapAt_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("index ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_swapAt_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" out of bounds", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Array_swapAt_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Array.Basic", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Array_swapAt_x21___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Array.swapAt!", 13, 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_swapAt_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_7 = l_Array_swapAt_x21___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Array_swapAt_x21___rarg___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Array_swapAt_x21___rarg___closed__3;
x_12 = l_Array_swapAt_x21___rarg___closed__4;
x_13 = lean_unsigned_to_nat(316u);
x_14 = lean_unsigned_to_nat(4u);
x_15 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_11, x_12, x_13, x_14, x_10);
lean_dec(x_10);
x_16 = l_panic___at_Array_swapAt_x21___spec__1___rarg(x_1, x_3, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_array_fget(x_1, x_2);
x_18 = lean_array_fset(x_1, x_2, x_3);
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_swapAt_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_swapAt_x21___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_shrink_loop___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
x_7 = lean_array_pop(x_2);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Array_shrink_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_shrink_loop___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_sub(x_3, x_2);
lean_dec(x_3);
x_5 = l_Array_shrink_loop___rarg(x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_shrink(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_shrink___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_shrink___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_shrink___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_take___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_extract___rarg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_take(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_take___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_take___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_take___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_drop___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = l_Array_extract___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_drop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_drop___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_drop___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_drop___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_array_fset(x_2, x_3, x_4);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_box(0);
x_12 = lean_array_fset(x_2, x_3, x_11);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_apply_1(x_4, x_10);
x_15 = lean_alloc_closure((void*)(l_Array_modifyMUnsafe___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_3);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_modifyMUnsafe___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_modifyMUnsafe___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_modifyMUnsafe___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_modify___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_1, x_2, x_7);
x_9 = lean_apply_1(x_3, x_6);
x_10 = lean_array_fset(x_8, x_2, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_modify(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_modify___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_modify___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_modify___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_1, x_2, x_7);
x_9 = lean_apply_1(x_3, x_6);
x_10 = lean_array_fset(x_8, x_2, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_modifyOp___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_modifyOp___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_modifyOp___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___rarg___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_7);
return x_10;
}
else
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = l_Array_forIn_x27Unsafe_loop___rarg(x_1, x_3, x_4, x_5, x_13, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_array_uget(x_2, x_5);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_3);
x_13 = lean_apply_3(x_3, x_11, lean_box(0), x_6);
x_14 = lean_box_usize(x_5);
x_15 = lean_box_usize(x_4);
x_16 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_15);
x_17 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forIn_x27Unsafe_loop___rarg___lambda__1(x_1, x_7, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forIn_x27Unsafe_loop___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_array_size(x_2);
x_6 = 0;
x_7 = l_Array_forIn_x27Unsafe_loop___rarg(x_1, x_2, x_4, x_5, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Array_forIn_x27_loop___rarg(x_1, x_2, x_3, x_4, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_sub(x_12, x_9);
lean_dec(x_12);
x_14 = lean_nat_sub(x_13, x_10);
lean_dec(x_13);
x_15 = lean_array_fget(x_2, x_14);
lean_dec(x_14);
lean_inc(x_3);
x_16 = lean_apply_3(x_3, x_15, lean_box(0), x_6);
x_17 = lean_alloc_closure((void*)(l_Array_forIn_x27_loop___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_10);
x_18 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_apply_2(x_20, lean_box(0), x_6);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_forIn_x27_loop___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forIn_x27_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forIn_x27_loop___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembership___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_array_size(x_2);
x_6 = 0;
x_7 = l_Array_forIn_x27Unsafe_loop___rarg(x_1, x_2, x_4, x_5, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_instForIn_x27InferInstanceMembership(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_instForIn_x27InferInstanceMembership___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
x_10 = lean_apply_2(x_2, x_6, x_9);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_3);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_4);
x_12 = lean_nat_dec_le(x_6, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_3);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_5);
x_17 = lean_usize_of_nat(x_6);
x_18 = l_Array_foldlMUnsafe_fold___rarg(x_1, x_2, x_4, x_16, x_17, x_3);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlMUnsafe___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_1, x_8);
x_10 = l_Array_foldlM_loop___rarg(x_2, x_3, x_4, x_5, lean_box(0), x_6, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_7, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_8);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_6, x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_array_fget(x_3, x_7);
lean_inc(x_2);
x_19 = lean_apply_2(x_2, x_8, x_18);
x_20 = lean_alloc_closure((void*)(l_Array_foldlM_loop___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_20, 0, x_7);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_4);
lean_closure_set(x_20, 5, x_16);
x_21 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_19, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_apply_2(x_23, lean_box(0), x_8);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlM_loop___rarg___boxed), 8, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldlM_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlM_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_foldlM_loop___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 1;
x_10 = lean_usize_sub(x_4, x_9);
x_11 = lean_array_uget(x_3, x_10);
lean_inc(x_2);
x_12 = lean_apply_2(x_2, x_11, x_6);
x_13 = lean_box_usize(x_10);
x_14 = lean_box_usize(x_5);
x_15 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___rarg___boxed), 6, 5);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_13);
lean_closure_set(x_15, 4, x_14);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_12, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldrMUnsafe_fold___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_le(x_5, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_6, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_3);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_14 = lean_usize_of_nat(x_6);
x_15 = l_Array_foldrMUnsafe_fold___rarg(x_1, x_2, x_4, x_13, x_14, x_3);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_7);
x_16 = lean_nat_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_3);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_usize_of_nat(x_5);
x_21 = lean_usize_of_nat(x_6);
x_22 = l_Array_foldrMUnsafe_fold___rarg(x_1, x_2, x_4, x_20, x_21, x_3);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldrMUnsafe___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_5, x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_fget(x_3, x_12);
lean_inc(x_2);
x_15 = lean_apply_2(x_2, x_14, x_7);
x_16 = lean_alloc_closure((void*)(l_Array_foldrM_fold___rarg___boxed), 7, 6);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_12);
lean_closure_set(x_16, 5, lean_box(0));
x_17 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_2(x_19, lean_box(0), x_7);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_apply_2(x_22, lean_box(0), x_7);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldrM_fold___rarg___boxed), 7, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrM_fold___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldrM_fold___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = lean_array_uset(x_2, x_1, x_6);
x_10 = l_Array_mapMUnsafe_map___rarg(x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_array_uget(x_5, x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_5, x_4, x_11);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_10);
x_15 = lean_box_usize(x_4);
x_16 = lean_box_usize(x_3);
x_17 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_12);
lean_closure_set(x_17, 2, x_1);
lean_closure_set(x_17, 3, x_2);
lean_closure_set(x_17, 4, x_16);
x_18 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___rarg___boxed), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___rarg(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_array_size(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___rarg(x_1, x_2, x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_mapMUnsafe___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_map___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = lean_array_push(x_2, x_6);
x_10 = l_Array_mapM_map___rarg(x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_map___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_array_fget(x_3, x_4);
lean_inc(x_2);
x_13 = lean_apply_1(x_2, x_12);
x_14 = lean_alloc_closure((void*)(l_Array_mapM_map___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_5);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_2);
lean_closure_set(x_14, 4, x_3);
x_15 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapM_map(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_mapM_map___rarg), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_map___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapM_map___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_array_size(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___rarg(x_1, x_2, x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_sequenceMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_sequenceMap___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_1, x_8);
x_10 = lean_array_push(x_2, x_7);
x_11 = l_Array_mapFinIdxM_map___rarg(x_3, x_4, x_5, x_6, x_9, lean_box(0), x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_array_fget(x_2, x_5);
lean_inc(x_3);
lean_inc(x_5);
x_14 = lean_apply_3(x_3, x_5, x_13, lean_box(0));
x_15 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_7);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_2);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_11);
x_16 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___rarg___boxed), 7, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapFinIdxM_map___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapFinIdxM_map___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_mapFinIdxM_map___rarg(x_1, x_2, x_3, x_4, x_6, lean_box(0), x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_mapFinIdxM___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = lean_array_push(x_2, x_8);
x_12 = l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1___rarg(x_3, x_4, x_5, x_6, x_7, x_10, lean_box(0), x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_fget(x_4, x_6);
lean_inc(x_2);
lean_inc(x_6);
x_15 = lean_apply_2(x_2, x_6, x_14);
x_16 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_16, 0, x_6);
lean_closure_set(x_16, 1, x_8);
lean_closure_set(x_16, 2, x_1);
lean_closure_set(x_16, 3, x_2);
lean_closure_set(x_16, 4, x_3);
lean_closure_set(x_16, 5, x_4);
lean_closure_set(x_16, 6, x_12);
x_17 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_2(x_19, lean_box(0), x_8);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1___rarg___boxed), 8, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_7 = l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1___rarg(x_1, x_2, x_3, x_3, x_4, x_6, lean_box(0), x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_mapIdxM___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapFinIdxM_map___at_Array_mapIdxM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_firstM_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = l_Array_firstM_go___rarg(x_2, x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_firstM_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_7, lean_box(0));
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_3, x_4);
lean_inc(x_2);
x_10 = lean_apply_1(x_2, x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Array_firstM_go___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_3(x_12, lean_box(0), x_10, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_firstM_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_firstM_go___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_firstM_go___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_firstM_go___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_firstM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_firstM_go___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_firstM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_firstM___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
lean_inc(x_6);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_6);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_4);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_apply_2(x_13, lean_box(0), x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_apply_2(x_21, lean_box(0), x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_11);
return x_14;
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_9, x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_15 = lean_array_uget(x_7, x_9);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_2);
x_17 = lean_apply_1(x_2, x_15);
lean_inc(x_4);
lean_inc(x_6);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__2), 4, 3);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_6);
lean_closure_set(x_18, 2, x_4);
lean_inc(x_4);
x_19 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_17, x_18);
x_20 = lean_box_usize(x_9);
x_21 = lean_box_usize(x_8);
x_22 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__3___boxed), 10, 9);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_3);
lean_closure_set(x_22, 4, x_4);
lean_closure_set(x_22, 5, x_5);
lean_closure_set(x_22, 6, x_6);
lean_closure_set(x_22, 7, x_7);
lean_closure_set(x_22, 8, x_21);
x_23 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_19, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___boxed), 10, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_12);
return x_15;
}
}
}
static lean_object* _init_l_Array_findSomeM_x3f___rarg___closed__1() {
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
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_array_size(x_3);
x_8 = 0;
x_9 = l_Array_findSomeM_x3f___rarg___closed__1;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_9, x_3, x_7, x_8, x_9);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___rarg___lambda__2), 4, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_6);
lean_closure_set(x_11, 2, x_4);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__3(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeM_x3f___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findSomeM_x3f___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
x_10 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_findSomeM_x3f___spec__1___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_7);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_apply_2(x_13, lean_box(0), x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_11);
return x_14;
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_9, x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_15 = lean_array_uget(x_7, x_9);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_2);
lean_inc(x_15);
x_17 = lean_apply_1(x_2, x_15);
lean_inc(x_4);
lean_inc(x_6);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_6);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_15);
lean_inc(x_4);
x_19 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_17, x_18);
x_20 = lean_box_usize(x_9);
x_21 = lean_box_usize(x_8);
x_22 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg___lambda__2___boxed), 10, 9);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_3);
lean_closure_set(x_22, 4, x_4);
lean_closure_set(x_22, 5, x_5);
lean_closure_set(x_22, 6, x_6);
lean_closure_set(x_22, 7, x_7);
lean_closure_set(x_22, 8, x_21);
x_23 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_19, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg___boxed), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_array_size(x_3);
x_8 = 0;
x_9 = l_Array_findSomeM_x3f___rarg___closed__1;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_9, x_3, x_7, x_8, x_9);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Array_findM_x3f___rarg___lambda__1), 4, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_6);
lean_closure_set(x_11, 2, x_4);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_findM_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findM_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg___lambda__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Array_findM_x3f___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_4, x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
lean_inc(x_9);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
x_12 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_7);
lean_closure_set(x_12, 2, x_9);
x_13 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
lean_inc(x_3);
x_10 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_4);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_apply_2(x_13, lean_box(0), x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__4(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_11);
return x_14;
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_9, x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_array_uget(x_7, x_9);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
lean_inc(x_2);
x_18 = lean_apply_1(x_2, x_15);
lean_inc(x_4);
lean_inc(x_6);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__3___boxed), 5, 4);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_6);
lean_closure_set(x_19, 2, x_4);
lean_closure_set(x_19, 3, x_17);
lean_inc(x_4);
x_20 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_18, x_19);
x_21 = lean_box_usize(x_9);
x_22 = lean_box_usize(x_8);
x_23 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__4___boxed), 10, 9);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_21);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_3);
lean_closure_set(x_23, 4, x_4);
lean_closure_set(x_23, 5, x_5);
lean_closure_set(x_23, 6, x_6);
lean_closure_set(x_23, 7, x_7);
lean_closure_set(x_23, 8, x_22);
x_24 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_20, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___boxed), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Array_findSomeM_x3f___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_12);
return x_15;
}
}
}
static lean_object* _init_l_Array_findIdxM_x3f___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_array_size(x_3);
x_8 = 0;
x_9 = l_Array_findIdxM_x3f___rarg___closed__1;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_3, x_7, x_8, x_9);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___rarg___lambda__1), 4, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_6);
lean_closure_set(x_11, 2, x_4);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_findIdxM_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findIdxM_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__3(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___lambda__4(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Array_findIdxM_x3f___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_anyMUnsafe_any___rarg(x_2, x_3, x_4, x_8, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_apply_2(x_11, lean_box(0), x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_box_usize(x_4);
x_11 = lean_box_usize(x_5);
x_12 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_11);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_apply_2(x_15, lean_box(0), x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Array_anyMUnsafe_any___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___rarg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_le(x_5, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_4, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_apply_2(x_16, lean_box(0), x_18);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_usize_of_nat(x_4);
x_21 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_22 = l_Array_anyMUnsafe_any___rarg(x_1, x_2, x_3, x_20, x_21);
return x_22;
}
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
lean_dec(x_12);
x_23 = lean_usize_of_nat(x_4);
x_24 = lean_usize_of_nat(x_5);
x_25 = l_Array_anyMUnsafe_any___rarg(x_1, x_2, x_3, x_23, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyMUnsafe___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_anyMUnsafe___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = l_Array_anyM_loop___rarg(x_2, x_3, x_4, x_5, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_apply_2(x_11, lean_box(0), x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_apply_2(x_9, lean_box(0), x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_fget(x_3, x_6);
lean_inc(x_2);
x_15 = lean_apply_1(x_2, x_14);
x_16 = lean_alloc_closure((void*)(l_Array_anyM_loop___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_16, 0, x_6);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_4);
x_17 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyM_loop___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyM_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Array_anyM_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___lambda__1(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = 1;
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_4, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_apply_2(x_9, lean_box(0), x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___lambda__2(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, uint8_t x_7) {
_start:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 1;
x_9 = lean_usize_add(x_1, x_8);
x_10 = l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg(x_2, x_3, x_4, x_5, x_9, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_apply_2(x_12, lean_box(0), x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_4, x_5);
lean_inc(x_2);
x_10 = lean_apply_1(x_2, x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_3);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_11);
x_13 = lean_box_usize(x_5);
x_14 = lean_box_usize(x_6);
x_15 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_4);
lean_closure_set(x_15, 5, x_14);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_12, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_apply_2(x_18, lean_box(0), x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__2___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, uint8_t x_7) {
_start:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 1;
x_9 = lean_usize_add(x_1, x_8);
x_10 = l_Array_anyMUnsafe_any___at_Array_allM___spec__2___rarg(x_2, x_3, x_4, x_5, x_9, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_apply_2(x_12, lean_box(0), x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_4, x_5);
lean_inc(x_2);
x_10 = lean_apply_1(x_2, x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_3);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_11);
x_13 = lean_box_usize(x_5);
x_14 = lean_box_usize(x_6);
x_15 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Array_allM___spec__2___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_4);
lean_closure_set(x_15, 5, x_14);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_12, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_apply_2(x_18, lean_box(0), x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Array_allM___spec__2___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_allM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_nat_dec_lt(x_4, x_5);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
if (x_7 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_apply_2(x_10, lean_box(0), x_12);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_13, x_8);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_3);
x_16 = lean_nat_dec_le(x_5, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_4, x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_apply_2(x_19, lean_box(0), x_21);
x_23 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_22, x_8);
return x_23;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_usize_of_nat(x_4);
x_25 = lean_usize_of_nat(x_15);
lean_dec(x_15);
lean_inc(x_6);
x_26 = l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg(x_1, x_2, x_6, x_3, x_24, x_25);
x_27 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_26, x_8);
return x_27;
}
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_15);
x_28 = lean_usize_of_nat(x_4);
x_29 = lean_usize_of_nat(x_5);
lean_inc(x_6);
x_30 = l_Array_anyMUnsafe_any___at_Array_allM___spec__2___rarg(x_1, x_2, x_6, x_3, x_28, x_29);
x_31 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_30, x_8);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_allM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_allM___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___lambda__1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___lambda__2(x_8, x_2, x_3, x_4, x_5, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = l_Array_anyMUnsafe_any___at_Array_allM___spec__1___rarg(x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l_Array_anyMUnsafe_any___at_Array_allM___spec__2___rarg___lambda__1(x_8, x_2, x_3, x_4, x_5, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_allM___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = l_Array_anyMUnsafe_any___at_Array_allM___spec__2___rarg(x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_allM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_allM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Array_findSomeRevM_x3f_find___rarg(x_1, x_2, x_3, x_4, lean_box(0));
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_array_fget(x_3, x_9);
lean_inc(x_2);
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_9);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_16, lean_box(0), x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___rarg___boxed), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_findSomeRevM_x3f_find___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_findSomeRevM_x3f_find___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = l_Array_findSomeRevM_x3f_find___rarg(x_1, x_2, x_3, x_4, lean_box(0));
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg(x_1, x_2, x_3, x_4, lean_box(0));
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_array_fget(x_3, x_9);
lean_inc(x_2);
lean_inc(x_11);
x_12 = lean_apply_1(x_2, x_11);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_11);
lean_inc(x_10);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_13);
x_15 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_9);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_18, lean_box(0), x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg(x_1, x_2, x_3, x_4, lean_box(0));
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_findRevM_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findRevM_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg___lambda__1(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_findSomeRevM_x3f_find___at_Array_findRevM_x3f___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_le(x_5, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_usize_of_nat(x_4);
x_18 = lean_usize_of_nat(x_5);
x_19 = lean_box(0);
x_20 = l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1___rarg(x_1, x_2, x_3, x_17, x_18, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_forM___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_forM___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_instForM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_4, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1___rarg(x_1, x_3, x_2, x_16, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_instForM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_instForM___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_instForM___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 1;
x_10 = lean_usize_sub(x_4, x_9);
x_11 = lean_array_uget(x_3, x_10);
lean_inc(x_2);
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_box_usize(x_10);
x_14 = lean_box_usize(x_5);
x_15 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__1___rarg___boxed), 6, 5);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_13);
lean_closure_set(x_15, 4, x_14);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_12, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = 1;
x_10 = lean_usize_sub(x_4, x_9);
x_11 = lean_array_uget(x_3, x_10);
lean_inc(x_2);
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_box_usize(x_10);
x_14 = lean_box_usize(x_5);
x_15 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__2___rarg___boxed), 6, 5);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_13);
lean_closure_set(x_15, 4, x_14);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_12, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__2___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_le(x_4, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = lean_usize_of_nat(x_5);
x_15 = lean_box(0);
x_16 = l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__1___rarg(x_1, x_2, x_3, x_13, x_14, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_6);
x_17 = lean_nat_dec_lt(x_5, x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
return x_21;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_usize_of_nat(x_4);
x_23 = lean_usize_of_nat(x_5);
x_24 = lean_box(0);
x_25 = l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__2___rarg(x_1, x_2, x_3, x_22, x_23, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forRevM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_forRevM___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldrMUnsafe_fold___at_Array_forRevM___spec__2___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forRevM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forRevM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_foldl___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_foldl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_foldl___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_le(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Array_foldl___spec__1___rarg(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldl___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_foldl___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Array_foldl___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldl___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_9, x_5);
x_3 = x_8;
x_5 = x_10;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__2___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_9, x_5);
x_3 = x_8;
x_5 = x_10;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__2___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_le(x_4, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__1___rarg(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_6);
x_12 = lean_nat_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_4);
x_14 = lean_usize_of_nat(x_5);
x_15 = l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__2___rarg(x_1, x_3, x_13, x_14, x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldr___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Array_foldr___spec__2___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldr___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldr___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_sum___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_9, x_5);
x_3 = x_8;
x_5 = x_10;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_sum___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_sum___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_sum___spec__2___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_9, x_5);
x_3 = x_8;
x_5 = x_10;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_sum___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_sum___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_sum___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_le(x_4, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = 0;
x_10 = l_Array_foldrMUnsafe_fold___at_Array_sum___spec__1___rarg(x_1, x_3, x_8, x_9, x_2);
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_4);
if (x_12 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = 0;
x_15 = l_Array_foldrMUnsafe_fold___at_Array_sum___spec__2___rarg(x_1, x_3, x_13, x_14, x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_sum(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_sum___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_sum___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Array_sum___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_sum___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Array_sum___spec__2___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_sum___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_sum___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_countP___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_3 = x_8;
x_5 = x_14;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_countP___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_countP___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_countP___spec__2___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_3 = x_8;
x_5 = x_14;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_countP___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_countP___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_countP___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_le(x_3, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(0u);
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = 0;
x_10 = l_Array_foldrMUnsafe_fold___at_Array_countP___spec__1___rarg(x_1, x_2, x_8, x_9, x_5);
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_unsigned_to_nat(0u);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_15 = 0;
x_16 = l_Array_foldrMUnsafe_fold___at_Array_countP___spec__2___rarg(x_1, x_2, x_14, x_15, x_11);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_countP(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_countP___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_countP___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Array_countP___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_countP___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at_Array_countP___spec__2___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_countP___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_countP___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_count___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = 1;
x_9 = lean_usize_sub(x_4, x_8);
x_10 = lean_array_uget(x_3, x_9);
lean_inc(x_1);
lean_inc(x_2);
x_11 = lean_apply_2(x_1, x_10, x_2);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_4 = x_9;
x_6 = x_15;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_count___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_count___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_count___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = 1;
x_9 = lean_usize_sub(x_4, x_8);
x_10 = lean_array_uget(x_3, x_9);
lean_inc(x_1);
lean_inc(x_2);
x_11 = lean_apply_2(x_1, x_10, x_2);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_4 = x_9;
x_6 = x_15;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_count___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_count___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_count___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_le(x_4, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_4);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(0u);
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = 0;
x_11 = l_Array_foldrMUnsafe_fold___at_Array_count___spec__1___rarg(x_1, x_2, x_3, x_9, x_10, x_6);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_4);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(0u);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_16 = 0;
x_17 = l_Array_foldrMUnsafe_fold___at_Array_count___spec__2___rarg(x_1, x_2, x_3, x_15, x_16, x_12);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_count(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_count___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_count___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldrMUnsafe_fold___at_Array_count___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_count___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldrMUnsafe_fold___at_Array_count___spec__2___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_count___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_count___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_map___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_map___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Array_map___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_map___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at_Array_map___spec__1___rarg(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_map___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_map___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Array_map___spec__1___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__2___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_4, x_3, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
lean_inc(x_1);
x_10 = lean_array_uset(x_7, x_3, x_1);
x_3 = x_9;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__2___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_array_size(x_4);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__1___rarg(x_3, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_instFunctor___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_array_size(x_4);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__2___rarg(x_3, x_5, x_6, x_4);
return x_7;
}
}
static lean_object* _init_l_Array_instFunctor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_instFunctor___lambda__1), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Array_instFunctor___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_instFunctor___lambda__2), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Array_instFunctor___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_instFunctor___closed__1;
x_2 = l_Array_instFunctor___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_instFunctor() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instFunctor___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__1___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Array_instFunctor___spec__2___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapFinIdx___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_array_fget(x_3, x_5);
lean_inc(x_2);
lean_inc(x_5);
x_13 = lean_apply_3(x_2, x_5, x_12, lean_box(0));
x_14 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_15 = lean_array_push(x_7, x_13);
x_4 = x_11;
x_5 = x_14;
x_6 = lean_box(0);
x_7 = x_15;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapFinIdx___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at_Array_mapFinIdx___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_mapFinIdxM_map___at_Array_mapFinIdx___spec__1___rarg(x_1, x_2, x_1, x_3, x_5, lean_box(0), x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mapFinIdx___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapFinIdx___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapFinIdxM_map___at_Array_mapFinIdx___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdx___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapFinIdx___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdx___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_array_fget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_5);
x_13 = lean_apply_2(x_1, x_5, x_12);
x_14 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_15 = lean_array_push(x_7, x_13);
x_4 = x_11;
x_5 = x_14;
x_6 = lean_box(0);
x_7 = x_15;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdx___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at_Array_mapIdx___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_mapFinIdxM_map___at_Array_mapIdx___spec__1___rarg(x_1, x_2, x_2, x_3, x_5, lean_box(0), x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mapIdx___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_mapIdx___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapFinIdxM_map___at_Array_mapIdx___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdx___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapIdx___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_zipIdx___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_array_fget(x_3, x_5);
x_13 = lean_nat_add(x_2, x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_16 = lean_array_push(x_7, x_14);
x_4 = x_11;
x_5 = x_15;
x_6 = lean_box(0);
x_7 = x_16;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_zipIdx___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at_Array_zipIdx___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_mapFinIdxM_map___at_Array_zipIdx___spec__1___rarg(x_1, x_2, x_1, x_3, x_5, lean_box(0), x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_zipIdx___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Array_zipIdx___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapFinIdxM_map___at_Array_zipIdx___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_zipIdx___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_zipIdx___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithIndex___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_zipIdx___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithIndex(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_zipWithIndex___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithIndex___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_zipWithIndex___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_find_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec(x_1);
lean_inc(x_8);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_uget(x_5, x_7);
lean_inc(x_1);
lean_inc(x_10);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_7, x_13);
{
size_t _tmp_6 = x_14;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_10);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_find_x3f___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_find_x3f___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Array_find_x3f___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_find_x3f___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_find_x3f___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_find_x3f___rarg___closed__1;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_box(0);
x_4 = lean_array_size(x_2);
x_5 = 0;
x_6 = l_Array_findSomeM_x3f___rarg___closed__1;
x_7 = l_Array_forIn_x27Unsafe_loop___at_Array_find_x3f___spec__1___rarg(x_1, x_2, x_3, x_6, x_2, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Array_find_x3f___rarg___closed__2;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_find_x3f___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_find_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at_Array_find_x3f___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_find_x3f___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_find_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_find_x3f___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec(x_1);
lean_inc(x_8);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_5, x_7);
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_7, x_12);
{
size_t _tmp_6 = x_13;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x3f___spec__1___rarg___boxed), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_box(0);
x_4 = lean_array_size(x_2);
x_5 = 0;
x_6 = l_Array_findSomeM_x3f___rarg___closed__1;
x_7 = l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x3f___spec__1___rarg(x_1, x_2, x_3, x_6, x_2, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findSome_x3f___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x3f___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findSome_x3f___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x21___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_7, x_6);
if (x_9 == 0)
{
lean_dec(x_1);
lean_inc(x_8);
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_5, x_7);
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_7, x_12);
{
size_t _tmp_6 = x_13;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x21___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x21___spec__1___rarg___boxed), 8, 0);
return x_3;
}
}
static lean_object* _init_l_Array_findSome_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Array.findSome!", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Array_findSome_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to find element", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Array_findSome_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_swapAt_x21___rarg___closed__3;
x_2 = l_Array_findSome_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(708u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Array_findSome_x21___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_box(0);
x_5 = lean_array_size(x_3);
x_6 = 0;
x_7 = l_Array_findSomeM_x3f___rarg___closed__1;
x_8 = l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x21___spec__1___rarg(x_2, x_3, x_4, x_7, x_3, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Array_findSome_x21___rarg___closed__3;
x_11 = l_panic___rarg(x_1, x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Array_findSome_x21___rarg___closed__3;
x_14 = l_panic___rarg(x_1, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findSome_x21___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x21___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forIn_x27Unsafe_loop___at_Array_findSome_x21___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_findSome_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findSome_x21___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findSomeRev_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_2, x_8);
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findSomeRev_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Array_findSomeRev_x3f___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = l_Array_findSomeRevM_x3f_find___at_Array_findSomeRev_x3f___spec__1___rarg(x_1, x_2, x_3, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findSomeRev_x3f___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findSomeRev_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Array_findSomeRev_x3f___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRev_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findSomeRev_x3f___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRev_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_2, x_8);
lean_inc(x_1);
lean_inc(x_9);
x_10 = lean_apply_1(x_1, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_dec(x_9);
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_box(0);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRev_x3f___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findSomeRevM_x3f_find___at_Array_findRev_x3f___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = l_Array_findSomeRevM_x3f_find___at_Array_findRev_x3f___spec__1___rarg(x_1, x_2, x_3, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findRev_x3f___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Array_findRev_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Array_findRev_x3f___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_findRev_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findRev_x3f___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findIdx_x3f_loop___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdx_x3f_loop___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_findIdx_x3f_loop___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findIdx_x3f___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findIdx_x3f___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findFinIdx_x3f_loop___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findFinIdx_x3f_loop___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_findFinIdx_x3f_loop___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findFinIdx_x3f___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_findFinIdx_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findFinIdx_x3f___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_findIdx_x3f_loop___rarg(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_array_get_size(x_2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findIdx___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findIdx___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_2, x_4);
lean_inc(x_1);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_8, x_3);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_idxOfAux___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_idxOfAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_indexOfAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_idxOfAux___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_indexOfAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_indexOfAux___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_indexOfAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_indexOfAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_idxOfAux___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_finIdxOf_x3f___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_finIdxOf_x3f___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_indexOf_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_idxOfAux___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_indexOf_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_indexOf_x3f___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_indexOf_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_indexOf_x3f___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Array_idxOf___rarg___lambda__1), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_findIdx_x3f_loop___rarg(x_4, x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_array_get_size(x_3);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_idxOf___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_idxOf___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_idxOfAux___rarg(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_idxOf_x3f___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_idxOf_x3f___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_getIdx_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Array_idxOf___rarg___lambda__1), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_findIdx_x3f_loop___rarg(x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_getIdx_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_getIdx_x3f___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_getIdx_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_getIdx_x3f___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Array_any___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_unbox(x_7);
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
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_any___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Array_any___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Array_any___spec__2___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_unbox(x_7);
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
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_any___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Array_any___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_any___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_le(x_4, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_2);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = lean_usize_of_nat(x_3);
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at_Array_any___spec__1___rarg(x_2, x_1, x_11, x_12);
return x_13;
}
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
lean_dec(x_7);
x_14 = lean_usize_of_nat(x_3);
x_15 = lean_usize_of_nat(x_4);
x_16 = l_Array_anyMUnsafe_any___at_Array_any___spec__2___rarg(x_2, x_1, x_14, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_any(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_any___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_any___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Array_any___spec__1___rarg(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_any___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Array_any___spec__2___rarg(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_any___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_any___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Array_all___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_1);
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
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_all___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Array_all___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Array_all___spec__2___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_6);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_1);
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
lean_dec(x_1);
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_all___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Array_all___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_all___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = 1;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_le(x_4, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_2);
x_10 = 1;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = lean_usize_of_nat(x_3);
x_12 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_13 = l_Array_anyMUnsafe_any___at_Array_all___spec__1___rarg(x_2, x_1, x_11, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
lean_dec(x_7);
x_16 = lean_usize_of_nat(x_3);
x_17 = lean_usize_of_nat(x_4);
x_18 = l_Array_anyMUnsafe_any___at_Array_all___spec__2___rarg(x_2, x_1, x_16, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_all(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_all___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_all___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Array_all___spec__1___rarg(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_all___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Array_all___spec__2___rarg(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_all___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_all___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Array_contains___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_uget(x_3, x_4);
lean_inc(x_1);
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_2, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_contains___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Array_contains___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = 0;
return x_7;
}
else
{
size_t x_8; size_t x_9; uint8_t x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_anyMUnsafe_any___at_Array_contains___spec__1___rarg(x_1, x_3, x_2, x_8, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_contains___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Array_contains___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Array_contains___spec__1___rarg(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_contains___rarg(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_elem___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_contains___rarg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_elem(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_elem___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_elem___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_elem___rarg(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__2___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_array_to_list_impl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box(0);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_le(x_4, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = 0;
x_10 = l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__1___rarg(x_2, x_8, x_9, x_3);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_4);
if (x_12 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = 0;
x_15 = l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__2___rarg(x_2, x_13, x_14, x_3);
lean_dec(x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__1___rarg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at_Array_toListImpl___spec__2___rarg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__2___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_le(x_3, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_8 = 0;
x_9 = l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__1___rarg(x_1, x_7, x_8, x_2);
return x_9;
}
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_3);
if (x_11 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_13 = 0;
x_14 = l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__2___rarg(x_1, x_12, x_13, x_2);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_toListAppend___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__1___rarg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at_Array_toListAppend___spec__2___rarg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_toListAppend___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_toListAppend___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_append___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_array_push(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_append___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_append___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_append___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_append___spec__1___rarg(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_append(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_append___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_append___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Array_append___spec__1___rarg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_append___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_append___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Array_instAppend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_append___rarg___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_instAppend(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_instAppend___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Array_appendList___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_push(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Array_appendList___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___at_Array_appendList___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_appendList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_Array_appendList___spec__1___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_appendList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_appendList___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Array_instHAppendList___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_appendList___rarg), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_instHAppendList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_instHAppendList___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Array_append___rarg(x_2, x_3);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___lambda__2(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
x_10 = lean_apply_1(x_2, x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_6);
lean_inc(x_8);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_11);
x_13 = lean_box_usize(x_4);
x_14 = lean_box_usize(x_5);
x_15 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_14);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_12, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_4, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_18 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_19 = l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg(x_1, x_2, x_3, x_16, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMapM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_flatMapM___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___lambda__2(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
x_10 = lean_apply_1(x_2, x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_flatMapM___spec__1___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_6);
lean_inc(x_8);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_11);
x_13 = lean_box_usize(x_4);
x_14 = lean_box_usize(x_5);
x_15 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_14);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_12, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_concatMapM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_4, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_18 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_19 = l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1___rarg(x_1, x_2, x_3, x_16, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_concatMapM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_concatMapM___rarg), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_concatMapM___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMap___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_1(x_1, x_7);
x_9 = l_Array_append___rarg(x_5, x_8);
lean_dec(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_9;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_flatMap___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_12 = l_Array_foldlMUnsafe_fold___at_Array_flatMap___spec__1___rarg(x_1, x_2, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_flatMap___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatMap___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Array_flatMap___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_flatMap___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_flatMap___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMap___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_1(x_1, x_7);
x_9 = l_Array_append___rarg(x_5, x_8);
lean_dec(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
x_5 = x_9;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_concatMap___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_concatMap___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_12 = l_Array_foldlMUnsafe_fold___at_Array_concatMap___spec__1___rarg(x_1, x_2, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_concatMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_concatMap___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_concatMap___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Array_concatMap___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_concatMap___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_concatMap___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatten___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Array_append___rarg(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatten___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_flatten___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_flatten___rarg(lean_object* x_1) {
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
x_5 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
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
x_7 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_11 = l_Array_foldlMUnsafe_fold___at_Array_flatten___spec__1___rarg(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_flatten(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_flatten___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_flatten___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Array_flatten___spec__1___rarg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_flatten___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_flatten___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_array_fswap(x_1, x_2, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_2, x_6);
lean_dec(x_2);
x_8 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_1 = x_5;
x_2 = x_7;
x_3 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_reverse_loop___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_reverse___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_le(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_reverse_loop___rarg(x_1, x_6, x_5);
return x_7;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_reverse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_reverse___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filter___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_7);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
if (x_9 == 0)
{
lean_dec(x_7);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_7);
x_3 = x_11;
x_5 = x_13;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filter___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_filter___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
static lean_object* _init_l_Array_filter___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Array_filter___rarg___closed__1;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_le(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Array_filter___rarg___closed__1;
return x_9;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_usize_of_nat(x_3);
x_11 = lean_usize_of_nat(x_4);
x_12 = l_Array_filter___rarg___closed__1;
x_13 = l_Array_foldlMUnsafe_fold___at_Array_filter___spec__1___rarg(x_1, x_2, x_10, x_11, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_filter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filter___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Array_filter___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_filter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_array_push(x_2, x_3);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg___lambda__2(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_9);
x_10 = lean_apply_1(x_2, x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_6);
lean_closure_set(x_11, 2, x_9);
lean_inc(x_8);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_11);
x_13 = lean_box_usize(x_4);
x_14 = lean_box_usize(x_5);
x_15 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_14);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_12, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Array_filter___rarg___closed__1;
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_le(x_5, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Array_filter___rarg___closed__1;
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_usize_of_nat(x_4);
x_18 = lean_usize_of_nat(x_5);
x_19 = l_Array_filter___rarg___closed__1;
x_20 = l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg(x_1, x_2, x_3, x_17, x_18, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_filterM___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg___lambda__2(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Array_filterM___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_filterM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_filterM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_array_push(x_2, x_3);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = 1;
x_11 = lean_usize_sub(x_5, x_10);
x_12 = lean_array_uget(x_4, x_11);
lean_inc(x_2);
lean_inc(x_12);
x_13 = lean_apply_1(x_2, x_12);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_7);
lean_closure_set(x_14, 2, x_12);
lean_inc(x_9);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_13, x_14);
x_16 = lean_box_usize(x_11);
x_17 = lean_box_usize(x_6);
x_18 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1___rarg___boxed), 7, 6);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_16);
lean_closure_set(x_18, 5, x_17);
x_19 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_15, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_2(x_21, lean_box(0), x_7);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = 1;
x_11 = lean_usize_sub(x_5, x_10);
x_12 = lean_array_uget(x_4, x_11);
lean_inc(x_2);
lean_inc(x_12);
x_13 = lean_apply_1(x_2, x_12);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_7);
lean_closure_set(x_14, 2, x_12);
lean_inc(x_9);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_13, x_14);
x_16 = lean_box_usize(x_11);
x_17 = lean_box_usize(x_6);
x_18 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__2___rarg___boxed), 7, 6);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_16);
lean_closure_set(x_18, 5, x_17);
x_19 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_15, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_apply_2(x_21, lean_box(0), x_7);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__2___rarg___boxed), 7, 0);
return x_3;
}
}
static lean_object* _init_l_Array_filterRevM___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_reverse___rarg), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_le(x_4, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_5, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_Array_filter___rarg___closed__1;
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
x_15 = l_Array_filterRevM___rarg___closed__1;
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_18 = lean_usize_of_nat(x_5);
x_19 = l_Array_filter___rarg___closed__1;
x_20 = l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1___rarg(x_1, x_2, x_6, x_3, x_17, x_18, x_19);
x_21 = l_Array_filterRevM___rarg___closed__1;
x_22 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_21, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
x_23 = lean_nat_dec_lt(x_5, x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_dec(x_6);
x_25 = l_Array_filter___rarg___closed__1;
x_26 = lean_apply_2(x_24, lean_box(0), x_25);
x_27 = l_Array_filterRevM___rarg___closed__1;
x_28 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_27, x_26);
return x_28;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_usize_of_nat(x_4);
x_30 = lean_usize_of_nat(x_5);
x_31 = l_Array_filter___rarg___closed__1;
x_32 = l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__2___rarg(x_1, x_2, x_6, x_3, x_29, x_30, x_31);
x_33 = l_Array_filterRevM___rarg___closed__1;
x_34 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_33, x_32);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_filterRevM___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__1___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldrMUnsafe_fold___at_Array_filterRevM___spec__2___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_filterRevM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_filterRevM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_array_push(x_2, x_7);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_alloc_closure((void*)(l_Array_filterMapM___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Array_filterMapM___rarg___lambda__2), 4, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Array_filter___rarg___closed__1;
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_le(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Array_filter___rarg___closed__1;
x_17 = lean_apply_2(x_15, lean_box(0), x_16);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_usize_of_nat(x_4);
x_19 = lean_usize_of_nat(x_5);
x_20 = l_Array_filter___rarg___closed__1;
x_21 = l_Array_foldlMUnsafe_fold___rarg(x_1, x_6, x_3, x_18, x_19, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_filterMapM___rarg___boxed), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_filterMapM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterMap___spec__2___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_1(x_1, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (lean_obj_tag(x_8) == 0)
{
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_array_push(x_5, x_12);
x_3 = x_10;
x_5 = x_13;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterMap___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_filterMap___spec__2___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Array_filterMap___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Array_filter___rarg___closed__1;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_le(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Array_filter___rarg___closed__1;
return x_9;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_usize_of_nat(x_3);
x_11 = lean_usize_of_nat(x_4);
x_12 = l_Array_filter___rarg___closed__1;
x_13 = l_Array_foldlMUnsafe_fold___at_Array_filterMap___spec__2___rarg(x_1, x_2, x_10, x_11, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Array_filterMap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_filterMapM___at_Array_filterMap___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterMapM___at_Array_filterMap___spec__1___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_filterMap___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_filterMap___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Array_filterMap___spec__2___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Array_filterMap___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterMapM___at_Array_filterMap___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_filterMap___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterMap___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_1, x_4);
x_8 = lean_alloc_closure((void*)(l_Array_getMax_x3f___rarg___lambda__1), 3, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_lt(x_9, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_3, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_7);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = 1;
x_15 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_16 = l_Id_instMonad;
x_17 = l_Array_foldlMUnsafe_fold___rarg(x_16, x_8, x_1, x_14, x_15, x_7);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getMax_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_getMax_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_partition___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
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
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_uget(x_4, x_6);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_1);
lean_inc(x_9);
x_13 = lean_apply_1(x_1, x_9);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_array_push(x_12, x_9);
lean_ctor_set(x_7, 1, x_15);
x_16 = 1;
x_17 = lean_usize_add(x_6, x_16);
x_6 = x_17;
goto _start;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_array_push(x_11, x_9);
lean_ctor_set(x_7, 0, x_19);
x_20 = 1;
x_21 = lean_usize_add(x_6, x_20);
x_6 = x_21;
goto _start;
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
lean_inc(x_1);
lean_inc(x_9);
x_25 = lean_apply_1(x_1, x_9);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_27 = lean_array_push(x_24, x_9);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = 1;
x_30 = lean_usize_add(x_6, x_29);
x_6 = x_30;
x_7 = x_28;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_32 = lean_array_push(x_23, x_9);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_24);
x_34 = 1;
x_35 = lean_usize_add(x_6, x_34);
x_6 = x_35;
x_7 = x_33;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_partition___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Array_partition___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Array_partition___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_filter___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_partition___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_box(0);
x_4 = lean_array_size(x_2);
x_5 = 0;
x_6 = l_Array_partition___rarg___closed__1;
x_7 = l_Array_forIn_x27Unsafe_loop___at_Array_partition___spec__1___rarg(x_1, x_2, x_3, x_2, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_partition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_partition___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Array_partition___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forIn_x27Unsafe_loop___at_Array_partition___spec__1___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_partition___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_partition___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_popWhile___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget(x_2, x_7);
lean_dec(x_7);
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_11; 
x_11 = lean_array_pop(x_2);
x_2 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_popWhile(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_popWhile___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_7);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_12 = lean_array_push(x_4, x_7);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_takeWhile_go___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_takeWhile_go___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_filter___rarg___closed__1;
x_5 = l_Array_takeWhile_go___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_takeWhile___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_takeWhile___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_takeWhile___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_11923_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__17;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = lean_array_pop(x_1);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_array_fswap(x_1, x_5, x_2);
lean_dec(x_2);
x_1 = x_9;
x_2 = x_5;
x_3 = lean_box(0);
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_eraseIdx___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; 
x_5 = l_Array_eraseIdx___rarg(x_1, x_2, lean_box(0));
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdxIfInBounds(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_eraseIdxIfInBounds___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Array_eraseIdx_x21___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Array_eraseIdx_x21___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panic___at_Array_eraseIdx_x21___spec__1___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Array_eraseIdx_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Array.eraseIdx!", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Array_eraseIdx_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid index", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Array_eraseIdx_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_swapAt_x21___rarg___closed__3;
x_2 = l_Array_eraseIdx_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(978u);
x_4 = lean_unsigned_to_nat(47u);
x_5 = l_Array_eraseIdx_x21___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = l_Array_eraseIdx_x21___rarg___closed__3;
x_6 = l_panic___at_Array_eraseIdx_x21___spec__1___rarg(x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_Array_eraseIdx___rarg(x_1, x_2, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseIdx_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_eraseIdx_x21___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_idxOfAux___rarg(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Array_eraseIdx___rarg(x_2, x_6, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_erase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_erase___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_eraseP___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_findFinIdx_x3f_loop___rarg(x_2, x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Array_eraseIdx___rarg(x_1, x_5, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseP(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_eraseP___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l___auto____x40_Init_Data_Array_Basic___hyg_12376_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__17;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_1, x_3);
if (x_4 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_3, x_5);
x_7 = lean_array_fswap(x_2, x_6, x_3);
lean_dec(x_3);
x_2 = x_7;
x_3 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_insertIdx_loop___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_insertIdx_loop___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_array_push(x_1, x_3);
x_7 = l_Array_insertIdx_loop___rarg(x_2, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_insertIdx___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_insertIdx___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_insertAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_array_push(x_1, x_3);
x_7 = l_Array_insertIdx_loop___rarg(x_2, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_insertAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_insertAt___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_insertAt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_insertAt___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at_Array_insertIdx_x21___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Array_insertIdx_x21___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panic___at_Array_insertIdx_x21___spec__1___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Array_insertIdx_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Array.insertIdx!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Array_insertIdx_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_swapAt_x21___rarg___closed__3;
x_2 = l_Array_insertIdx_x21___rarg___closed__1;
x_3 = lean_unsigned_to_nat(1023u);
x_4 = lean_unsigned_to_nat(7u);
x_5 = l_Array_eraseIdx_x21___rarg___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_le(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = l_Array_insertIdx_x21___rarg___closed__2;
x_7 = l_panic___at_Array_insertIdx_x21___spec__1___rarg(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_push(x_1, x_3);
x_9 = l_Array_insertIdx_loop___rarg(x_2, x_8, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_insertIdx_x21___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdx_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_insertIdx_x21___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_insertAt_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_insertIdx_x21___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_insertAt_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_insertAt_x21___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_insertAt_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_insertAt_x21___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_le(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_push(x_1, x_3);
x_7 = l_Array_insertIdx_loop___rarg(x_2, x_6, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_insertIdxIfInBounds___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_insertIdxIfInBounds___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_insertIdxIfInBounds___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOfAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_1);
x_8 = 1;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
lean_inc(x_1);
x_11 = lean_apply_2(x_1, x_9, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_isPrefixOfAux___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOfAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isPrefixOfAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_isPrefixOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_le(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_isPrefixOfAux___rarg(x_1, x_2, x_3, lean_box(0), x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_isPrefixOf___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_isPrefixOf___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isPrefixOf___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_1, x_4);
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_fget(x_2, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
lean_inc(x_3);
x_14 = lean_apply_2(x_3, x_8, x_11);
x_15 = lean_array_push(x_5, x_14);
x_4 = x_13;
x_5 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_zipWithAux___rarg___boxed), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_zipWithAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_filter___rarg___closed__1;
x_6 = l_Array_zipWithAux___rarg(x_2, x_3, x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_zipWith___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_zipWith___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_zipWith___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAux___at_Array_zip___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_array_push(x_4, x_13);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAux___at_Array_zip___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_zipWithAux___at_Array_zip___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_zip___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_filter___rarg___closed__1;
x_5 = l_Array_zipWithAux___at_Array_zip___spec__1___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_zip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_zip___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAux___at_Array_zip___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_zipWithAux___at_Array_zip___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_zip___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_zip___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_array_get_size(x_2);
x_36 = lean_array_get_size(x_3);
x_37 = lean_nat_dec_le(x_35, x_36);
if (x_37 == 0)
{
lean_dec(x_36);
x_6 = x_35;
goto block_34;
}
else
{
lean_dec(x_35);
x_6 = x_36;
goto block_34;
}
block_34:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
if (x_9 == 0)
{
lean_object* x_14; 
x_14 = lean_box(0);
if (x_11 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_inc(x_1);
x_15 = lean_apply_2(x_1, x_14, x_14);
x_16 = lean_array_push(x_5, x_15);
x_4 = x_13;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_fget(x_3, x_4);
lean_dec(x_4);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_1);
x_20 = lean_apply_2(x_1, x_14, x_19);
x_21 = lean_array_push(x_5, x_20);
x_4 = x_13;
x_5 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_array_fget(x_2, x_4);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
if (x_11 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
x_25 = lean_box(0);
lean_inc(x_1);
x_26 = lean_apply_2(x_1, x_24, x_25);
x_27 = lean_array_push(x_5, x_26);
x_4 = x_13;
x_5 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_array_fget(x_3, x_4);
lean_dec(x_4);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_inc(x_1);
x_31 = lean_apply_2(x_1, x_24, x_30);
x_32 = lean_array_push(x_5, x_31);
x_4 = x_13;
x_5 = x_32;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_zipWithAll_go___rarg___boxed), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_zipWithAll_go___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_filter___rarg___closed__1;
x_6 = l_Array_zipWithAll_go___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_zipWithAll___rarg___boxed), 3, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithAll___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_zipWithAll___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_unzip___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_array_push(x_9, x_12);
x_15 = lean_array_push(x_10, x_13);
lean_ctor_set(x_6, 1, x_15);
lean_ctor_set(x_6, 0, x_14);
x_2 = x_8;
x_4 = x_6;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_array_push(x_9, x_17);
x_20 = lean_array_push(x_10, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_2 = x_8;
x_4 = x_21;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_unzip___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_unzip___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
static lean_object* _init_l_Array_unzip___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_filter___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___rarg(lean_object* x_1) {
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
x_5 = l_Array_unzip___rarg___closed__1;
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
x_7 = l_Array_unzip___rarg___closed__1;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Array_unzip___rarg___closed__1;
x_11 = l_Array_foldlMUnsafe_fold___at_Array_unzip___spec__1___rarg(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_unzip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_unzip___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_unzip___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Array_unzip___spec__1___rarg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_unzip___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_unzip___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_split___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_1);
lean_inc(x_7);
x_13 = lean_apply_1(x_1, x_7);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_push(x_12, x_7);
lean_ctor_set(x_5, 1, x_15);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_array_push(x_11, x_7);
lean_ctor_set(x_5, 0, x_17);
x_3 = x_9;
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_7);
x_21 = lean_apply_1(x_1, x_7);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_array_push(x_20, x_7);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_3 = x_9;
x_5 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_array_push(x_19, x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
x_3 = x_9;
x_5 = x_27;
goto _start;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_split___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_split___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_split___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = l_Array_unzip___rarg___closed__1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Array_unzip___rarg___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_unzip___rarg___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Array_split___spec__1___rarg(x_2, x_1, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_split(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_split___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_split___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Array_split___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_split___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_split___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_replace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_idxOfAux___rarg(x_1, x_2, x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_fset(x_2, x_7, x_4);
lean_dec(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_replace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_replace___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_instLT(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_instLT___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_instLT(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_instLE(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_instLE___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_instLE(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_sub(x_1, x_4);
lean_dec(x_4);
x_6 = lean_mk_array(x_5, x_2);
x_7 = l_Array_append___rarg(x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_leftpad___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_leftpad___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_leftpad___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_sub(x_1, x_4);
lean_dec(x_4);
x_6 = lean_mk_array(x_5, x_2);
x_7 = l_Array_append___rarg(x_3, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_rightpad___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_rightpad___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_rightpad___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_reduceOption___spec__2___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_array_push(x_4, x_10);
x_2 = x_8;
x_4 = x_11;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_reduceOption___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_reduceOption___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Array_reduceOption___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Array_filter___rarg___closed__1;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Array_filter___rarg___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_3);
x_11 = l_Array_filter___rarg___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Array_reduceOption___spec__2___rarg(x_1, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Array_reduceOption___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_filterMapM___at_Array_reduceOption___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_filterMapM___at_Array_reduceOption___spec__1___rarg(x_1, x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_reduceOption___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_reduceOption___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Array_reduceOption___spec__2___rarg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Array_reduceOption___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at_Array_reduceOption___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_reduceOption___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_reduceOption___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_eraseReps___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_7);
x_13 = lean_apply_2(x_1, x_7, x_11);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_push(x_12, x_11);
lean_ctor_set(x_5, 1, x_15);
lean_ctor_set(x_5, 0, x_7);
x_3 = x_9;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_9;
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_18);
lean_inc(x_7);
x_20 = lean_apply_2(x_1, x_7, x_18);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_array_push(x_19, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_22);
x_3 = x_9;
x_5 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_7);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
x_3 = x_9;
x_5 = x_25;
goto _start;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_eraseReps___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_eraseReps___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = l_Array_filter___rarg___closed__1;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l_Array_filter___rarg___closed__1;
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_nat_dec_le(x_3, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_array_push(x_8, x_7);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_12 = 0;
x_13 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Array_eraseReps___spec__1___rarg(x_1, x_2, x_12, x_13, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_push(x_16, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_eraseReps___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_eraseReps___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Array_eraseReps___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_eraseReps___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_eraseReps___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = lean_array_fget(x_2, x_9);
lean_inc(x_1);
lean_inc(x_3);
x_11 = lean_apply_2(x_1, x_3, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
x_4 = x_9;
x_5 = lean_box(0);
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_14 = 0;
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = 1;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = 1;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_3);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___rarg(x_1, x_2, x_7, x_3, lean_box(0));
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_allDiffAux___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___rarg(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_allDiff___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_allDiff___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_allDiff___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_allDiff___rarg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_getEvenElems___spec__1___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
x_13 = 1;
x_14 = lean_box(x_13);
lean_ctor_set(x_4, 0, x_14);
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
x_2 = x_8;
x_4 = x_19;
goto _start;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_array_push(x_22, x_6);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_4, 1, x_24);
lean_ctor_set(x_4, 0, x_26);
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_array_push(x_28, x_6);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_2 = x_8;
x_4 = x_32;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_getEvenElems___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Array_getEvenElems___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Array_getEvenElems___rarg___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___rarg(lean_object* x_1) {
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
x_5 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
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
x_7 = l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Array_getEvenElems___rarg___closed__1;
x_11 = l_Array_foldlMUnsafe_fold___at_Array_getEvenElems___spec__1___rarg(x_1, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_getEvenElems___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Array_getEvenElems___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Array_getEvenElems___spec__1___rarg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_getEvenElems___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_getEvenElems___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Array_instRepr___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_2);
lean_ctor_set_tag(x_4, 5);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_3);
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_6, x_8);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
x_3 = x_10;
x_4 = x_7;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
lean_inc(x_2);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_16 = lean_apply_2(x_1, x_12, x_15);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_3 = x_17;
x_4 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Array_instRepr___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___at_Array_instRepr___spec__2___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Array_instRepr___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_apply_2(x_1, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_11 = lean_apply_2(x_1, x_9, x_10);
x_12 = l_List_foldl___at_Array_instRepr___spec__2___rarg(x_1, x_3, x_11, x_5);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Array_instRepr___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Format_joinSep___at_Array_instRepr___spec__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Array_instRepr___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_x23_x5b___x2c_x5d___closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_instRepr___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_instRepr___rarg___closed__1;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_instRepr___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_x23_x5b___x2c_x5d___closed__5;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_instRepr___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_instRepr___rarg___closed__3;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_instRepr___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_x23_x5b___x2c_x5d___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_instRepr___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_x23_x5b___x2c_x5d___closed__18;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_instRepr___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[]", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_instRepr___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_instRepr___rarg___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_7 = lean_array_to_list(x_2);
x_8 = l_Array_instRepr___rarg___closed__2;
x_9 = l_Std_Format_joinSep___at_Array_instRepr___spec__1___rarg(x_1, x_7, x_8);
x_10 = l_Array_instRepr___rarg___closed__5;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Array_instRepr___rarg___closed__6;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Array_instRepr___rarg___closed__4;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = 1;
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Array_instRepr___rarg___closed__8;
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_instRepr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_instRepr___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_instRepr___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_instRepr___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Array_instToString___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_instToString___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_to_list(x_2);
x_4 = l_List_toString___rarg(x_1, x_3);
x_5 = l_Array_instToString___rarg___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_instToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_instToString___rarg), 2, 0);
return x_2;
}
}
lean_object* initialize_Init_WFTactics(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Fin_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_UInt_BasicAux(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Repr(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_GetElem(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_ToArrayImpl(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Set(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_WFTactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_BasicAux(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Repr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GetElem(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_ToArrayImpl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Set(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_term_x23_x5b___x2c_x5d___closed__1 = _init_l_term_x23_x5b___x2c_x5d___closed__1();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__1);
l_term_x23_x5b___x2c_x5d___closed__2 = _init_l_term_x23_x5b___x2c_x5d___closed__2();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__2);
l_term_x23_x5b___x2c_x5d___closed__3 = _init_l_term_x23_x5b___x2c_x5d___closed__3();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__3);
l_term_x23_x5b___x2c_x5d___closed__4 = _init_l_term_x23_x5b___x2c_x5d___closed__4();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__4);
l_term_x23_x5b___x2c_x5d___closed__5 = _init_l_term_x23_x5b___x2c_x5d___closed__5();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__5);
l_term_x23_x5b___x2c_x5d___closed__6 = _init_l_term_x23_x5b___x2c_x5d___closed__6();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__6);
l_term_x23_x5b___x2c_x5d___closed__7 = _init_l_term_x23_x5b___x2c_x5d___closed__7();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__7);
l_term_x23_x5b___x2c_x5d___closed__8 = _init_l_term_x23_x5b___x2c_x5d___closed__8();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__8);
l_term_x23_x5b___x2c_x5d___closed__9 = _init_l_term_x23_x5b___x2c_x5d___closed__9();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__9);
l_term_x23_x5b___x2c_x5d___closed__10 = _init_l_term_x23_x5b___x2c_x5d___closed__10();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__10);
l_term_x23_x5b___x2c_x5d___closed__11 = _init_l_term_x23_x5b___x2c_x5d___closed__11();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__11);
l_term_x23_x5b___x2c_x5d___closed__12 = _init_l_term_x23_x5b___x2c_x5d___closed__12();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__12);
l_term_x23_x5b___x2c_x5d___closed__13 = _init_l_term_x23_x5b___x2c_x5d___closed__13();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__13);
l_term_x23_x5b___x2c_x5d___closed__14 = _init_l_term_x23_x5b___x2c_x5d___closed__14();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__14);
l_term_x23_x5b___x2c_x5d___closed__15 = _init_l_term_x23_x5b___x2c_x5d___closed__15();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__15);
l_term_x23_x5b___x2c_x5d___closed__16 = _init_l_term_x23_x5b___x2c_x5d___closed__16();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__16);
l_term_x23_x5b___x2c_x5d___closed__17 = _init_l_term_x23_x5b___x2c_x5d___closed__17();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__17);
l_term_x23_x5b___x2c_x5d___closed__18 = _init_l_term_x23_x5b___x2c_x5d___closed__18();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__18);
l_term_x23_x5b___x2c_x5d___closed__19 = _init_l_term_x23_x5b___x2c_x5d___closed__19();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__19);
l_term_x23_x5b___x2c_x5d___closed__20 = _init_l_term_x23_x5b___x2c_x5d___closed__20();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__20);
l_term_x23_x5b___x2c_x5d___closed__21 = _init_l_term_x23_x5b___x2c_x5d___closed__21();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d___closed__21);
l_term_x23_x5b___x2c_x5d = _init_l_term_x23_x5b___x2c_x5d();
lean_mark_persistent(l_term_x23_x5b___x2c_x5d);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__1);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__2);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__3 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__3();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__3);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__4);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__5 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__5();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__5);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__6);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__7 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__7();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__7);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__8 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__8();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__8);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__9);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__10 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__10();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__10);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__11 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__11();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__11);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__12 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__12();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__12);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__13);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__14 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__14();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__14);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__15 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__15();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__15);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__16 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__16();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__16);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__17);
l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18 = _init_l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18();
lean_mark_persistent(l___aux__Init__Data__Array__Basic______macroRules__term_x23_x5b___x2c_x5d__1___closed__18);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__1 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__1();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__1);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__2 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__2();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__2);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__3 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__3();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__3);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__4 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__4();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__4);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__5 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__5();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__5);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__6 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__6();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__6);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__7 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__7();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__7);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__8 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__8();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__8);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__9 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__9();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__9);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__10 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__10();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__10);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__11 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__11();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__11);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__12 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__12();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__12);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__13 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__13();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__13);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__14 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__14();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__14);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__15 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__15();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__15);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__16 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__16();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__16);
l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__17 = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__17();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739____closed__17);
l___auto____x40_Init_Data_Array_Basic___hyg_1739_ = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1739_();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1739_);
l___auto____x40_Init_Data_Array_Basic___hyg_1747_ = _init_l___auto____x40_Init_Data_Array_Basic___hyg_1747_();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_1747_);
l_Array_instGetElemUSizeLtNatToNatSize___closed__1 = _init_l_Array_instGetElemUSizeLtNatToNatSize___closed__1();
lean_mark_persistent(l_Array_instGetElemUSizeLtNatToNatSize___closed__1);
l_Array_range___closed__1 = _init_l_Array_range___closed__1();
lean_mark_persistent(l_Array_range___closed__1);
l___auto____x40_Init_Data_Array_Basic___hyg_2765_ = _init_l___auto____x40_Init_Data_Array_Basic___hyg_2765_();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_2765_);
l___auto____x40_Init_Data_Array_Basic___hyg_2860_ = _init_l___auto____x40_Init_Data_Array_Basic___hyg_2860_();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_2860_);
l_Array_swapAt_x21___rarg___closed__1 = _init_l_Array_swapAt_x21___rarg___closed__1();
lean_mark_persistent(l_Array_swapAt_x21___rarg___closed__1);
l_Array_swapAt_x21___rarg___closed__2 = _init_l_Array_swapAt_x21___rarg___closed__2();
lean_mark_persistent(l_Array_swapAt_x21___rarg___closed__2);
l_Array_swapAt_x21___rarg___closed__3 = _init_l_Array_swapAt_x21___rarg___closed__3();
lean_mark_persistent(l_Array_swapAt_x21___rarg___closed__3);
l_Array_swapAt_x21___rarg___closed__4 = _init_l_Array_swapAt_x21___rarg___closed__4();
lean_mark_persistent(l_Array_swapAt_x21___rarg___closed__4);
l_Array_findSomeM_x3f___rarg___closed__1 = _init_l_Array_findSomeM_x3f___rarg___closed__1();
lean_mark_persistent(l_Array_findSomeM_x3f___rarg___closed__1);
l_Array_findIdxM_x3f___rarg___closed__1 = _init_l_Array_findIdxM_x3f___rarg___closed__1();
lean_mark_persistent(l_Array_findIdxM_x3f___rarg___closed__1);
l_Array_instFunctor___closed__1 = _init_l_Array_instFunctor___closed__1();
lean_mark_persistent(l_Array_instFunctor___closed__1);
l_Array_instFunctor___closed__2 = _init_l_Array_instFunctor___closed__2();
lean_mark_persistent(l_Array_instFunctor___closed__2);
l_Array_instFunctor___closed__3 = _init_l_Array_instFunctor___closed__3();
lean_mark_persistent(l_Array_instFunctor___closed__3);
l_Array_instFunctor = _init_l_Array_instFunctor();
lean_mark_persistent(l_Array_instFunctor);
l_Array_find_x3f___rarg___closed__1 = _init_l_Array_find_x3f___rarg___closed__1();
lean_mark_persistent(l_Array_find_x3f___rarg___closed__1);
l_Array_find_x3f___rarg___closed__2 = _init_l_Array_find_x3f___rarg___closed__2();
lean_mark_persistent(l_Array_find_x3f___rarg___closed__2);
l_Array_findSome_x21___rarg___closed__1 = _init_l_Array_findSome_x21___rarg___closed__1();
lean_mark_persistent(l_Array_findSome_x21___rarg___closed__1);
l_Array_findSome_x21___rarg___closed__2 = _init_l_Array_findSome_x21___rarg___closed__2();
lean_mark_persistent(l_Array_findSome_x21___rarg___closed__2);
l_Array_findSome_x21___rarg___closed__3 = _init_l_Array_findSome_x21___rarg___closed__3();
lean_mark_persistent(l_Array_findSome_x21___rarg___closed__3);
l_Array_instAppend___closed__1 = _init_l_Array_instAppend___closed__1();
lean_mark_persistent(l_Array_instAppend___closed__1);
l_Array_instHAppendList___closed__1 = _init_l_Array_instHAppendList___closed__1();
lean_mark_persistent(l_Array_instHAppendList___closed__1);
l_Array_filter___rarg___closed__1 = _init_l_Array_filter___rarg___closed__1();
lean_mark_persistent(l_Array_filter___rarg___closed__1);
l_Array_filterRevM___rarg___closed__1 = _init_l_Array_filterRevM___rarg___closed__1();
lean_mark_persistent(l_Array_filterRevM___rarg___closed__1);
l_Array_partition___rarg___closed__1 = _init_l_Array_partition___rarg___closed__1();
lean_mark_persistent(l_Array_partition___rarg___closed__1);
l___auto____x40_Init_Data_Array_Basic___hyg_11923_ = _init_l___auto____x40_Init_Data_Array_Basic___hyg_11923_();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_11923_);
l_Array_eraseIdx_x21___rarg___closed__1 = _init_l_Array_eraseIdx_x21___rarg___closed__1();
lean_mark_persistent(l_Array_eraseIdx_x21___rarg___closed__1);
l_Array_eraseIdx_x21___rarg___closed__2 = _init_l_Array_eraseIdx_x21___rarg___closed__2();
lean_mark_persistent(l_Array_eraseIdx_x21___rarg___closed__2);
l_Array_eraseIdx_x21___rarg___closed__3 = _init_l_Array_eraseIdx_x21___rarg___closed__3();
lean_mark_persistent(l_Array_eraseIdx_x21___rarg___closed__3);
l___auto____x40_Init_Data_Array_Basic___hyg_12376_ = _init_l___auto____x40_Init_Data_Array_Basic___hyg_12376_();
lean_mark_persistent(l___auto____x40_Init_Data_Array_Basic___hyg_12376_);
l_Array_insertIdx_x21___rarg___closed__1 = _init_l_Array_insertIdx_x21___rarg___closed__1();
lean_mark_persistent(l_Array_insertIdx_x21___rarg___closed__1);
l_Array_insertIdx_x21___rarg___closed__2 = _init_l_Array_insertIdx_x21___rarg___closed__2();
lean_mark_persistent(l_Array_insertIdx_x21___rarg___closed__2);
l_Array_unzip___rarg___closed__1 = _init_l_Array_unzip___rarg___closed__1();
lean_mark_persistent(l_Array_unzip___rarg___closed__1);
l_Array_getEvenElems___rarg___closed__1 = _init_l_Array_getEvenElems___rarg___closed__1();
lean_mark_persistent(l_Array_getEvenElems___rarg___closed__1);
l_Array_instRepr___rarg___closed__1 = _init_l_Array_instRepr___rarg___closed__1();
lean_mark_persistent(l_Array_instRepr___rarg___closed__1);
l_Array_instRepr___rarg___closed__2 = _init_l_Array_instRepr___rarg___closed__2();
lean_mark_persistent(l_Array_instRepr___rarg___closed__2);
l_Array_instRepr___rarg___closed__3 = _init_l_Array_instRepr___rarg___closed__3();
lean_mark_persistent(l_Array_instRepr___rarg___closed__3);
l_Array_instRepr___rarg___closed__4 = _init_l_Array_instRepr___rarg___closed__4();
lean_mark_persistent(l_Array_instRepr___rarg___closed__4);
l_Array_instRepr___rarg___closed__5 = _init_l_Array_instRepr___rarg___closed__5();
lean_mark_persistent(l_Array_instRepr___rarg___closed__5);
l_Array_instRepr___rarg___closed__6 = _init_l_Array_instRepr___rarg___closed__6();
lean_mark_persistent(l_Array_instRepr___rarg___closed__6);
l_Array_instRepr___rarg___closed__7 = _init_l_Array_instRepr___rarg___closed__7();
lean_mark_persistent(l_Array_instRepr___rarg___closed__7);
l_Array_instRepr___rarg___closed__8 = _init_l_Array_instRepr___rarg___closed__8();
lean_mark_persistent(l_Array_instRepr___rarg___closed__8);
l_Array_instToString___rarg___closed__1 = _init_l_Array_instToString___rarg___closed__1();
lean_mark_persistent(l_Array_instToString___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
