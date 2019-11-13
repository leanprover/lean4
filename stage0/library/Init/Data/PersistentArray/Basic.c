// Lean compiler output
// Module: Init.Data.PersistentArray.Basic
// Imports: Init.Control.Conditional Init.Data.Array.Default
#include "runtime/lean.h"
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
lean_object* l_PersistentArray_foldlFromMAux___main___at_PersistentArray_foldlFrom___spec__2___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_PersistentArray_anyM___at_PersistentArray_any___spec__1(lean_object*);
lean_object* l_PersistentArray_empty___closed__2;
lean_object* l_mkPArray(lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__7(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__5(lean_object*, lean_object*);
lean_object* l_PersistentArray_mapM___at_PersistentArray_map___spec__1(lean_object*, lean_object*);
lean_object* l_PersistentArray_all(lean_object*);
lean_object* l_PersistentArray_any(lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_mapMAux___main___rarg___closed__1;
uint8_t l_Array_anyMAux___main___at_PersistentArray_all___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__5___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_PersistentArray_map___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toPersistentArrayAux___main(lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at_PersistentArray_all___spec__2(lean_object*);
lean_object* l_PersistentArray_collectStats(lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at_PersistentArray_allM___spec__2(lean_object*, lean_object*);
lean_object* l_PersistentArray_collectStats___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_stats(lean_object*);
lean_object* l_PersistentArray_mkNewTail(lean_object*);
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__5(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_all___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevMAux___main___boxed(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_PersistentArray_setAux___rarg(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_PersistentArray_mul2Shift(size_t, size_t);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__3___boxed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_modifyAux(lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg___lambda__1(lean_object*, uint8_t);
uint8_t l_PersistentArray_all___rarg(lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_forM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_forMAux(lean_object*, lean_object*);
lean_object* l_PersistentArrayNode_isNode___rarg___boxed(lean_object*);
lean_object* l_PersistentArray_popLeaf___rarg(lean_object*);
lean_object* l_PersistentArray_popLeaf___main___rarg___closed__1;
lean_object* l_PersistentArray_insertNewLeaf___main(lean_object*);
lean_object* l_PersistentArray_mapMAux___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromMAux___main___at_PersistentArray_foldlFrom___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_PersistentArray_map___spec__5(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Array_iterateMAux___main___at_Array_toPersistentArray___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_any___rarg___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_getAux___main___rarg(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Array_toPArray___rarg(lean_object*);
lean_object* l_PersistentArray_mapMAux___main___rarg___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shift__right(size_t, size_t);
lean_object* l_PersistentArray_findM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_mkNewPath___main(lean_object*);
lean_object* l_PersistentArray_anyM___at_PersistentArray_all___spec__1(lean_object*);
uint8_t l_Array_anyMAux___main___at_PersistentArray_any___spec__3___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyM___at_PersistentArray_all___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_insertNewLeaf___rarg(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_any___spec__4(lean_object*);
lean_object* l_PersistentArray_toList___rarg___boxed(lean_object*);
lean_object* l_List_toPersistentArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_forMAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromMAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__8(lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromMAux(lean_object*, lean_object*);
lean_object* l_PersistentArray_mkNewPath___rarg___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_findM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_toList___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__4(lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_insertNewLeaf___main___rarg(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Nat_foldAux___main___at_mkPersistentArray___spec__1(lean_object*);
lean_object* l_PersistentArray_findMAux___main___at_PersistentArray_find___spec__2(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toPersistentArrayAux(lean_object*);
lean_object* l_PersistentArray_findRevM___at_PersistentArray_findRev___spec__1(lean_object*, lean_object*);
lean_object* l_PersistentArray_mapM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__3(lean_object*, lean_object*);
lean_object* l_PersistentArray_Stats_toString___closed__2;
lean_object* l_PersistentArray_getAux(lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_isEmpty___rarg___boxed(lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__5___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_PersistentArray_mapM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__5(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFrom(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_forMAux___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_PersistentArray_map___spec__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at_PersistentArray_allM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Array_anyMAux___main___at_PersistentArray_any___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevMAux___main___at_PersistentArray_findRev___spec__3___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_forMAux___main(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM(lean_object*, lean_object*);
lean_object* l_PersistentArray_getAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_any___spec__5(lean_object*);
lean_object* l_Array_umapMAux___main___at_PersistentArray_map___spec__4(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_PersistentArray_map___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__3(lean_object*, lean_object*);
lean_object* l_PersistentArray_findRev(lean_object*, lean_object*);
lean_object* l_PersistentArray_push(lean_object*);
lean_object* l_PersistentArray_mkNewTail___rarg(lean_object*);
lean_object* l_PersistentArray_modifyAux___main___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_PersistentArray_anyMAux___main___at_PersistentArray_any___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_toPArray___rarg___boxed(lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_any___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__4(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_foldlFrom___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_get_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__1(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__5(lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findM___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_allM(lean_object*, lean_object*);
lean_object* l_PersistentArray_mapMAux___main(lean_object*, lean_object*);
lean_object* l_PersistentArray_mul2Shift___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_PersistentArray_map(lean_object*, lean_object*);
lean_object* l_PersistentArray_set___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_collectStats___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_mapMAux___main___rarg___lambda__1(lean_object*);
lean_object* l_PersistentArray_foldlM___at_PersistentArray_toList___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_mkEmptyArray(lean_object*);
lean_object* l_PersistentArray_findRevMAux___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at_PersistentArray_allM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___boxed(lean_object*, lean_object*);
lean_object* l_Array_toPersistentArray___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__3(lean_object*, lean_object*);
lean_object* l_PersistentArray_mapMAux___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__2(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_foldlFrom___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findMAux___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_pop___rarg(lean_object*);
lean_object* l_PersistentArray_mapMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___boxed(lean_object*, lean_object*);
size_t l_PersistentArray_initShift;
lean_object* l_Array_anyMAux___main___at_PersistentArray_all___spec__3(lean_object*);
lean_object* l_PersistentArray_anyM___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findMAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at_mkPersistentArray___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArrayNode_Inhabited(lean_object*);
lean_object* l___private_Init_Data_PersistentArray_Basic_1__emptyArray(lean_object*);
lean_object* l_PersistentArray_allM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_Stats_toString___closed__4;
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyMAux___main___at_PersistentArray_all___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_setAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_setAux(lean_object*);
lean_object* l_List_toPersistentArray___rarg(lean_object*);
lean_object* l_PersistentArray_tooBig___closed__1;
lean_object* l_PersistentArray_anyMAux___main(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* l_PersistentArray_mapMAux___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at_PersistentArray_allM___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at_PersistentArray_all___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_empty___closed__3;
lean_object* l_PersistentArray_findM___at_PersistentArray_find___spec__1(lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__2(lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_any___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_toList___rarg(lean_object*);
uint8_t l_PersistentArray_any___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_empty___closed__1;
lean_object* l_PersistentArray_Stats_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_all___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_toList___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_PersistentArray_foldlFromMAux___main(lean_object*, lean_object*);
lean_object* l_PersistentArray_allM___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldl(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromM___at_PersistentArray_foldlFrom___spec__1(lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_PersistentArray_all___rarg___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_toList(lean_object*);
lean_object* l_Array_toPArray(lean_object*);
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_mkNewPath___main___rarg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_PersistentArray_collectStats___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_any___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_isEmpty(lean_object*);
lean_object* l_PersistentArray_mapMAux(lean_object*, lean_object*);
lean_object* l_PersistentArray_forM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_empty(lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__6(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldl___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_set(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_toPersistentArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevMAux(lean_object*, lean_object*);
lean_object* l_PersistentArray_stats___rarg(lean_object*);
lean_object* l_PersistentArray_anyM___at_PersistentArray_allM___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevMAux___main(lean_object*, lean_object*);
lean_object* l_PersistentArray_mapM___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_mkNewPath___rarg(size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlM___at_PersistentArray_foldl___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_mapMAux___main___at_PersistentArray_map___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_PersistentArray_map___spec__3(lean_object*, lean_object*);
lean_object* l_PersistentArray_setAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_HasToString;
lean_object* l_PersistentArray_foldlFromM___at_PersistentArray_foldlFrom___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_PersistentArray_forM(lean_object*, lean_object*);
lean_object* l_PersistentArray_popLeaf___main___rarg(lean_object*);
lean_object* l_PersistentArray_findRev___rarg___boxed(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_PersistentArray_collectStats___main(lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_collectStats___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__9(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__5___boxed(lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at_PersistentArray_all___spec__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_forMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromM(lean_object*, lean_object*);
lean_object* l_PersistentArray_find___rarg___boxed(lean_object*, lean_object*);
size_t l_PersistentArray_mod2Shift(size_t, size_t);
uint8_t l_Array_anyMAux___main___at_PersistentArray_all___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromMAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromMAux___main___at_PersistentArray_foldlFrom___spec__2(lean_object*, lean_object*);
lean_object* l_Array_toPersistentArray___rarg___boxed(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__1(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_all___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at_PersistentArray_any___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_List_toPersistentArrayAux___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_setAux___main(lean_object*);
lean_object* l_PersistentArray_popLeaf(lean_object*);
lean_object* l_PersistentArray_Stats_toString___closed__1;
lean_object* l_PersistentArray_getAux___main___rarg___closed__1;
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__4(lean_object*, lean_object*);
lean_object* l_PersistentArray_forMAux___main___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_foldlFrom___spec__3(lean_object*, lean_object*);
lean_object* l_PersistentArray_mapMAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlM(lean_object*, lean_object*);
lean_object* l_PersistentArray_tooBig;
lean_object* l_Array_findMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_popLeaf___main(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_toPersistentArray___spec__1(lean_object*);
lean_object* l_PersistentArray_Inhabited(lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_all___spec__4(lean_object*);
lean_object* l_PersistentArray_anyMAux___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toPersistentArray(lean_object*);
lean_object* l_PersistentArray_get_x21(lean_object*);
lean_object* l_PersistentArray_mapMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_all___spec__5(lean_object*);
lean_object* l_PersistentArrayNode_Inhabited___closed__1;
lean_object* l_PersistentArray_foldlFromMAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_forMAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_modify___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_mapM___at_PersistentArray_map___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_collectStats___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArrayNode_isNode(lean_object*);
lean_object* l_PersistentArray_modify___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_PersistentArray_mkNewPath___main___rarg(size_t, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_collectStats___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_modifyAux___main(lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at_PersistentArray_allM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__5(lean_object*);
lean_object* l_PersistentArray_insertNewLeaf___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at_PersistentArray_allM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_getAux___rarg(lean_object*, lean_object*, size_t, size_t);
lean_object* l_PersistentArray_mapM(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromM___at_PersistentArray_foldlFrom___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_stats___rarg___boxed(lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at_PersistentArray_any___spec__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_find___rarg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_PersistentArray_anyM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_forM___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_get_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_div2Shift___boxed(lean_object*, lean_object*);
lean_object* l_mkPersistentArray___rarg(lean_object*, lean_object*);
lean_object* l_mkPersistentArray(lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__4(lean_object*);
lean_object* l_PersistentArray_getAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_Stats_toString___closed__3;
size_t l_PersistentArray_div2Shift(size_t, size_t);
lean_object* l_PersistentArray_findM(lean_object*, lean_object*);
lean_object* l_PersistentArray_set___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_find(lean_object*, lean_object*);
lean_object* l_PersistentArray_modifyAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toPersistentArray___rarg___closed__1;
lean_object* l_PersistentArray_foldlM___at_PersistentArray_foldl___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_foldl___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_mapMAux___main___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFrom___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevM___at_PersistentArray_findRev___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_forMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__5(lean_object*, lean_object*);
lean_object* l_PersistentArray_mapMAux___main___rarg___closed__2;
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at_PersistentArray_allM___spec__1(lean_object*, lean_object*);
lean_object* l_PersistentArray_HasToString___closed__1;
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__4(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_toList___spec__2(lean_object*);
lean_object* l_PersistentArray_foldlM___at_PersistentArray_foldl___spec__1(lean_object*, lean_object*);
lean_object* l_PersistentArray_map___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_insertNewLeaf___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at_PersistentArray_all___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_findM___at_PersistentArray_find___spec__1___rarg(lean_object*, lean_object*);
size_t l_PersistentArray_branching;
lean_object* l_PersistentArray_mapMAux___main___at_PersistentArray_map___spec__2(lean_object*, lean_object*);
lean_object* l_PersistentArray_modify(lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlM___at_PersistentArray_toList___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_usizeSz;
lean_object* l_PersistentArray_foldlM___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_PersistentArray_foldlFromMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyM___at_PersistentArray_any___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevM___at_PersistentArray_findRev___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevMAux___main___at_PersistentArray_findRev___spec__3___rarg___boxed(lean_object*, lean_object*);
uint8_t l_PersistentArrayNode_isNode___rarg(lean_object*);
lean_object* l_PersistentArray_findMAux___main(lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_PersistentArray_pop(lean_object*);
lean_object* l_PersistentArray_findMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_mapM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__4(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromM___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_modifyAux___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t);
size_t l_USize_shift__left(size_t, size_t);
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_any___spec__3(lean_object*);
lean_object* l_PersistentArray_mapM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_getAux___main(lean_object*);
lean_object* l_PersistentArray_anyM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_mod2Shift___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_PersistentArray_findMAux(lean_object*, lean_object*);
lean_object* l_PersistentArray_findMAux___main___at_PersistentArray_find___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Nat_max(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at_mkPersistentArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFrom___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_PersistentArray_findRev___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_setAux___main___rarg(lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_toPersistentArray(lean_object*);
lean_object* l_PersistentArray_insertNewLeaf(lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux(lean_object*, lean_object*);
lean_object* l_PersistentArray_mapMAux___main___rarg___lambda__3(lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__3(lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromMAux___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_foldl___spec__2(lean_object*, lean_object*);
uint8_t l_PersistentArray_anyMAux___main___at_PersistentArray_any___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_foldl___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldl___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_mkNewPath(lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentArray_collectStats___main___spec__1(lean_object*);
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_modifyAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlM___at_PersistentArray_toList___spec__1(lean_object*);
lean_object* l_mkPArray___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevM___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevM(lean_object*, lean_object*);
lean_object* l_PersistentArray_findMAux___main___at_PersistentArray_find___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_PersistentArray_findRevMAux___main___at_PersistentArray_findRev___spec__3(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at_PersistentArray_any___spec__2(lean_object*);
uint8_t l_PersistentArray_isEmpty___rarg(lean_object*);
lean_object* l_PersistentArray_anyM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_PersistentArray_foldlMAux___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findM___at_PersistentArray_find___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* _init_l_PersistentArrayNode_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_PersistentArrayNode_Inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PersistentArrayNode_Inhabited___closed__1;
return x_2;
}
}
uint8_t l_PersistentArrayNode_isNode___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
lean_object* l_PersistentArrayNode_isNode(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArrayNode_isNode___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_PersistentArrayNode_isNode___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_PersistentArrayNode_isNode___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
size_t _init_l_PersistentArray_initShift() {
_start:
{
size_t x_1; 
x_1 = 5;
return x_1;
}
}
size_t _init_l_PersistentArray_branching() {
_start:
{
size_t x_1; 
x_1 = 32;
return x_1;
}
}
lean_object* _init_l_PersistentArray_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* _init_l_PersistentArray_empty___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_PersistentArray_empty___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_PersistentArray_empty___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_PersistentArray_empty___closed__2;
x_3 = l_PersistentArray_empty___closed__1;
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
lean_object* l_PersistentArray_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PersistentArray_empty___closed__3;
return x_2;
}
}
uint8_t l_PersistentArray_isEmpty___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
lean_object* l_PersistentArray_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_isEmpty___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_PersistentArray_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_PersistentArray_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_Inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PersistentArray_empty___closed__3;
return x_2;
}
}
lean_object* l_PersistentArray_mkEmptyArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PersistentArray_empty___closed__1;
return x_2;
}
}
size_t l_PersistentArray_mul2Shift(size_t x_1, size_t x_2) {
_start:
{
size_t x_3; 
x_3 = x_1 << x_2;
return x_3;
}
}
lean_object* l_PersistentArray_mul2Shift___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentArray_mul2Shift(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
size_t l_PersistentArray_div2Shift(size_t x_1, size_t x_2) {
_start:
{
size_t x_3; 
x_3 = x_1 >> x_2;
return x_3;
}
}
lean_object* l_PersistentArray_div2Shift___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentArray_div2Shift(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
size_t l_PersistentArray_mod2Shift(size_t x_1, size_t x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; size_t x_6; 
x_3 = 1;
x_4 = x_3 << x_2;
x_5 = x_4 - x_3;
x_6 = x_1 & x_5;
return x_6;
}
}
lean_object* l_PersistentArray_mod2Shift___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentArray_mod2Shift(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
lean_object* _init_l_PersistentArray_getAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_PersistentArrayNode_Inhabited(lean_box(0));
return x_1;
}
}
lean_object* l_PersistentArray_getAux___main___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = x_3 >> x_4;
x_7 = lean_usize_to_nat(x_6);
x_8 = l_PersistentArray_getAux___main___rarg___closed__1;
x_9 = lean_array_get(x_8, x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
x_10 = 1;
x_11 = x_10 << x_4;
x_12 = x_11 - x_10;
x_13 = x_3 & x_12;
x_14 = 5;
x_15 = x_4 - x_14;
x_2 = x_9;
x_3 = x_13;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_usize_to_nat(x_3);
x_19 = lean_array_get(x_1, x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
return x_19;
}
}
}
lean_object* l_PersistentArray_getAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_getAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_PersistentArray_getAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_PersistentArray_getAux___main___rarg(x_1, x_2, x_5, x_6);
return x_7;
}
}
lean_object* l_PersistentArray_getAux___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_getAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentArray_getAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_getAux___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_PersistentArray_getAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_PersistentArray_getAux___rarg(x_1, x_2, x_5, x_6);
return x_7;
}
}
lean_object* l_PersistentArray_get_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
x_5 = lean_nat_dec_le(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_usize_of_nat(x_3);
x_8 = lean_ctor_get_usize(x_2, 4);
lean_dec(x_2);
x_9 = l_PersistentArray_getAux___main___rarg(x_1, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_12 = lean_array_get(x_1, x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
return x_12;
}
}
}
lean_object* l_PersistentArray_get_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_get_x21___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_PersistentArray_get_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_get_x21___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_PersistentArray_setAux___main___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = x_2 >> x_3;
x_8 = 1;
x_9 = x_8 << x_3;
x_10 = x_9 - x_8;
x_11 = x_2 & x_10;
x_12 = 5;
x_13 = x_3 - x_12;
x_14 = lean_usize_to_nat(x_7);
x_15 = lean_array_get_size(x_6);
x_16 = lean_nat_dec_lt(x_14, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_fget(x_6, x_14);
x_18 = l_PersistentArrayNode_Inhabited___closed__1;
x_19 = lean_array_fset(x_6, x_14, x_18);
x_20 = l_PersistentArray_setAux___main___rarg(x_17, x_11, x_13, x_4);
x_21 = lean_array_fset(x_19, x_14, x_20);
lean_dec(x_14);
lean_ctor_set(x_1, 0, x_21);
return x_1;
}
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = x_2 >> x_3;
x_24 = 1;
x_25 = x_24 << x_3;
x_26 = x_25 - x_24;
x_27 = x_2 & x_26;
x_28 = 5;
x_29 = x_3 - x_28;
x_30 = lean_usize_to_nat(x_23);
x_31 = lean_array_get_size(x_22);
x_32 = lean_nat_dec_lt(x_30, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_4);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_22);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_array_fget(x_22, x_30);
x_35 = l_PersistentArrayNode_Inhabited___closed__1;
x_36 = lean_array_fset(x_22, x_30, x_35);
x_37 = l_PersistentArray_setAux___main___rarg(x_34, x_27, x_29, x_4);
x_38 = lean_array_fset(x_36, x_30, x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_1);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_usize_to_nat(x_2);
x_43 = lean_array_set(x_41, x_42, x_4);
lean_dec(x_42);
lean_ctor_set(x_1, 0, x_43);
return x_1;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_usize_to_nat(x_2);
x_46 = lean_array_set(x_44, x_45, x_4);
lean_dec(x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
lean_object* l_PersistentArray_setAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_setAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_PersistentArray_setAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_PersistentArray_setAux___main___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_PersistentArray_setAux___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_setAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentArray_setAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_setAux___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_PersistentArray_setAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_PersistentArray_setAux___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_PersistentArray_set___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get_usize(x_1, 4);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_nat_dec_le(x_8, x_2);
if (x_9 == 0)
{
size_t x_10; lean_object* x_11; 
x_10 = lean_usize_of_nat(x_2);
x_11 = l_PersistentArray_setAux___main___rarg(x_5, x_10, x_7, x_3);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_nat_sub(x_2, x_8);
x_13 = lean_array_set(x_6, x_12, x_3);
lean_dec(x_12);
lean_ctor_set(x_1, 1, x_13);
return x_1;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_ctor_get_usize(x_1, 4);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_19 = lean_nat_dec_le(x_18, x_2);
if (x_19 == 0)
{
size_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_usize_of_nat(x_2);
x_21 = l_PersistentArray_setAux___main___rarg(x_14, x_20, x_17, x_3);
x_22 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_16);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set_usize(x_22, 4, x_17);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_nat_sub(x_2, x_18);
x_24 = lean_array_set(x_15, x_23, x_3);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_16);
lean_ctor_set(x_25, 3, x_18);
lean_ctor_set_usize(x_25, 4, x_17);
return x_25;
}
}
}
}
lean_object* l_PersistentArray_set(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_set___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_PersistentArray_set___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_set___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_PersistentArray_modifyAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = x_4 >> x_5;
x_9 = 1;
x_10 = x_9 << x_5;
x_11 = x_10 - x_9;
x_12 = x_4 & x_11;
x_13 = 5;
x_14 = x_5 - x_13;
x_15 = lean_usize_to_nat(x_8);
x_16 = lean_array_get_size(x_7);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_7, x_15);
x_19 = l_PersistentArrayNode_Inhabited___closed__1;
x_20 = lean_array_fset(x_7, x_15, x_19);
x_21 = l_PersistentArray_modifyAux___main___rarg(x_1, x_2, x_18, x_12, x_14);
x_22 = lean_array_fset(x_20, x_15, x_21);
lean_dec(x_15);
lean_ctor_set(x_3, 0, x_22);
return x_3;
}
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = x_4 >> x_5;
x_25 = 1;
x_26 = x_25 << x_5;
x_27 = x_26 - x_25;
x_28 = x_4 & x_27;
x_29 = 5;
x_30 = x_5 - x_29;
x_31 = lean_usize_to_nat(x_24);
x_32 = lean_array_get_size(x_23);
x_33 = lean_nat_dec_lt(x_31, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_23);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_array_fget(x_23, x_31);
x_36 = l_PersistentArrayNode_Inhabited___closed__1;
x_37 = lean_array_fset(x_23, x_31, x_36);
x_38 = l_PersistentArray_modifyAux___main___rarg(x_1, x_2, x_35, x_28, x_30);
x_39 = lean_array_fset(x_37, x_31, x_38);
lean_dec(x_31);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_3);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_3, 0);
x_43 = lean_usize_to_nat(x_4);
x_44 = lean_array_get_size(x_42);
x_45 = lean_nat_dec_lt(x_43, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_array_fget(x_42, x_43);
x_47 = lean_array_fset(x_42, x_43, x_1);
x_48 = lean_apply_1(x_2, x_46);
x_49 = lean_array_fset(x_47, x_43, x_48);
lean_dec(x_43);
lean_ctor_set(x_3, 0, x_49);
return x_3;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_3, 0);
lean_inc(x_50);
lean_dec(x_3);
x_51 = lean_usize_to_nat(x_4);
x_52 = lean_array_get_size(x_50);
x_53 = lean_nat_dec_lt(x_51, x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_51);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_50);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_array_fget(x_50, x_51);
x_56 = lean_array_fset(x_50, x_51, x_1);
x_57 = lean_apply_1(x_2, x_55);
x_58 = lean_array_fset(x_56, x_51, x_57);
lean_dec(x_51);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
}
lean_object* l_PersistentArray_modifyAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_modifyAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_PersistentArray_modifyAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_PersistentArray_modifyAux___main___rarg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
lean_object* l_PersistentArray_modifyAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentArray_modifyAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_PersistentArray_modifyAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_modifyAux___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_PersistentArray_modifyAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_PersistentArray_modifyAux___rarg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
lean_object* l_PersistentArray_modify___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get_usize(x_2, 4);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_nat_dec_le(x_9, x_3);
if (x_10 == 0)
{
size_t x_11; lean_object* x_12; 
x_11 = lean_usize_of_nat(x_3);
x_12 = l_PersistentArray_modifyAux___main___rarg(x_1, x_4, x_6, x_11, x_8);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_nat_sub(x_3, x_9);
x_14 = lean_array_get_size(x_7);
x_15 = lean_nat_dec_lt(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_7, x_13);
x_17 = lean_array_fset(x_7, x_13, x_1);
x_18 = lean_apply_1(x_4, x_16);
x_19 = lean_array_fset(x_17, x_13, x_18);
lean_dec(x_13);
lean_ctor_set(x_2, 1, x_19);
return x_2;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get_usize(x_2, 4);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_25 = lean_nat_dec_le(x_24, x_3);
if (x_25 == 0)
{
size_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_usize_of_nat(x_3);
x_27 = l_PersistentArray_modifyAux___main___rarg(x_1, x_4, x_20, x_26, x_23);
x_28 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set_usize(x_28, 4, x_23);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_nat_sub(x_3, x_24);
x_30 = lean_array_get_size(x_21);
x_31 = lean_nat_dec_lt(x_29, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_4);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_24);
lean_ctor_set_usize(x_32, 4, x_23);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_array_fget(x_21, x_29);
x_34 = lean_array_fset(x_21, x_29, x_1);
x_35 = lean_apply_1(x_4, x_33);
x_36 = lean_array_fset(x_34, x_29, x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_22);
lean_ctor_set(x_37, 3, x_24);
lean_ctor_set_usize(x_37, 4, x_23);
return x_37;
}
}
}
}
}
lean_object* l_PersistentArray_modify(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_modify___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_PersistentArray_modify___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_modify___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentArray_mkNewPath___main___rarg(size_t x_1, lean_object* x_2) {
_start:
{
size_t x_3; uint8_t x_4; 
x_3 = 0;
x_4 = x_1 == x_3;
if (x_4 == 0)
{
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = 5;
x_6 = x_1 - x_5;
x_7 = l_PersistentArray_mkNewPath___main___rarg(x_6, x_2);
x_8 = l_PersistentArray_empty___closed__1;
x_9 = lean_array_push(x_8, x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
}
}
lean_object* l_PersistentArray_mkNewPath___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_mkNewPath___main___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_PersistentArray_mkNewPath___main___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_PersistentArray_mkNewPath___main___rarg(x_3, x_2);
return x_4;
}
}
lean_object* l_PersistentArray_mkNewPath___rarg(size_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_mkNewPath___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_PersistentArray_mkNewPath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_mkNewPath___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_PersistentArray_mkNewPath___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_PersistentArray_mkNewPath___rarg(x_3, x_2);
return x_4;
}
}
lean_object* l_PersistentArray_insertNewLeaf___main___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 32;
x_8 = x_2 < x_7;
if (x_8 == 0)
{
size_t x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = x_2 >> x_3;
x_10 = 1;
x_11 = x_10 << x_3;
x_12 = x_11 - x_10;
x_13 = x_2 & x_12;
x_14 = 5;
x_15 = x_3 - x_14;
x_16 = lean_usize_to_nat(x_9);
x_17 = lean_array_get_size(x_6);
x_18 = lean_nat_dec_lt(x_16, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
x_19 = l_PersistentArray_mkNewPath___main___rarg(x_15, x_4);
x_20 = lean_array_push(x_6, x_19);
lean_ctor_set(x_1, 0, x_20);
return x_1;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_array_fget(x_6, x_16);
x_22 = l_PersistentArrayNode_Inhabited___closed__1;
x_23 = lean_array_fset(x_6, x_16, x_22);
x_24 = l_PersistentArray_insertNewLeaf___main___rarg(x_21, x_13, x_15, x_4);
x_25 = lean_array_fset(x_23, x_16, x_24);
lean_dec(x_16);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_4);
x_26 = lean_array_push(x_6, x_1);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; size_t x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = 32;
x_30 = x_2 < x_29;
if (x_30 == 0)
{
size_t x_31; size_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_31 = x_2 >> x_3;
x_32 = 1;
x_33 = x_32 << x_3;
x_34 = x_33 - x_32;
x_35 = x_2 & x_34;
x_36 = 5;
x_37 = x_3 - x_36;
x_38 = lean_usize_to_nat(x_31);
x_39 = lean_array_get_size(x_28);
x_40 = lean_nat_dec_lt(x_38, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_38);
x_41 = l_PersistentArray_mkNewPath___main___rarg(x_37, x_4);
x_42 = lean_array_push(x_28, x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_array_fget(x_28, x_38);
x_45 = l_PersistentArrayNode_Inhabited___closed__1;
x_46 = lean_array_fset(x_28, x_38, x_45);
x_47 = l_PersistentArray_insertNewLeaf___main___rarg(x_44, x_35, x_37, x_4);
x_48 = lean_array_fset(x_46, x_38, x_47);
lean_dec(x_38);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_4);
x_51 = lean_array_push(x_28, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
lean_dec(x_4);
return x_1;
}
}
}
lean_object* l_PersistentArray_insertNewLeaf___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_insertNewLeaf___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_PersistentArray_insertNewLeaf___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_PersistentArray_insertNewLeaf___main___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_PersistentArray_insertNewLeaf___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_insertNewLeaf___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentArray_insertNewLeaf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_insertNewLeaf___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_PersistentArray_insertNewLeaf___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_PersistentArray_insertNewLeaf___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_PersistentArray_mkNewTail___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get_usize(x_1, 4);
x_7 = lean_ctor_get(x_1, 3);
lean_dec(x_7);
x_8 = 1;
x_9 = 5;
x_10 = x_6 + x_9;
x_11 = x_8 << x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_nat_dec_le(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = l_PersistentArray_empty___closed__1;
x_15 = lean_array_push(x_14, x_3);
x_16 = l_PersistentArray_mkNewPath___main___rarg(x_6, x_4);
x_17 = lean_array_push(x_15, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Array_empty___closed__1;
lean_inc(x_5);
lean_ctor_set(x_1, 3, x_5);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set_usize(x_1, 4, x_10);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_5, x_20);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = l_PersistentArray_insertNewLeaf___main___rarg(x_3, x_22, x_6, x_4);
x_24 = l_PersistentArray_empty___closed__1;
lean_inc(x_5);
lean_ctor_set(x_1, 3, x_5);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; uint8_t x_34; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 2);
x_28 = lean_ctor_get_usize(x_1, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_29 = 1;
x_30 = 5;
x_31 = x_28 + x_30;
x_32 = x_29 << x_31;
x_33 = lean_usize_to_nat(x_32);
x_34 = lean_nat_dec_le(x_27, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = l_PersistentArray_empty___closed__1;
x_36 = lean_array_push(x_35, x_25);
x_37 = l_PersistentArray_mkNewPath___main___rarg(x_28, x_26);
x_38 = lean_array_push(x_36, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Array_empty___closed__1;
lean_inc(x_27);
x_41 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_27);
lean_ctor_set(x_41, 3, x_27);
lean_ctor_set_usize(x_41, 4, x_31);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_27, x_42);
x_44 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_45 = l_PersistentArray_insertNewLeaf___main___rarg(x_25, x_44, x_28, x_26);
x_46 = l_PersistentArray_empty___closed__1;
lean_inc(x_27);
x_47 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_27);
lean_ctor_set(x_47, 3, x_27);
lean_ctor_set_usize(x_47, 4, x_28);
return x_47;
}
}
}
}
lean_object* l_PersistentArray_mkNewTail(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_mkNewTail___rarg), 1, 0);
return x_2;
}
}
lean_object* _init_l_PersistentArray_tooBig___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_usizeSz;
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_div(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_PersistentArray_tooBig() {
_start:
{
lean_object* x_1; 
x_1 = l_PersistentArray_tooBig___closed__1;
return x_1;
}
}
lean_object* l_PersistentArray_push___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_array_push(x_4, x_2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_5, x_7);
lean_inc(x_6);
lean_ctor_set(x_1, 2, x_8);
lean_ctor_set(x_1, 1, x_6);
x_9 = lean_array_get_size(x_6);
lean_dec(x_6);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_PersistentArray_tooBig;
x_13 = lean_nat_dec_le(x_12, x_5);
lean_dec(x_5);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_PersistentArray_mkNewTail___rarg(x_1);
return x_14;
}
else
{
return x_1;
}
}
else
{
lean_dec(x_5);
return x_1;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_ctor_get_usize(x_1, 4);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_20 = lean_array_push(x_16, x_2);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_17, x_21);
lean_inc(x_20);
x_23 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set_usize(x_23, 4, x_18);
x_24 = lean_array_get_size(x_20);
lean_dec(x_20);
x_25 = lean_unsigned_to_nat(32u);
x_26 = lean_nat_dec_lt(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_PersistentArray_tooBig;
x_28 = lean_nat_dec_le(x_27, x_17);
lean_dec(x_17);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_PersistentArray_mkNewTail___rarg(x_23);
return x_29;
}
else
{
return x_23;
}
}
else
{
lean_dec(x_17);
return x_23;
}
}
}
}
lean_object* l_PersistentArray_push(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_push___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_PersistentArray_Basic_1__emptyArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PersistentArray_empty___closed__1;
return x_2;
}
}
lean_object* _init_l_PersistentArray_popLeaf___main___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_PersistentArray_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_PersistentArray_popLeaf___main___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
x_9 = lean_array_fget(x_3, x_8);
x_10 = l_PersistentArrayNode_Inhabited___closed__1;
x_11 = lean_array_fset(x_3, x_8, x_10);
x_12 = l_PersistentArray_popLeaf___main___rarg(x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_8);
lean_free_object(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = l_PersistentArray_empty___closed__1;
lean_ctor_set(x_12, 1, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_18 = l_PersistentArray_empty___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_12, 1);
x_22 = lean_ctor_get(x_12, 0);
lean_dec(x_22);
x_23 = lean_array_get_size(x_21);
x_24 = lean_nat_dec_eq(x_23, x_5);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_ctor_set(x_1, 0, x_21);
x_25 = lean_array_fset(x_11, x_8, x_1);
lean_dec(x_8);
lean_ctor_set(x_12, 1, x_25);
return x_12;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_21);
lean_dec(x_8);
lean_free_object(x_1);
x_26 = lean_array_pop(x_11);
x_27 = l_Array_isEmpty___rarg(x_26);
if (x_27 == 0)
{
lean_ctor_set(x_12, 1, x_26);
return x_12;
}
else
{
lean_object* x_28; 
lean_dec(x_26);
x_28 = l_PersistentArray_empty___closed__1;
lean_ctor_set(x_12, 1, x_28);
return x_12;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_eq(x_30, x_5);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_ctor_set(x_1, 0, x_29);
x_32 = lean_array_fset(x_11, x_8, x_1);
lean_dec(x_8);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_29);
lean_dec(x_8);
lean_free_object(x_1);
x_34 = lean_array_pop(x_11);
x_35 = l_Array_isEmpty___rarg(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
x_37 = l_PersistentArray_empty___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_13);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_4);
lean_free_object(x_1);
lean_dec(x_3);
x_39 = l_PersistentArray_popLeaf___main___rarg___closed__1;
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_array_get_size(x_40);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_eq(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_41, x_44);
lean_dec(x_41);
x_46 = lean_array_fget(x_40, x_45);
x_47 = l_PersistentArrayNode_Inhabited___closed__1;
x_48 = lean_array_fset(x_40, x_45, x_47);
x_49 = l_PersistentArray_popLeaf___main___rarg(x_46);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_48);
lean_dec(x_45);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = l_PersistentArray_empty___closed__1;
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_55 = x_49;
} else {
 lean_dec_ref(x_49);
 x_55 = lean_box(0);
}
x_56 = lean_array_get_size(x_54);
x_57 = lean_nat_dec_eq(x_56, x_42);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_54);
x_59 = lean_array_fset(x_48, x_45, x_58);
lean_dec(x_45);
if (lean_is_scalar(x_55)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_55;
}
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
else
{
lean_object* x_61; uint8_t x_62; 
lean_dec(x_54);
lean_dec(x_45);
x_61 = lean_array_pop(x_48);
x_62 = l_Array_isEmpty___rarg(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
if (lean_is_scalar(x_55)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_55;
}
lean_ctor_set(x_63, 0, x_50);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_61);
x_64 = l_PersistentArray_empty___closed__1;
if (lean_is_scalar(x_55)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_55;
}
lean_ctor_set(x_65, 0, x_50);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
lean_object* x_66; 
lean_dec(x_41);
lean_dec(x_40);
x_66 = l_PersistentArray_popLeaf___main___rarg___closed__1;
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
lean_dec(x_1);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = l_PersistentArray_empty___closed__1;
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
lean_object* l_PersistentArray_popLeaf___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_popLeaf___main___rarg), 1, 0);
return x_2;
}
}
lean_object* l_PersistentArray_popLeaf___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PersistentArray_popLeaf___main___rarg(x_1);
return x_2;
}
}
lean_object* l_PersistentArray_popLeaf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_popLeaf___rarg), 1, 0);
return x_2;
}
}
lean_object* l_PersistentArray_pop___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get_usize(x_1, 4);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_array_get_size(x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_3);
x_10 = l_PersistentArray_popLeaf___main___rarg(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_10);
lean_dec(x_4);
return x_1;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_13 = lean_ctor_get(x_1, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_array_pop(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_4, x_20);
lean_dec(x_4);
x_22 = lean_array_get_size(x_19);
x_23 = lean_nat_sub(x_21, x_22);
lean_dec(x_22);
x_24 = lean_array_get_size(x_17);
x_25 = lean_nat_dec_eq(x_24, x_20);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_1, 3, x_23);
lean_ctor_set(x_1, 2, x_21);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_PersistentArray_getAux___main___rarg___closed__1;
x_28 = lean_array_get(x_27, x_17, x_8);
x_29 = l_PersistentArrayNode_isNode___rarg(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_1, 3, x_23);
lean_ctor_set(x_1, 2, x_21);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_30);
return x_1;
}
else
{
size_t x_31; size_t x_32; 
lean_dec(x_17);
x_31 = 5;
x_32 = x_5 - x_31;
lean_ctor_set(x_1, 3, x_23);
lean_ctor_set(x_1, 2, x_21);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_28);
lean_ctor_set_usize(x_1, 4, x_32);
return x_1;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_1);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_dec(x_10);
x_34 = lean_ctor_get(x_11, 0);
lean_inc(x_34);
lean_dec(x_11);
x_35 = lean_array_pop(x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_sub(x_4, x_36);
lean_dec(x_4);
x_38 = lean_array_get_size(x_35);
x_39 = lean_nat_sub(x_37, x_38);
lean_dec(x_38);
x_40 = lean_array_get_size(x_33);
x_41 = lean_nat_dec_eq(x_40, x_36);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_33);
x_43 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_35);
lean_ctor_set(x_43, 2, x_37);
lean_ctor_set(x_43, 3, x_39);
lean_ctor_set_usize(x_43, 4, x_5);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = l_PersistentArray_getAux___main___rarg___closed__1;
x_45 = lean_array_get(x_44, x_33, x_8);
x_46 = l_PersistentArrayNode_isNode___rarg(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_33);
x_48 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_35);
lean_ctor_set(x_48, 2, x_37);
lean_ctor_set(x_48, 3, x_39);
lean_ctor_set_usize(x_48, 4, x_5);
return x_48;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; 
lean_dec(x_33);
x_49 = 5;
x_50 = x_5 - x_49;
x_51 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_35);
lean_ctor_set(x_51, 2, x_37);
lean_ctor_set(x_51, 3, x_39);
lean_ctor_set_usize(x_51, 4, x_50);
return x_51;
}
}
}
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_1);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_1, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_1, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_1, 0);
lean_dec(x_56);
x_57 = lean_array_pop(x_3);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_4, x_58);
lean_dec(x_4);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_57);
return x_1;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_1);
x_60 = lean_array_pop(x_3);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_sub(x_4, x_61);
lean_dec(x_4);
x_63 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_63, 0, x_2);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_62);
lean_ctor_set(x_63, 3, x_6);
lean_ctor_set_usize(x_63, 4, x_5);
return x_63;
}
}
}
}
lean_object* l_PersistentArray_pop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_pop___rarg), 1, 0);
return x_2;
}
}
lean_object* l_PersistentArray_foldlMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentArray_foldlMAux___main___rarg(x_1, lean_box(0), x_2, x_4, x_5);
return x_6;
}
}
lean_object* l_PersistentArray_foldlMAux___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_PersistentArray_foldlMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_PersistentArray_foldlMAux___main___rarg___lambda__1___boxed), 5, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___rarg(x_1, lean_box(0), x_6, x_7, x_8, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_alloc_closure((void*)(l_PersistentArray_foldlMAux___main___rarg___lambda__2___boxed), 4, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateMAux___main___rarg(x_1, lean_box(0), x_10, x_11, x_12, x_5);
return x_13;
}
}
}
lean_object* l_PersistentArray_foldlMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_foldlMAux___main___rarg), 5, 0);
return x_3;
}
}
lean_object* l_PersistentArray_foldlMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentArray_foldlMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_PersistentArray_foldlMAux___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_foldlMAux___main___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_PersistentArray_foldlMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_foldlMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_foldlMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentArray_foldlMAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_PersistentArray_foldlMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_foldlMAux___rarg), 5, 0);
return x_3;
}
}
lean_object* l_PersistentArray_foldlMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_foldlMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_foldlM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_PersistentArray_foldlMAux___main___rarg___lambda__2___boxed), 4, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___main___rarg(x_3, lean_box(0), x_5, x_6, x_7, x_4);
return x_8;
}
}
lean_object* l_PersistentArray_foldlM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_1);
x_8 = l_PersistentArray_foldlMAux___main___rarg(x_1, lean_box(0), x_4, x_7, x_5);
x_9 = lean_alloc_closure((void*)(l_PersistentArray_foldlM___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_1);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_PersistentArray_foldlM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_foldlM___rarg), 5, 0);
return x_3;
}
}
lean_object* l_PersistentArray_foldlM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_foldlM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_findMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_PersistentArray_findMAux___main___rarg), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_findMAux___main___rarg(x_1, lean_box(0), x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_findMAux___main___rarg(x_1, lean_box(0), x_9, x_3, x_10);
return x_11;
}
}
}
lean_object* l_PersistentArray_findMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_findMAux___main___rarg), 4, 0);
return x_3;
}
}
lean_object* l_PersistentArray_findMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_findMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_findMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_findMAux___main___rarg(x_1, lean_box(0), x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentArray_findMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_findMAux___rarg), 4, 0);
return x_3;
}
}
lean_object* l_PersistentArray_findMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_findMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_findM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_findMAux___main___rarg(x_2, lean_box(0), x_5, x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_4);
return x_10;
}
}
}
lean_object* l_PersistentArray_findM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_7 = l_PersistentArray_findMAux___main___rarg(x_1, lean_box(0), x_4, x_6);
x_8 = lean_alloc_closure((void*)(l_PersistentArray_findM___rarg___lambda__1), 4, 3);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_4);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_PersistentArray_findM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_findM___rarg), 4, 0);
return x_3;
}
}
lean_object* l_PersistentArray_findM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_findM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_findRevMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_PersistentArray_findRevMAux___main___rarg), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_3);
x_7 = lean_array_get_size(x_5);
x_8 = l_Array_findRevMAux___main___rarg(x_1, lean_box(0), x_5, x_6, x_7, lean_box(0));
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_array_get_size(x_9);
x_11 = l_Array_findRevMAux___main___rarg(x_1, lean_box(0), x_9, x_3, x_10, lean_box(0));
lean_dec(x_10);
return x_11;
}
}
}
lean_object* l_PersistentArray_findRevMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_findRevMAux___main___rarg), 4, 0);
return x_3;
}
}
lean_object* l_PersistentArray_findRevMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_findRevMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_findRevMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_findRevMAux___main___rarg(x_1, lean_box(0), x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentArray_findRevMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_findRevMAux___rarg), 4, 0);
return x_3;
}
}
lean_object* l_PersistentArray_findRevMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_findRevMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_findRevM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_PersistentArray_findRevMAux___main___rarg(x_2, lean_box(0), x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_4);
return x_9;
}
}
}
lean_object* l_PersistentArray_findRevM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_8 = l_Array_findRevMAux___main___rarg(x_1, lean_box(0), x_6, x_4, x_7, lean_box(0));
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(l_PersistentArray_findRevM___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_4);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_PersistentArray_findRevM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_findRevM___rarg), 4, 0);
return x_3;
}
}
lean_object* l_PersistentArray_findRevM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_findRevM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_fget(x_5, x_6);
lean_inc(x_3);
lean_inc(x_1);
x_15 = l_PersistentArray_foldlMAux___main___rarg(x_1, lean_box(0), x_3, x_14, x_7);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_6, x_16);
x_18 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__1___rarg___boxed), 7, 6);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, lean_box(0));
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
lean_closure_set(x_18, 5, x_17);
x_19 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_18);
return x_19;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_fget(x_5, x_6);
lean_inc(x_3);
x_15 = lean_apply_2(x_3, x_7, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_6, x_16);
x_18 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__2___rarg___boxed), 7, 6);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, lean_box(0));
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
lean_closure_set(x_18, 5, x_17);
x_19 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_18);
return x_19;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__2___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_PersistentArray_foldlFromMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
lean_inc(x_4);
x_8 = l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__1___rarg(x_2, lean_box(0), x_3, x_4, x_4, x_7, x_5);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_PersistentArray_foldlFromMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = x_5 >> x_6;
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = l_PersistentArray_getAux___main___rarg___closed__1;
x_13 = lean_array_get(x_12, x_8, x_10);
x_14 = 1;
x_15 = x_14 << x_6;
x_16 = x_15 - x_14;
x_17 = x_5 & x_16;
x_18 = 5;
x_19 = x_6 - x_18;
lean_inc(x_3);
lean_inc(x_1);
x_20 = l_PersistentArray_foldlFromMAux___main___rarg(x_1, lean_box(0), x_3, x_13, x_17, x_19, x_7);
x_21 = lean_alloc_closure((void*)(l_PersistentArray_foldlFromMAux___main___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_21, 0, x_10);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_8);
x_22 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_20, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
lean_dec(x_4);
x_24 = lean_usize_to_nat(x_5);
lean_inc(x_23);
x_25 = l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__2___rarg(x_1, lean_box(0), x_3, x_23, x_23, x_24, x_7);
lean_dec(x_24);
return x_25;
}
}
}
lean_object* l_PersistentArray_foldlFromMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_foldlFromMAux___main___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateMAux___main___at_PersistentArray_foldlFromMAux___main___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_foldlFromMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentArray_foldlFromMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentArray_foldlFromMAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_PersistentArray_foldlFromMAux___main___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
lean_object* l_PersistentArray_foldlFromMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_foldlFromMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_foldlFromMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_PersistentArray_foldlFromMAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_PersistentArray_foldlFromMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_foldlFromMAux___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_PersistentArray_foldlFromMAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_PersistentArray_foldlFromMAux___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
lean_object* l_PersistentArray_foldlFromMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_foldlFromMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_fget(x_5, x_6);
lean_inc(x_4);
x_15 = lean_apply_2(x_4, x_7, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_6, x_16);
x_18 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__1___rarg___boxed), 7, 6);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, lean_box(0));
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
lean_closure_set(x_18, 5, x_17);
x_19 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_18);
return x_19;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_fget(x_5, x_6);
lean_inc(x_4);
x_15 = lean_apply_2(x_4, x_7, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_6, x_16);
x_18 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__2___rarg___boxed), 7, 6);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, lean_box(0));
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
lean_closure_set(x_18, 5, x_17);
x_19 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_18);
return x_19;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__2___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_PersistentArray_foldlFromM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__1___rarg(x_2, lean_box(0), x_1, x_3, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_PersistentArray_foldlFromM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_nat_dec_le(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_usize_of_nat(x_6);
x_12 = lean_ctor_get_usize(x_3, 4);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_PersistentArray_foldlFromMAux___main___rarg(x_1, lean_box(0), x_4, x_10, x_11, x_12, x_5);
x_14 = lean_alloc_closure((void*)(l_PersistentArray_foldlFromM___rarg___lambda__1), 4, 3);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_4);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
x_17 = lean_nat_sub(x_6, x_7);
lean_dec(x_7);
x_18 = l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__2___rarg(x_1, lean_box(0), x_3, x_4, x_16, x_17, x_5);
lean_dec(x_17);
return x_18;
}
}
}
lean_object* l_PersistentArray_foldlFromM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_foldlFromM___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateMAux___main___at_PersistentArray_foldlFromM___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_foldlFromM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_PersistentArray_foldlFromM___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_PersistentArray_foldlFromM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_foldlFromM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_forMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_PersistentArray_forMAux___main___rarg___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_forMAux___main___rarg(x_1, lean_box(0), lean_box(0), x_6, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_forMAux___main___rarg(x_1, lean_box(0), lean_box(0), x_3, x_9, x_10);
return x_11;
}
}
}
lean_object* l_PersistentArray_forMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_forMAux___main___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_PersistentArray_forMAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_forMAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_PersistentArray_forMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_forMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_forMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_forMAux___main___rarg(x_1, lean_box(0), x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentArray_forMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_forMAux___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_PersistentArray_forMAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_forMAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_PersistentArray_forMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_forMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_1);
x_8 = l_PersistentArray_forMAux___main___rarg(x_1, lean_box(0), x_4, x_7);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_forMAux___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_9, x_10);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
lean_object* l_PersistentArray_forM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_forM___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_PersistentArray_forM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_forM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentArray_forM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_forM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = l_PersistentArray_foldlMAux___main___at_PersistentArray_foldl___spec__2___rarg(x_1, x_8, x_5);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__3___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_5, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__4___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_foldl___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__3___rarg(x_1, x_4, x_4, x_5, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__4___rarg(x_1, x_7, x_7, x_8, x_3);
return x_9;
}
}
}
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_foldl___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_foldlMAux___main___at_PersistentArray_foldl___spec__2___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_5, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__5___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_PersistentArray_foldlM___at_PersistentArray_foldl___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_5 = l_PersistentArray_foldlMAux___main___at_PersistentArray_foldl___spec__2___rarg(x_1, x_4, x_3);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__5___rarg(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
lean_object* l_PersistentArray_foldlM___at_PersistentArray_foldl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_foldlM___at_PersistentArray_foldl___spec__1___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_PersistentArray_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_foldlM___at_PersistentArray_foldl___spec__1___rarg(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_PersistentArray_foldl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_foldl___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_foldl___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_foldlMAux___main___at_PersistentArray_foldl___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_PersistentArray_foldl___spec__5___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_PersistentArray_foldlM___at_PersistentArray_foldl___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_foldlM___at_PersistentArray_foldl___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_PersistentArray_foldl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_foldl___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_8 = l_PersistentArray_findMAux___main___at_PersistentArray_find___spec__2___rarg(x_1, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
}
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findMAux___main___at_PersistentArray_find___spec__3___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_1(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
}
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findMAux___main___at_PersistentArray_find___spec__4___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_PersistentArray_findMAux___main___at_PersistentArray_find___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_findMAux___main___at_PersistentArray_find___spec__3___rarg(x_1, x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_findMAux___main___at_PersistentArray_find___spec__4___rarg(x_1, x_6, x_7);
return x_8;
}
}
}
lean_object* l_PersistentArray_findMAux___main___at_PersistentArray_find___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_findMAux___main___at_PersistentArray_find___spec__2___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_1(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
}
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findMAux___main___at_PersistentArray_find___spec__5___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_PersistentArray_findM___at_PersistentArray_find___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_4 = l_PersistentArray_findMAux___main___at_PersistentArray_find___spec__2___rarg(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_findMAux___main___at_PersistentArray_find___spec__5___rarg(x_1, x_5, x_6);
return x_7;
}
else
{
lean_dec(x_1);
return x_4;
}
}
}
lean_object* l_PersistentArray_findM___at_PersistentArray_find___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_findM___at_PersistentArray_find___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_PersistentArray_find___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_findM___at_PersistentArray_find___spec__1___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_PersistentArray_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_find___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findMAux___main___at_PersistentArray_find___spec__3___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findMAux___main___at_PersistentArray_find___spec__4___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_PersistentArray_findMAux___main___at_PersistentArray_find___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_findMAux___main___at_PersistentArray_find___spec__2___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_findMAux___main___at_PersistentArray_find___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findMAux___main___at_PersistentArray_find___spec__5___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_PersistentArray_findM___at_PersistentArray_find___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_findM___at_PersistentArray_find___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_find___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_find___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_array_fget(x_2, x_9);
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
x_3 = x_9;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_1);
return x_11;
}
}
}
}
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__2___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_array_fget(x_2, x_9);
lean_inc(x_1);
x_11 = l_PersistentArray_findRevMAux___main___at_PersistentArray_findRev___spec__3___rarg(x_1, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
x_3 = x_9;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_1);
return x_11;
}
}
}
}
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__4___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_3);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_array_fget(x_2, x_9);
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
x_3 = x_9;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_1);
return x_11;
}
}
}
}
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__5___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_PersistentArray_findRevMAux___main___at_PersistentArray_findRev___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__4___rarg(x_1, x_3, x_4, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_array_get_size(x_6);
x_8 = l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__5___rarg(x_1, x_6, x_7, lean_box(0));
return x_8;
}
}
}
lean_object* l_PersistentArray_findRevMAux___main___at_PersistentArray_findRev___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_findRevMAux___main___at_PersistentArray_findRev___spec__3___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_PersistentArray_findRevM___at_PersistentArray_findRev___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_array_get_size(x_3);
lean_inc(x_1);
x_5 = l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__2___rarg(x_1, x_3, x_4, lean_box(0));
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_PersistentArray_findRevMAux___main___at_PersistentArray_findRev___spec__3___rarg(x_1, x_6);
return x_7;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_PersistentArray_findRevM___at_PersistentArray_findRev___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_findRevM___at_PersistentArray_findRev___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_PersistentArray_findRev___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_findRevM___at_PersistentArray_findRev___spec__1___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_PersistentArray_findRev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_findRev___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__4___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findRevMAux___main___at_PersistentArray_findRev___spec__5___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_PersistentArray_findRevMAux___main___at_PersistentArray_findRev___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_findRevMAux___main___at_PersistentArray_findRev___spec__3___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_findRevM___at_PersistentArray_findRev___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_findRevM___at_PersistentArray_findRev___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_findRev___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_findRev___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = l_PersistentArray_foldlMAux___main___at_PersistentArray_foldlFrom___spec__3___rarg(x_1, x_8, x_5);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__4___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_5, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__5___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_foldlFrom___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__4___rarg(x_1, x_4, x_4, x_5, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__5___rarg(x_1, x_7, x_7, x_8, x_3);
return x_9;
}
}
}
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_foldlFrom___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_foldlMAux___main___at_PersistentArray_foldlFrom___spec__3___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = l_PersistentArray_foldlMAux___main___at_PersistentArray_foldlFrom___spec__3___rarg(x_1, x_8, x_5);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__6___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_5, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__7___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_PersistentArray_foldlFromMAux___main___at_PersistentArray_foldlFrom___spec__2___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = x_3 >> x_4;
x_8 = lean_usize_to_nat(x_7);
x_9 = l_PersistentArray_getAux___main___rarg___closed__1;
x_10 = lean_array_get(x_9, x_6, x_8);
x_11 = 1;
x_12 = x_11 << x_4;
x_13 = x_12 - x_11;
x_14 = x_3 & x_13;
x_15 = 5;
x_16 = x_4 - x_15;
lean_inc(x_1);
x_17 = l_PersistentArray_foldlFromMAux___main___at_PersistentArray_foldlFrom___spec__2___rarg(x_1, x_10, x_14, x_16, x_5);
lean_dec(x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_8, x_18);
lean_dec(x_8);
x_20 = l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__6___rarg(x_1, x_6, x_6, x_19, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_usize_to_nat(x_3);
x_23 = l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__7___rarg(x_1, x_21, x_21, x_22, x_5);
return x_23;
}
}
}
lean_object* l_PersistentArray_foldlFromMAux___main___at_PersistentArray_foldlFrom___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_foldlFromMAux___main___at_PersistentArray_foldlFrom___spec__2___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_2);
x_9 = lean_apply_2(x_2, x_5, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__8___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_2);
x_9 = lean_apply_2(x_2, x_5, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__9___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_PersistentArray_foldlFromM___at_PersistentArray_foldlFrom___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_nat_dec_le(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_usize_of_nat(x_4);
x_9 = lean_ctor_get_usize(x_1, 4);
lean_inc(x_2);
x_10 = l_PersistentArray_foldlFromMAux___main___at_PersistentArray_foldlFrom___spec__2___rarg(x_2, x_7, x_8, x_9, x_3);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__8___rarg(x_1, x_2, x_11, x_12, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_nat_sub(x_4, x_5);
x_16 = l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__9___rarg(x_1, x_2, x_14, x_15, x_3);
return x_16;
}
}
}
lean_object* l_PersistentArray_foldlFromM___at_PersistentArray_foldlFrom___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_foldlFromM___at_PersistentArray_foldlFrom___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_PersistentArray_foldlFrom___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_foldlFromM___at_PersistentArray_foldlFrom___spec__1___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentArray_foldlFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_foldlFrom___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__5___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_foldlFrom___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_foldlMAux___main___at_PersistentArray_foldlFrom___spec__3___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__6___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__7___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_PersistentArray_foldlFromMAux___main___at_PersistentArray_foldlFrom___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_PersistentArray_foldlFromMAux___main___at_PersistentArray_foldlFrom___spec__2___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__8___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_PersistentArray_foldlFrom___spec__9___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentArray_foldlFromM___at_PersistentArray_foldlFrom___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_foldlFromM___at_PersistentArray_foldlFrom___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentArray_foldlFrom___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_foldlFrom___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_PersistentArray_foldlMAux___main___at_PersistentArray_toList___spec__2___rarg(x_7, x_4);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_toList___spec__3___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_toList___spec__4___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_toList___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_iterateMAux___main___at_PersistentArray_toList___spec__3___rarg(x_3, x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___main___at_PersistentArray_toList___spec__4___rarg(x_6, x_6, x_7, x_2);
return x_8;
}
}
}
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_toList___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_foldlMAux___main___at_PersistentArray_toList___spec__2___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_toList___spec__5___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_PersistentArray_foldlM___at_PersistentArray_toList___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_PersistentArray_foldlMAux___main___at_PersistentArray_toList___spec__2___rarg(x_3, x_2);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_iterateMAux___main___at_PersistentArray_toList___spec__5___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_PersistentArray_foldlM___at_PersistentArray_toList___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_foldlM___at_PersistentArray_toList___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_PersistentArray_toList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_PersistentArray_foldlM___at_PersistentArray_toList___spec__1___rarg(x_1, x_2);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
}
lean_object* l_PersistentArray_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_toList___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_PersistentArray_toList___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_PersistentArray_toList___spec__4___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentArray_foldlMAux___main___at_PersistentArray_toList___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_foldlMAux___main___at_PersistentArray_toList___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_toList___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_PersistentArray_toList___spec__5___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentArray_foldlM___at_PersistentArray_toList___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_foldlM___at_PersistentArray_toList___spec__1___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_PersistentArray_toList___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PersistentArray_toList___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_PersistentArray_anyMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_PersistentArray_anyMAux___main___rarg), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyMAux___main___rarg(x_1, x_4, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyMAux___main___rarg(x_1, x_8, x_2, x_9);
return x_10;
}
}
}
lean_object* l_PersistentArray_anyMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_anyMAux___main___rarg), 3, 0);
return x_3;
}
}
lean_object* l_PersistentArray_anyMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_anyMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_anyMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_anyMAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_PersistentArray_anyMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_anyMAux___rarg), 3, 0);
return x_3;
}
}
lean_object* l_PersistentArray_anyMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_anyMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_anyM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyMAux___main___rarg(x_2, x_5, x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(x_4);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
}
}
lean_object* l_PersistentArray_anyM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_PersistentArray_anyMAux___main___rarg(x_1, x_3, x_5);
x_7 = lean_alloc_closure((void*)(l_PersistentArray_anyM___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_PersistentArray_anyM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_anyM___rarg), 3, 0);
return x_3;
}
}
lean_object* l_PersistentArray_anyM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_PersistentArray_anyM___rarg___lambda__1(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l_PersistentArray_anyM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_anyM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = l_Array_anyMAux___main___at_PersistentArray_allM___spec__3___rarg(x_2, x_3, x_4, x_5, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(x_6);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
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
x_14 = lean_array_fget(x_4, x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_PersistentArray_anyMAux___main___at_PersistentArray_allM___spec__2___rarg(x_1, x_2, x_3, x_14);
x_16 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_PersistentArray_allM___spec__3___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_16, 0, x_5);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_4);
x_17 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_PersistentArray_allM___spec__3___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg___lambda__1(lean_object* x_1, uint8_t x_2) {
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
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg(x_2, x_3, x_4, x_5, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(x_6);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_fget(x_4, x_5);
lean_inc(x_2);
x_15 = lean_apply_1(x_2, x_14);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_16, 0, x_1);
lean_inc(x_3);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_15, x_16);
x_18 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_18, 0, x_5);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_4);
x_19 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg), 5, 0);
return x_3;
}
}
lean_object* l_PersistentArray_anyMAux___main___at_PersistentArray_allM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyMAux___main___at_PersistentArray_allM___spec__3___rarg(x_1, x_2, x_3, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg(x_1, x_2, x_3, x_8, x_9);
return x_10;
}
}
}
lean_object* l_PersistentArray_anyMAux___main___at_PersistentArray_allM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_anyMAux___main___at_PersistentArray_allM___spec__2___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = l_Array_anyMAux___main___at_PersistentArray_allM___spec__5___rarg(x_2, x_3, x_4, x_5, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(x_6);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_fget(x_4, x_5);
lean_inc(x_2);
x_15 = lean_apply_1(x_2, x_14);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_16, 0, x_1);
lean_inc(x_3);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_15, x_16);
x_18 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_PersistentArray_allM___spec__5___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_18, 0, x_5);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_4);
x_19 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_PersistentArray_allM___spec__5___rarg), 5, 0);
return x_3;
}
}
lean_object* l_PersistentArray_anyM___at_PersistentArray_allM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyMAux___main___at_PersistentArray_allM___spec__5___rarg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(x_5);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
}
}
lean_object* l_PersistentArray_anyM___at_PersistentArray_allM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_PersistentArray_anyMAux___main___at_PersistentArray_allM___spec__2___rarg(x_1, x_2, x_3, x_6);
x_8 = lean_alloc_closure((void*)(l_PersistentArray_anyM___at_PersistentArray_allM___spec__1___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_PersistentArray_anyM___at_PersistentArray_allM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_anyM___at_PersistentArray_allM___spec__1___rarg), 4, 0);
return x_3;
}
}
lean_object* l_PersistentArray_allM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_4);
lean_inc(x_1);
x_5 = l_PersistentArray_anyM___at_PersistentArray_allM___spec__1___rarg(x_1, x_3, x_4, x_2);
x_6 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_PersistentArray_allM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_allM___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__3___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Array_anyMAux___main___at_PersistentArray_allM___spec__3___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_anyMAux___main___at_PersistentArray_allM___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg___lambda__1(x_1, x_3);
return x_4;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_anyMAux___main___at_PersistentArray_allM___spec__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_anyMAux___main___at_PersistentArray_allM___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_anyMAux___main___at_PersistentArray_allM___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__5___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Array_anyMAux___main___at_PersistentArray_allM___spec__5___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_allM___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_anyMAux___main___at_PersistentArray_allM___spec__5(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_anyM___at_PersistentArray_allM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_PersistentArray_anyM___at_PersistentArray_allM___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
lean_object* l_PersistentArray_anyM___at_PersistentArray_allM___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_anyM___at_PersistentArray_allM___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_allM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_allM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_Array_anyMAux___main___at_PersistentArray_any___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_8 = l_PersistentArray_anyMAux___main___at_PersistentArray_any___spec__2___rarg(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_any___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_PersistentArray_any___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
uint8_t l_Array_anyMAux___main___at_PersistentArray_any___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = 0;
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
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_any___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_PersistentArray_any___spec__4___rarg___boxed), 3, 0);
return x_2;
}
}
uint8_t l_PersistentArray_anyMAux___main___at_PersistentArray_any___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyMAux___main___at_PersistentArray_any___spec__3___rarg(x_1, x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyMAux___main___at_PersistentArray_any___spec__4___rarg(x_1, x_6, x_7);
return x_8;
}
}
}
lean_object* l_PersistentArray_anyMAux___main___at_PersistentArray_any___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_anyMAux___main___at_PersistentArray_any___spec__2___rarg___boxed), 2, 0);
return x_2;
}
}
uint8_t l_Array_anyMAux___main___at_PersistentArray_any___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = 0;
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
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_any___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_PersistentArray_any___spec__5___rarg___boxed), 3, 0);
return x_2;
}
}
uint8_t l_PersistentArray_anyM___at_PersistentArray_any___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_4 = l_PersistentArray_anyMAux___main___at_PersistentArray_any___spec__2___rarg(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyMAux___main___at_PersistentArray_any___spec__5___rarg(x_1, x_5, x_6);
return x_7;
}
else
{
lean_dec(x_1);
return x_4;
}
}
}
lean_object* l_PersistentArray_anyM___at_PersistentArray_any___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_anyM___at_PersistentArray_any___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
uint8_t l_PersistentArray_any___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_PersistentArray_anyM___at_PersistentArray_any___spec__1___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_PersistentArray_any(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_any___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_any___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_PersistentArray_any___spec__3___rarg(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_any___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_PersistentArray_any___spec__4___rarg(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_PersistentArray_anyMAux___main___at_PersistentArray_any___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyMAux___main___at_PersistentArray_any___spec__2___rarg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_any___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_PersistentArray_any___spec__5___rarg(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_PersistentArray_anyM___at_PersistentArray_any___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyM___at_PersistentArray_any___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_PersistentArray_any___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_any___rarg(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Array_anyMAux___main___at_PersistentArray_all___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_8 = l_PersistentArray_anyMAux___main___at_PersistentArray_all___spec__2___rarg(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_all___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_PersistentArray_all___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
uint8_t l_Array_anyMAux___main___at_PersistentArray_all___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = 0;
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
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = 1;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
}
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_all___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_PersistentArray_all___spec__4___rarg___boxed), 3, 0);
return x_2;
}
}
uint8_t l_PersistentArray_anyMAux___main___at_PersistentArray_all___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyMAux___main___at_PersistentArray_all___spec__3___rarg(x_1, x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyMAux___main___at_PersistentArray_all___spec__4___rarg(x_1, x_6, x_7);
return x_8;
}
}
}
lean_object* l_PersistentArray_anyMAux___main___at_PersistentArray_all___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_anyMAux___main___at_PersistentArray_all___spec__2___rarg___boxed), 2, 0);
return x_2;
}
}
uint8_t l_Array_anyMAux___main___at_PersistentArray_all___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = 0;
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
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = 1;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
}
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_all___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_PersistentArray_all___spec__5___rarg___boxed), 3, 0);
return x_2;
}
}
uint8_t l_PersistentArray_anyM___at_PersistentArray_all___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_4 = l_PersistentArray_anyMAux___main___at_PersistentArray_all___spec__2___rarg(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyMAux___main___at_PersistentArray_all___spec__5___rarg(x_1, x_5, x_6);
return x_7;
}
else
{
lean_dec(x_1);
return x_4;
}
}
}
lean_object* l_PersistentArray_anyM___at_PersistentArray_all___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_anyM___at_PersistentArray_all___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
uint8_t l_PersistentArray_all___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_PersistentArray_anyM___at_PersistentArray_all___spec__1___rarg(x_2, x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
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
lean_object* l_PersistentArray_all(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_all___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_all___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_PersistentArray_all___spec__3___rarg(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_all___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_PersistentArray_all___spec__4___rarg(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_PersistentArray_anyMAux___main___at_PersistentArray_all___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyMAux___main___at_PersistentArray_all___spec__2___rarg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyMAux___main___at_PersistentArray_all___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_PersistentArray_all___spec__5___rarg(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_PersistentArray_anyM___at_PersistentArray_all___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyM___at_PersistentArray_all___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_PersistentArray_all___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_all___rarg(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_PersistentArray_mapMAux___main___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_PersistentArray_mapMAux___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_mapMAux___main___rarg(x_1, lean_box(0), x_2, x_4);
return x_5;
}
}
lean_object* l_PersistentArray_mapMAux___main___rarg___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_PersistentArray_mapMAux___main___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
lean_object* _init_l_PersistentArray_mapMAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_PersistentArray_mapMAux___main___rarg___lambda__1), 1, 0);
return x_1;
}
}
lean_object* _init_l_PersistentArray_mapMAux___main___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_PersistentArray_mapMAux___main___rarg___lambda__3), 1, 0);
return x_1;
}
}
lean_object* l_PersistentArray_mapMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_PersistentArray_mapMAux___main___rarg___lambda__2___boxed), 4, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_umapMAux___main___rarg(x_1, lean_box(0), x_9, x_10, x_5);
x_12 = l_PersistentArray_mapMAux___main___rarg___closed__1;
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_closure((void*)(l_PersistentArray_mapMAux___main___rarg___lambda__4___boxed), 3, 1);
lean_closure_set(x_18, 0, x_3);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_umapMAux___main___rarg(x_1, lean_box(0), x_18, x_19, x_14);
x_21 = l_PersistentArray_mapMAux___main___rarg___closed__2;
x_22 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_21, x_20);
return x_22;
}
}
}
lean_object* l_PersistentArray_mapMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_mapMAux___main___rarg), 4, 0);
return x_3;
}
}
lean_object* l_PersistentArray_mapMAux___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_mapMAux___main___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentArray_mapMAux___main___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_mapMAux___main___rarg___lambda__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_PersistentArray_mapMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_mapMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_mapMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_mapMAux___main___rarg(x_1, lean_box(0), x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentArray_mapMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_mapMAux___rarg), 4, 0);
return x_3;
}
}
lean_object* l_PersistentArray_mapMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_mapMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_PersistentArray_mapM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get_usize(x_2, 4);
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
lean_inc(x_7);
x_10 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set_usize(x_10, 4, x_8);
x_11 = lean_apply_2(x_6, lean_box(0), x_10);
return x_11;
}
}
lean_object* l_PersistentArray_mapM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_PersistentArray_mapMAux___main___rarg___lambda__4___boxed), 3, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_9 = l_Array_umapMAux___main___rarg(x_3, lean_box(0), x_7, x_8, x_6);
x_10 = lean_alloc_closure((void*)(l_PersistentArray_mapM___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_5);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_PersistentArray_mapM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_1);
x_7 = l_PersistentArray_mapMAux___main___rarg(x_1, lean_box(0), x_3, x_6);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_PersistentArray_mapM___rarg___lambda__2), 5, 4);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_1);
lean_closure_set(x_8, 3, x_5);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_PersistentArray_mapM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_mapM___rarg), 4, 0);
return x_3;
}
}
lean_object* l_PersistentArray_mapM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_mapM___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_PersistentArray_mapM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_mapM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_PersistentArray_map___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_8);
lean_inc(x_1);
x_12 = l_PersistentArray_mapMAux___main___at_PersistentArray_map___spec__2___rarg(x_1, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_PersistentArray_map___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_PersistentArray_map___spec__3___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_PersistentArray_map___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_1);
lean_inc(x_8);
x_12 = lean_apply_1(x_1, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_PersistentArray_map___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_PersistentArray_map___spec__4___rarg), 3, 0);
return x_3;
}
}
lean_object* l_PersistentArray_mapMAux___main___at_PersistentArray_map___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___at_PersistentArray_map___spec__3___rarg(x_1, x_5, x_4);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_umapMAux___main___at_PersistentArray_map___spec__3___rarg(x_1, x_8, x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_umapMAux___main___at_PersistentArray_map___spec__4___rarg(x_1, x_13, x_12);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_umapMAux___main___at_PersistentArray_map___spec__4___rarg(x_1, x_16, x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
lean_object* l_PersistentArray_mapMAux___main___at_PersistentArray_map___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_mapMAux___main___at_PersistentArray_map___spec__2___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_PersistentArray_map___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_1);
lean_inc(x_8);
x_12 = lean_apply_1(x_1, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_PersistentArray_map___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_PersistentArray_map___spec__5___rarg), 3, 0);
return x_3;
}
}
lean_object* l_PersistentArray_mapM___at_PersistentArray_map___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_6 = l_PersistentArray_mapMAux___main___at_PersistentArray_map___spec__2___rarg(x_1, x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_umapMAux___main___at_PersistentArray_map___spec__5___rarg(x_1, x_7, x_5);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get_usize(x_2, 4);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_14 = l_PersistentArray_mapMAux___main___at_PersistentArray_map___spec__2___rarg(x_1, x_9);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_umapMAux___main___at_PersistentArray_map___spec__5___rarg(x_1, x_15, x_10);
x_17 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set_usize(x_17, 4, x_12);
return x_17;
}
}
}
lean_object* l_PersistentArray_mapM___at_PersistentArray_map___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_mapM___at_PersistentArray_map___spec__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l_PersistentArray_map___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentArray_mapM___at_PersistentArray_map___spec__1___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_PersistentArray_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentArray_map___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_collectStats___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = l_PersistentArray_collectStats___main___rarg(x_8, x_5, x_10);
lean_dec(x_10);
lean_dec(x_8);
x_12 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_4 = x_12;
x_5 = x_11;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_collectStats___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentArray_collectStats___main___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_PersistentArray_collectStats___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_10 = l_Nat_max(x_3, x_7);
lean_dec(x_7);
lean_ctor_set(x_2, 1, x_10);
lean_ctor_set(x_2, 0, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateMAux___main___at_PersistentArray_collectStats___main___spec__1___rarg(x_3, x_5, x_5, x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_14, x_17);
lean_dec(x_14);
x_19 = l_Nat_max(x_3, x_15);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_16);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Array_iterateMAux___main___at_PersistentArray_collectStats___main___spec__1___rarg(x_3, x_13, x_13, x_21, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_24, x_26);
lean_dec(x_24);
x_28 = l_Nat_max(x_3, x_25);
lean_dec(x_25);
lean_ctor_set(x_2, 1, x_28);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_29, x_32);
lean_dec(x_29);
x_34 = l_Nat_max(x_3, x_30);
lean_dec(x_30);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_31);
return x_35;
}
}
}
}
lean_object* l_PersistentArray_collectStats___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_collectStats___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentArray_collectStats___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_PersistentArray_collectStats___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentArray_collectStats___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_collectStats___main___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_PersistentArray_collectStats___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_collectStats___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_PersistentArray_collectStats(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_collectStats___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_PersistentArray_collectStats___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_collectStats___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_PersistentArray_stats___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_4);
x_7 = l_PersistentArray_collectStats___main___rarg(x_2, x_6, x_5);
return x_7;
}
}
lean_object* l_PersistentArray_stats(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_stats___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_PersistentArray_stats___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PersistentArray_stats___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_PersistentArray_Stats_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("{nodes := ");
return x_1;
}
}
lean_object* _init_l_PersistentArray_Stats_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", depth := ");
return x_1;
}
}
lean_object* _init_l_PersistentArray_Stats_toString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", tail size := ");
return x_1;
}
}
lean_object* _init_l_PersistentArray_Stats_toString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("}");
return x_1;
}
}
lean_object* l_PersistentArray_Stats_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Nat_repr(x_2);
x_4 = l_PersistentArray_Stats_toString___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_PersistentArray_Stats_toString___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Nat_repr(x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec(x_9);
x_11 = l_PersistentArray_Stats_toString___closed__3;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Nat_repr(x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec(x_14);
x_16 = l_PersistentArray_Stats_toString___closed__4;
x_17 = lean_string_append(x_15, x_16);
return x_17;
}
}
lean_object* _init_l_PersistentArray_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_PersistentArray_Stats_toString), 1, 0);
return x_1;
}
}
lean_object* _init_l_PersistentArray_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_PersistentArray_HasToString___closed__1;
return x_1;
}
}
lean_object* l_List_toPersistentArrayAux___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_PersistentArray_push___rarg(x_2, x_3);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
}
}
lean_object* l_List_toPersistentArrayAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toPersistentArrayAux___main___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_toPersistentArrayAux___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_toPersistentArrayAux___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_toPersistentArrayAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toPersistentArrayAux___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_toPersistentArray___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_PersistentArray_empty___closed__3;
x_3 = l_List_toPersistentArrayAux___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_toPersistentArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toPersistentArray___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_toPersistentArray___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_PersistentArray_push___rarg(x_4, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Array_toPersistentArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_toPersistentArray___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* _init_l_Array_toPersistentArray___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_PersistentArray_empty(lean_box(0));
return x_1;
}
}
lean_object* l_Array_toPersistentArray___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_toPersistentArray___rarg___closed__1;
x_4 = l_Array_iterateMAux___main___at_Array_toPersistentArray___spec__1___rarg(x_1, x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_toPersistentArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_toPersistentArray___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_toPersistentArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Array_toPersistentArray___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_toPersistentArray___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_toPersistentArray___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_toPArray___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_toPersistentArray___rarg(x_1);
return x_2;
}
}
lean_object* l_Array_toPArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_toPArray___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Array_toPArray___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_toPArray___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_foldAux___main___at_mkPersistentArray___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
lean_inc(x_1);
x_9 = l_PersistentArray_push___rarg(x_4, x_1);
x_3 = x_8;
x_4 = x_9;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
}
lean_object* l_Nat_foldAux___main___at_mkPersistentArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Nat_foldAux___main___at_mkPersistentArray___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_mkPersistentArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Array_toPersistentArray___rarg___closed__1;
lean_inc(x_1);
x_4 = l_Nat_foldAux___main___at_mkPersistentArray___spec__1___rarg(x_2, x_1, x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_mkPersistentArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_mkPersistentArray___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Nat_foldAux___main___at_mkPersistentArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Nat_foldAux___main___at_mkPersistentArray___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_mkPArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_mkPersistentArray___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_mkPArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_mkPArray___rarg), 2, 0);
return x_2;
}
}
lean_object* initialize_Init_Control_Conditional(lean_object*);
lean_object* initialize_Init_Data_Array_Default(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_PersistentArray_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Conditional(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Default(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PersistentArrayNode_Inhabited___closed__1 = _init_l_PersistentArrayNode_Inhabited___closed__1();
lean_mark_persistent(l_PersistentArrayNode_Inhabited___closed__1);
l_PersistentArray_initShift = _init_l_PersistentArray_initShift();
l_PersistentArray_branching = _init_l_PersistentArray_branching();
l_PersistentArray_empty___closed__1 = _init_l_PersistentArray_empty___closed__1();
lean_mark_persistent(l_PersistentArray_empty___closed__1);
l_PersistentArray_empty___closed__2 = _init_l_PersistentArray_empty___closed__2();
lean_mark_persistent(l_PersistentArray_empty___closed__2);
l_PersistentArray_empty___closed__3 = _init_l_PersistentArray_empty___closed__3();
lean_mark_persistent(l_PersistentArray_empty___closed__3);
l_PersistentArray_getAux___main___rarg___closed__1 = _init_l_PersistentArray_getAux___main___rarg___closed__1();
lean_mark_persistent(l_PersistentArray_getAux___main___rarg___closed__1);
l_PersistentArray_tooBig___closed__1 = _init_l_PersistentArray_tooBig___closed__1();
lean_mark_persistent(l_PersistentArray_tooBig___closed__1);
l_PersistentArray_tooBig = _init_l_PersistentArray_tooBig();
lean_mark_persistent(l_PersistentArray_tooBig);
l_PersistentArray_popLeaf___main___rarg___closed__1 = _init_l_PersistentArray_popLeaf___main___rarg___closed__1();
lean_mark_persistent(l_PersistentArray_popLeaf___main___rarg___closed__1);
l_PersistentArray_mapMAux___main___rarg___closed__1 = _init_l_PersistentArray_mapMAux___main___rarg___closed__1();
lean_mark_persistent(l_PersistentArray_mapMAux___main___rarg___closed__1);
l_PersistentArray_mapMAux___main___rarg___closed__2 = _init_l_PersistentArray_mapMAux___main___rarg___closed__2();
lean_mark_persistent(l_PersistentArray_mapMAux___main___rarg___closed__2);
l_PersistentArray_Stats_toString___closed__1 = _init_l_PersistentArray_Stats_toString___closed__1();
lean_mark_persistent(l_PersistentArray_Stats_toString___closed__1);
l_PersistentArray_Stats_toString___closed__2 = _init_l_PersistentArray_Stats_toString___closed__2();
lean_mark_persistent(l_PersistentArray_Stats_toString___closed__2);
l_PersistentArray_Stats_toString___closed__3 = _init_l_PersistentArray_Stats_toString___closed__3();
lean_mark_persistent(l_PersistentArray_Stats_toString___closed__3);
l_PersistentArray_Stats_toString___closed__4 = _init_l_PersistentArray_Stats_toString___closed__4();
lean_mark_persistent(l_PersistentArray_Stats_toString___closed__4);
l_PersistentArray_HasToString___closed__1 = _init_l_PersistentArray_HasToString___closed__1();
lean_mark_persistent(l_PersistentArray_HasToString___closed__1);
l_PersistentArray_HasToString = _init_l_PersistentArray_HasToString();
lean_mark_persistent(l_PersistentArray_HasToString);
l_Array_toPersistentArray___rarg___closed__1 = _init_l_Array_toPersistentArray___rarg___closed__1();
lean_mark_persistent(l_Array_toPersistentArray___rarg___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
