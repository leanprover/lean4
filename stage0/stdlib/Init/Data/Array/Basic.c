// Lean compiler output
// Module: Init.Data.Array.Basic
// Imports: Init.Data.Nat.Basic Init.Data.Fin.Basic Init.Data.UInt Init.Data.Repr Init.Data.ToString Init.Control.Id Init.Util
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
lean_object* l_Array_getD(lean_object*);
lean_object* l_Array_forM(lean_object*);
lean_object* l_Array_foldlM_u2082___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findM_x3f(lean_object*, lean_object*);
lean_object* l_List_repr___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyRangeM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldl_u2082___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main(lean_object*, lean_object*);
lean_object* l_Array_iterate_u2082(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extractAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_HasBeq(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Array_swapAt_x21___spec__1(lean_object*);
lean_object* l_Array_forRevM___boxed(lean_object*);
lean_object* l_Array_forMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyFrom___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_getD___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_iterateFrom___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_forM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_iterateFrom___spec__1(lean_object*, lean_object*);
lean_object* l_Array_mkArray___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2(lean_object*, lean_object*);
lean_object* l_Array_mapIdxM(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_anyRange___spec__2(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_foldlM___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_umapIdxM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_iterate___spec__1(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_foldlM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__1(lean_object*);
lean_object* l_Array_modifyM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_mapIdxM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main(lean_object*);
lean_object* l_Array_forMAux___main___boxed(lean_object*);
lean_object* l_List_redLength___rarg___boxed(lean_object*);
lean_object* l_List_redLength___main(lean_object*);
lean_object* l_Array_forRevMAux___boxed(lean_object*);
lean_object* l_Array_uset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Array_allRange___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extractAux(lean_object*);
lean_object* l_Array_anyM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_HasToString___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_swapAt(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_foldlFromM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Array_umapM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filter(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldr___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__3;
lean_object* l_Array_insertAtAux___main(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_foldlM_u2082___spec__1(lean_object*, lean_object*);
lean_object* l_Array_empty___closed__1;
lean_object* l_Array_modifyM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdxSzAuxInstance___rarg(lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_uget___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_foldlFrom___spec__1(lean_object*, lean_object*);
lean_object* l_Array_foldlFrom(lean_object*, lean_object*);
lean_object* l_Array_foldl___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_allRange(lean_object*);
lean_object* l_Array_isEqvAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_all___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyM(lean_object*, lean_object*);
lean_object* l_Array_reverseAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_all(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Array_all___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverseAux(lean_object*);
lean_object* l_Array_foldl_u2082___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_Array_findRev_x3f___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_umapM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_map___rarg(lean_object*, lean_object*);
lean_object* l_Array_findRevMAux(lean_object*, lean_object*);
lean_object* l_Array_findRev_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Array_anyRange___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___boxed(lean_object*, lean_object*);
lean_object* l_Array_forM___boxed(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_any___spec__1(lean_object*);
lean_object* l_Array_isEqvAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Array_find_x3f___rarg(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Array_allRange___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back(lean_object*);
lean_object* l_Array_findM_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlFromM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArray___rarg(lean_object*);
lean_object* l_Array_modifyM___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRange___spec__2(lean_object*);
uint8_t l_Array_allRange___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_singleton(lean_object*);
lean_object* l_Array_find_x3f(lean_object*, lean_object*);
lean_object* l_Array_foldlM_u2082(lean_object*, lean_object*);
lean_object* l_Array_foldlFrom___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapM(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRange___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyFrom___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_allM(lean_object*, lean_object*);
lean_object* l_Array_get___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_foldlM_u2082___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_iterateFrom___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_iterateRev___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isEqvAux(lean_object*);
lean_object* l_Array_findRevMAux___boxed(lean_object*, lean_object*);
lean_object* l_Array_eraseIdxSzAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRange___spec__1(lean_object*);
lean_object* l_List_redLength___main___rarg___boxed(lean_object*);
lean_object* l_Array_anyRange(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_contains___spec__1(lean_object*);
lean_object* l_Array_mapIdx___rarg(lean_object*, lean_object*);
lean_object* l_Array_swap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_swap_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlM(lean_object*, lean_object*);
lean_object* l_Array_foldrM(lean_object*, lean_object*);
lean_object* l_Array_extractAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterate_u2082___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdxAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_Array_find_x21___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldr___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdx(lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___main(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_foldlFrom___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_HasRepr___rarg___closed__1;
uint8_t l_Array_anyRange___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_HasAppend___closed__1;
lean_object* l_Array_foldl(lean_object*, lean_object*);
lean_object* l_Array_findIdx_x21___rarg(lean_object*, lean_object*);
lean_object* l_Array_isEqv(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Array_map___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAtAux___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_push___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forRevMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_HasRepr___rarg___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_HasToString___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_Array_findRev_x21___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapIdxM___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Array_mapIdx___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_iterateRev___spec__1(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_toList___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_extract___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1(lean_object*);
uint8_t l_Array_all___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allM___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx_x27___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Array_any___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_get_x3f___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_mapM___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_mapM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlM_u2082___boxed(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_findRev_x3f(lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOf(lean_object*);
lean_object* l_Array_findMAux___main___at_Array_find_x21___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux(lean_object*, lean_object*);
lean_object* l_Array_iterateFrom___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_any___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_allM___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_pop___boxed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_map(lean_object*, lean_object*);
lean_object* l_Array_forMAux___boxed(lean_object*);
lean_object* l_Array_singleton___rarg(lean_object*);
lean_object* l_Array_indexOf___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_foldlFromM___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_toList___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux(lean_object*, lean_object*);
lean_object* l_Array_append___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_feraseIdx(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldrM___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAtAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_allRange___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main(lean_object*, lean_object*);
lean_object* l_Array_insertAtAux(lean_object*);
lean_object* l_Array_anyRangeM___boxed(lean_object*, lean_object*);
lean_object* l_Array_reverse(lean_object*);
lean_object* l_Array_eraseIdxSzAux___main(lean_object*);
lean_object* l_Array_modifyM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx(lean_object*);
lean_object* l_Array_iterateM___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterate___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Array_anyRange___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_umapMAux___main___at_Array_mapIdx___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg___lambda__1(lean_object*, uint8_t);
lean_object* l_Array_iterateMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapM___boxed(lean_object*, lean_object*);
lean_object* l_Array_forRevMAux___main___boxed(lean_object*);
lean_object* l_Array_mkEmpty___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_anyRange___spec__1(lean_object*);
lean_object* l_Array_iterateM(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_iterate_u2082___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_foldlM_u2082___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_anyRange___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_foldl___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlFromM___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Array_umapM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allM___spec__1(lean_object*, lean_object*);
lean_object* l_Array_toList(lean_object*);
lean_object* l_Array_forRevMAux___main(lean_object*);
lean_object* l_Array_eraseIdxSzAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_sz(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_foldlM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdxSzAux(lean_object*);
lean_object* l_Array_getOp(lean_object*);
lean_object* l_Array_modify___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___rarg(lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg___lambda__1(lean_object*, uint8_t);
lean_object* l_Array_iterateRevM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_iterate___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOfAux(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_toList___spec__1(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_foldl_u2082___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*);
lean_object* l_Array_umapIdxM(lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_Array_find_x21___spec__1(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapM___boxed(lean_object*, lean_object*);
lean_object* l_Array_forMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevM_x3f(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_foldl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg___boxed(lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
lean_object* l_Array_findRev_x3f___rarg___boxed(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Array_any(lean_object*);
lean_object* l_Array_eraseIdxSzAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevM_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_HasBeq___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_swapAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_HasEmptyc(lean_object*);
lean_object* l_List_toArrayAux___main(lean_object*);
lean_object* l_Array_iterateM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldr___spec__1(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldr___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_find_x21___rarg___closed__2;
lean_object* l_Array_mapIdxM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forRevMAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux(lean_object*, lean_object*);
lean_object* l_Array_size___boxed(lean_object*, lean_object*);
lean_object* l_Array_extract(lean_object*);
lean_object* l_Array_eraseIdx_x27(lean_object*);
lean_object* l_Array_allM___boxed(lean_object*, lean_object*);
lean_object* l_Array_foldlFromM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateFrom___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082___boxed(lean_object*, lean_object*);
lean_object* l_List_toArrayAux(lean_object*);
lean_object* l_Array_umapMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg___closed__2;
lean_object* l_Array_findRev_x21(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Array_umapM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extractAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_swapAt___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_feraseIdx___rarg(lean_object*, lean_object*);
uint8_t l_Array_contains___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_find_x3f___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_getOp___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_data___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_getD___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_Array_findRev_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Array_foldrM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdxSzAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateRev___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg___closed__1;
lean_object* l_Array_findMAux___main(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_foldlFrom___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__2(lean_object*);
lean_object* l_Array_eraseIdxAux___main(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_foldlFromM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_Array_findRev_x21___spec__1(lean_object*, lean_object*);
lean_object* l_Array_allRangeM___boxed(lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_Array_find_x3f___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRange___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevM_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Array_HasRepr___rarg(lean_object*, lean_object*);
lean_object* l_Array_forRevM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_iterateRev___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg___boxed(lean_object*, lean_object*);
uint8_t l_Array_isEqv___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_foldl___spec__1(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*, lean_object*);
lean_object* l_Array_modify(lean_object*);
lean_object* l_List_toArray(lean_object*);
lean_object* l_Array_findMAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_allRangeM(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_extractAux___main(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_foldlM___spec__1(lean_object*, lean_object*);
lean_object* l_Array_modifyM(lean_object*, lean_object*);
lean_object* l_Array_iterateRevM(lean_object*, lean_object*);
uint8_t l_Array_HasBeq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink(lean_object*);
lean_object* l_Array_foldl_u2082(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isEmpty(lean_object*);
lean_object* l_Array_findMAux___main___at_Array_find_x3f___spec__1(lean_object*, lean_object*);
uint8_t l_Array_any___rarg(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Array_map___spec__1(lean_object*, lean_object*);
lean_object* l_Array_iterateRev___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldr___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlFrom___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forRevMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateRev(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_List_redLength(lean_object*);
lean_object* l_Array_findMAux___boxed(lean_object*, lean_object*);
lean_object* l_Array_findRev_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAtAux___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_find_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlM___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Array_swapAt_x21___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_find_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdxAux(lean_object*);
lean_object* l_Array_mapIdxM___boxed(lean_object*, lean_object*);
lean_object* l_Array_isEmpty___rarg___boxed(lean_object*);
lean_object* l_Array_iterateRevM___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_all___spec__1(lean_object*);
lean_object* l_Array_findMAux(lean_object*, lean_object*);
lean_object* l_Array_filterAux___main(lean_object*);
lean_object* l_Array_Inhabited(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21(lean_object*);
lean_object* l_Array_indexOfAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forRevMAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_HasToString(lean_object*);
lean_object* l_Array_anyM___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapM(lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___at_Array_findRev_x21___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx_x27___rarg(lean_object*, lean_object*);
lean_object* l_Array_findIdx_x21(lean_object*);
lean_object* l_Array_back___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main(lean_object*);
lean_object* l_Array_findRev_x21___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOf___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRev_x21___rarg___closed__1;
lean_object* l_Array_findIdxAux(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_foldlFromM___spec__1(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_mapM___spec__1(lean_object*, lean_object*);
lean_object* l_Array_findMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_find_x21___rarg___closed__1;
lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__2;
lean_object* l_Array_anyRangeM(lean_object*, lean_object*);
lean_object* l_Array_forRevM(lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l_Array_extractAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_iterate___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_get_x3f(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldrM___spec__1(lean_object*, lean_object*);
lean_object* l_Array_get_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRange___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_modify___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f(lean_object*);
lean_object* l_Array_findRevMAux___main___at_Array_findRev_x3f___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_feraseIdx___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_getOp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Array_swapAt_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldrM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_data(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg(lean_object*, lean_object*);
lean_object* l_Array_reverseAux___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_anyRange___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___boxed(lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forRevMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterate_u2082___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdxSzAuxInstance(lean_object*);
lean_object* l_Array_find_x21(lean_object*, lean_object*);
lean_object* l_Array_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_allRangeM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at_Array_find_x3f___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_HasAppend(lean_object*);
lean_object* l_Array_findIdx_x21___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_findIdx_x21___rarg___closed__1;
lean_object* l_Array_forRevMAux(lean_object*);
lean_object* l_Array_iterate(lean_object*, lean_object*);
lean_object* l_Array_forMAux(lean_object*);
lean_object* l_Array_findM_x3f___boxed(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* l_Array_contains(lean_object*);
lean_object* l_Array_insertAtAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_all___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverseAux___main(lean_object*);
lean_object* l_Array_swapAt_x21(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_mapIdxM___spec__1(lean_object*, lean_object*);
lean_object* l_Array_sz___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Array_contains___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux(lean_object*);
lean_object* l_Array_isEqv___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldrM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main(lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main(lean_object*);
lean_object* l_Array_insertAt(lean_object*);
lean_object* l_Array_foldlFromM(lean_object*, lean_object*);
lean_object* l_Array_filter___rarg(lean_object*, lean_object*);
lean_object* l_Array_forRevMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_HasRepr(lean_object*);
lean_object* l_Array_mk___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main(lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_mapIdxM___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_contains___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateFrom(lean_object*, lean_object*);
lean_object* l_Array_eraseIdxAux___rarg(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Array_umapM___spec__1(lean_object*, lean_object*);
lean_object* l_Array_iterate___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyFrom(lean_object*);
lean_object* l_Array_set_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Array_umapM___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__1;
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_foldlM_u2082___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrM___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_any___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_contains___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_foldr(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRevMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldl___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_mk(x_2, x_3);
return x_4;
}
}
lean_object* l_Array_data___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_data(x_2, x_3);
return x_4;
}
}
lean_object* l_Array_sz___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_sz(x_2);
return x_3;
}
}
lean_object* l_Array_size___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_get_size(x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mkEmpty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_mk_empty_array_with_capacity(x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_push___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_push(x_2, x_3);
return x_4;
}
}
lean_object* l_Array_mkArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_mk_array(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Array_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Array_empty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Array_HasEmptyc(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Array_Inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
uint8_t l_Array_isEmpty___rarg(lean_object* x_1) {
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
lean_object* l_Array_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_isEmpty___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Array_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_singleton___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
lean_object* l_Array_singleton(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_singleton___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Array_get___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_fget(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_uget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_get_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_get(x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_back___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_back(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_back___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_back___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_back___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_get_x3f___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_get_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_get_x3f___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_get_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_get_x3f___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_getD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_6; 
x_6 = lean_array_fget(x_1, x_2);
return x_6;
}
}
}
lean_object* l_Array_getD(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_getD___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_getD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_getD___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_getOp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_get(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_getOp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_getOp___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_getOp___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_getOp___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_fset(x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_uset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_array_uset(x_2, x_6, x_4);
return x_7;
}
}
lean_object* l_Array_set_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_set(x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_swap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_fswap(x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_swap_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_swap(x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_swapAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_array_fget(x_1, x_2);
x_5 = lean_array_fset(x_1, x_2, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Array_swapAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_swapAt___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_swapAt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_swapAt___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("index ");
return x_1;
}
}
lean_object* _init_l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" out of bounds");
return x_1;
}
}
lean_object* _init_l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Data.Array.Basic");
return x_1;
}
}
lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Nat_repr(x_2);
x_6 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__3;
x_11 = lean_unsigned_to_nat(143u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Init_Util_1__mkPanicMessage(x_10, x_11, x_12, x_9);
lean_dec(x_9);
x_14 = lean_panic_fn(x_4, x_13);
return x_14;
}
}
lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Array_swapAt_x21___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Nat_repr(x_2);
x_6 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__3;
x_11 = lean_unsigned_to_nat(143u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Init_Util_1__mkPanicMessage(x_10, x_11, x_12, x_9);
lean_dec(x_9);
x_14 = lean_panic_fn(x_4, x_13);
return x_14;
}
}
lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Array_swapAt_x21___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Array_swapAt_x21___spec__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_swapAt_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Array_swapAt_x21___spec__1___rarg(x_3, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = lean_array_fset(x_1, x_2, x_3);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
lean_object* l_Array_swapAt_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_swapAt_x21___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_pop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_pop(x_2);
return x_3;
}
}
lean_object* l_Array_shrink___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_le(x_3, x_2);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_array_pop(x_1);
x_1 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
lean_object* l_Array_shrink___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_shrink___main___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_shrink___main___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_shrink___main___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_shrink___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_shrink___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_shrink(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_shrink___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_shrink___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_shrink___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_array_fget(x_3, x_5);
lean_inc(x_4);
lean_inc(x_5);
x_14 = lean_apply_3(x_4, x_5, x_13, x_6);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_17 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___rarg), 6, 5);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, lean_box(0));
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_4);
lean_closure_set(x_17, 4, x_16);
x_18 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_17);
return x_18;
}
}
}
lean_object* l_Array_iterateMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Array_iterateMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_iterateMAux___main___rarg(x_1, lean_box(0), x_3, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Array_iterateM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateM___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_iterateM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_foldlM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_18 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_foldlM___spec__1___rarg___boxed), 7, 6);
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
lean_object* l_Array_iterateMAux___main___at_Array_foldlM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_foldlM___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_Array_foldlM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_7 = l_Array_iterateMAux___main___at_Array_foldlM___spec__1___rarg(x_1, lean_box(0), x_3, x_5, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Array_foldlM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlM___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_foldlM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Array_foldlM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_foldlM___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateMAux___main___at_Array_foldlM___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_foldlM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_foldlM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_foldlFromM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_18 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_foldlFromM___spec__1___rarg___boxed), 7, 6);
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
lean_object* l_Array_iterateMAux___main___at_Array_foldlFromM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_foldlFromM___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_Array_foldlFromM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l_Array_iterateMAux___main___at_Array_foldlFromM___spec__1___rarg(x_1, lean_box(0), x_3, x_5, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Array_foldlFromM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlFromM___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_foldlFromM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Array_foldlFromM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_foldlFromM___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateMAux___main___at_Array_foldlFromM___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_foldlFromM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlFromM___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Array_foldlFromM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_foldlFromM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_4);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_12, lean_box(0), x_8);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_5);
x_15 = lean_nat_dec_lt(x_7, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_apply_2(x_17, lean_box(0), x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_array_fget(x_4, x_7);
x_21 = lean_array_fget(x_5, x_7);
lean_inc(x_6);
lean_inc(x_7);
x_22 = lean_apply_4(x_6, x_7, x_20, x_21, x_8);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_7, x_23);
lean_dec(x_7);
x_25 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___rarg), 8, 7);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, lean_box(0));
lean_closure_set(x_25, 2, lean_box(0));
lean_closure_set(x_25, 3, x_4);
lean_closure_set(x_25, 4, x_5);
lean_closure_set(x_25, 5, x_6);
lean_closure_set(x_25, 6, x_24);
x_26 = lean_apply_4(x_19, lean_box(0), lean_box(0), x_22, x_25);
return x_26;
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___rarg), 8, 0);
return x_3;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateM_u2082Aux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateM_u2082Aux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateM_u2082Aux___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Array_iterateM_u2082Aux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___rarg), 8, 0);
return x_3;
}
}
lean_object* l_Array_iterateM_u2082Aux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateM_u2082Aux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateM_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateM_u2082Aux___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_7, x_8, x_6);
return x_9;
}
}
lean_object* l_Array_iterateM_u2082(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateM_u2082___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Array_iterateM_u2082___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateM_u2082(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_foldlM_u2082___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_6);
x_11 = lean_nat_dec_lt(x_8, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_9);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_7);
x_16 = lean_nat_dec_lt(x_8, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_array_fget(x_6, x_8);
x_22 = lean_array_fget(x_7, x_8);
lean_inc(x_4);
x_23 = lean_apply_3(x_4, x_9, x_21, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_8, x_24);
x_26 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Array_foldlM_u2082___spec__1___rarg___boxed), 9, 8);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, lean_box(0));
lean_closure_set(x_26, 2, lean_box(0));
lean_closure_set(x_26, 3, x_4);
lean_closure_set(x_26, 4, x_5);
lean_closure_set(x_26, 5, x_6);
lean_closure_set(x_26, 6, x_7);
lean_closure_set(x_26, 7, x_25);
x_27 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_23, x_26);
return x_27;
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_foldlM_u2082___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Array_foldlM_u2082___spec__1___rarg___boxed), 9, 0);
return x_3;
}
}
lean_object* l_Array_foldlM_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_9 = l_Array_iterateM_u2082Aux___main___at_Array_foldlM_u2082___spec__1___rarg(x_1, lean_box(0), lean_box(0), x_4, x_6, x_6, x_7, x_8, x_5);
return x_9;
}
}
lean_object* l_Array_foldlM_u2082(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlM_u2082___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_foldlM_u2082___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateM_u2082Aux___main___at_Array_foldlM_u2082___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_foldlM_u2082___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateM_u2082Aux___main___at_Array_foldlM_u2082___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_foldlM_u2082___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_foldlM_u2082(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_findMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = l_Array_findMAux___main___rarg(x_2, lean_box(0), x_3, x_4, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_5);
return x_11;
}
}
}
lean_object* l_Array_findMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_array_fget(x_3, x_5);
lean_inc(x_4);
x_14 = lean_apply_1(x_4, x_13);
x_15 = lean_alloc_closure((void*)(l_Array_findMAux___main___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
x_16 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
lean_object* l_Array_findMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findMAux___main___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_findMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_findMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_findMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_findMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_findMAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_findMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findMAux___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_findMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_findM_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_findMAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_findM_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findM_x3f___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_findM_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findM_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_findRevMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Array_findRevMAux___main___rarg(x_1, lean_box(0), x_2, x_3, x_4, lean_box(0));
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
lean_object* l_Array_findRevMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_5, x_13);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_array_fget(x_3, x_14);
lean_inc(x_4);
x_17 = lean_apply_1(x_4, x_16);
x_18 = lean_alloc_closure((void*)(l_Array_findRevMAux___main___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_14);
x_19 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
}
lean_object* l_Array_findRevMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findRevMAux___main___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Array_findRevMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_findRevMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_findRevMAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findRevMAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Array_findRevMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findRevMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_findRevMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findRevMAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
lean_object* l_Array_findRevMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findRevMAux___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Array_findRevMAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_findRevMAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Array_findRevMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findRevMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_findRevM_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_get_size(x_3);
x_6 = l_Array_findRevMAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5, lean_box(0));
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Array_findRevM_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findRevM_x3f___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_findRevM_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findRevM_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_iterate___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_inc(x_4);
x_9 = lean_apply_3(x_2, x_4, x_8, x_5);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Array_iterate___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_iterate___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Array_iterate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_iterateMAux___main___at_Array_iterate___spec__1___rarg(x_1, x_3, x_1, x_4, x_2);
return x_5;
}
}
lean_object* l_Array_iterate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterate___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_iterate___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Array_iterate___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterate___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_iterate___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_iterateFrom___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_inc(x_4);
x_9 = lean_apply_3(x_2, x_4, x_8, x_5);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Array_iterateFrom___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_iterateFrom___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Array_iterateFrom___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Array_iterateFrom___spec__1___rarg(x_1, x_4, x_1, x_3, x_2);
return x_5;
}
}
lean_object* l_Array_iterateFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateFrom___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_iterateFrom___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Array_iterateFrom___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateFrom___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateFrom___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_foldl___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Array_iterateMAux___main___at_Array_foldl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_foldl___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Array_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_iterateMAux___main___at_Array_foldl___spec__1___rarg(x_1, x_3, x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Array_foldl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldl___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_foldl___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Array_foldl___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_foldl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_foldl___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_foldlFrom___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Array_iterateMAux___main___at_Array_foldlFrom___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_foldlFrom___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Array_foldlFrom___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Array_foldlFrom___spec__1___rarg(x_1, x_3, x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Array_foldlFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlFrom___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_foldlFrom___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Array_foldlFrom___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_foldlFrom___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_foldlFrom___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_4);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_fget(x_3, x_5);
x_12 = lean_array_fget(x_4, x_5);
lean_inc(x_2);
lean_inc(x_5);
x_13 = lean_apply_4(x_2, x_5, x_11, x_12, x_6);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_5 = x_15;
x_6 = x_13;
goto _start;
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_iterate_u2082___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
lean_object* l_Array_iterate_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateM_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg(x_1, x_4, x_1, x_2, x_5, x_3);
return x_6;
}
}
lean_object* l_Array_iterate_u2082(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_iterate_u2082___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateM_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_iterate_u2082___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterate_u2082___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_4);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_fget(x_3, x_5);
x_12 = lean_array_fget(x_4, x_5);
lean_inc(x_1);
x_13 = lean_apply_3(x_1, x_6, x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_5 = x_15;
x_6 = x_13;
goto _start;
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_foldl_u2082___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_iterateM_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
lean_object* l_Array_foldl_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateM_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg(x_1, x_3, x_3, x_4, x_5, x_2);
return x_6;
}
}
lean_object* l_Array_foldl_u2082(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldl_u2082___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateM_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_foldl_u2082___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_foldl_u2082___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_findMAux___main___at_Array_find_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_findMAux___main___at_Array_find_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findMAux___main___at_Array_find_x3f___spec__1___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_find_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_findMAux___main___at_Array_find_x3f___spec__1___rarg(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_Array_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_find_x3f___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Array_findMAux___main___at_Array_find_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findMAux___main___at_Array_find_x3f___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_find_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_find_x3f___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_findMAux___main___at_Array_find_x21___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_findMAux___main___at_Array_find_x21___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findMAux___main___at_Array_find_x21___spec__1___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* _init_l_Array_find_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to find element");
return x_1;
}
}
lean_object* _init_l_Array_find_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__3;
x_2 = lean_unsigned_to_nat(256u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_Array_find_x21___rarg___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_find_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_findMAux___main___at_Array_find_x21___spec__1___rarg(x_3, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Array_find_x21___rarg___closed__2;
x_7 = lean_panic_fn(x_1, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
return x_8;
}
}
}
lean_object* l_Array_find_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_find_x21___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_findMAux___main___at_Array_find_x21___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findMAux___main___at_Array_find_x21___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_find_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_find_x21___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_findRevMAux___main___at_Array_findRev_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_findRevMAux___main___at_Array_findRev_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findRevMAux___main___at_Array_findRev_x3f___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Array_findRev_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = l_Array_findRevMAux___main___at_Array_findRev_x3f___spec__1___rarg(x_2, x_1, x_3, lean_box(0));
return x_4;
}
}
lean_object* l_Array_findRev_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findRev_x3f___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Array_findRevMAux___main___at_Array_findRev_x3f___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findRevMAux___main___at_Array_findRev_x3f___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_findRev_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findRev_x3f___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_findRevMAux___main___at_Array_findRev_x21___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_findRevMAux___main___at_Array_findRev_x21___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findRevMAux___main___at_Array_findRev_x21___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* _init_l_Array_findRev_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__3;
x_2 = lean_unsigned_to_nat(264u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_Array_find_x21___rarg___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_findRev_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = l_Array_findRevMAux___main___at_Array_findRev_x21___spec__1___rarg(x_3, x_2, x_4, lean_box(0));
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Array_findRev_x21___rarg___closed__1;
x_7 = lean_panic_fn(x_1, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
return x_8;
}
}
}
lean_object* l_Array_findRev_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findRev_x21___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_findRevMAux___main___at_Array_findRev_x21___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findRevMAux___main___at_Array_findRev_x21___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_findRev_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findRev_x21___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_findIdxAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_1, x_3);
lean_inc(x_2);
x_8 = lean_apply_1(x_2, x_7);
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
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
}
}
}
lean_object* l_Array_findIdxAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findIdxAux___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_findIdxAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_findIdxAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_findIdxAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findIdxAux___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_findIdxAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_findIdx_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_findIdxAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_findIdx_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findIdx_x3f___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_findIdx_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findIdx_x3f___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Array_findIdx_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__3;
x_2 = lean_unsigned_to_nat(280u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_Array_find_x21___rarg___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_findIdx_x21___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_findIdxAux___main___rarg(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Nat_Inhabited;
x_6 = l_Array_findIdx_x21___rarg___closed__1;
x_7 = lean_panic_fn(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
return x_8;
}
}
}
lean_object* l_Array_findIdx_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_findIdx_x21___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_findIdx_x21___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findIdx_x21___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = l_Array_anyRangeMAux___main___rarg(x_2, x_3, x_4, lean_box(0), x_5, x_8);
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
lean_object* l_Array_anyRangeMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
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
x_14 = lean_array_fget(x_2, x_6);
lean_inc(x_5);
x_15 = lean_apply_1(x_5, x_14);
x_16 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_16, 0, x_6);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_5);
x_17 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
}
lean_object* l_Array_anyRangeMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Array_anyRangeMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_anyRangeMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_anyRangeMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_anyRangeMAux___main___rarg(x_1, x_2, x_3, lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_anyRangeMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_anyRangeMAux___main___rarg(x_1, x_2, x_4, lean_box(0), x_3, x_5);
return x_6;
}
}
lean_object* l_Array_anyM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyM___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Array_anyM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_anyM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg___lambda__1(lean_object* x_1, uint8_t x_2) {
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
lean_object* l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(x_8);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_array_fget(x_5, x_7);
lean_inc(x_3);
x_16 = lean_apply_1(x_3, x_15);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_17, 0, x_1);
lean_inc(x_4);
x_18 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_16, x_17);
x_19 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg___lambda__2___boxed), 8, 7);
lean_closure_set(x_19, 0, x_7);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_4);
lean_closure_set(x_19, 5, x_5);
lean_closure_set(x_19, 6, x_6);
x_20 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Array_allM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_array_get_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg(x_1, x_2, x_3, x_4, x_2, x_5, x_6);
x_8 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_Array_allM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_allM___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg___lambda__1(x_1, x_3);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allM___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_anyRangeMAux___main___at_Array_allM___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_allM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_allM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyRangeM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_le(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = l_Array_anyRangeMAux___main___rarg(x_1, x_2, x_6, lean_box(0), x_5, x_3);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = l_Array_anyRangeMAux___main___rarg(x_1, x_2, x_4, lean_box(0), x_5, x_3);
return x_9;
}
}
}
lean_object* l_Array_anyRangeM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyRangeM___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_anyRangeM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_anyRangeM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg___lambda__1(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(x_8);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_array_fget(x_5, x_7);
lean_inc(x_3);
x_16 = lean_apply_1(x_3, x_15);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_17, 0, x_1);
lean_inc(x_4);
x_18 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_16, x_17);
x_19 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg___lambda__2___boxed), 8, 7);
lean_closure_set(x_19, 0, x_7);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_4);
lean_closure_set(x_19, 5, x_5);
lean_closure_set(x_19, 6, x_6);
x_20 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9) {
_start:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2___rarg(x_2, x_3, x_4, x_5, x_6, lean_box(0), x_7, x_8, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(x_9);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
return x_16;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_apply_2(x_12, lean_box(0), x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_array_fget(x_7, x_9);
lean_inc(x_4);
x_18 = lean_apply_1(x_4, x_17);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_19, 0, x_1);
lean_inc(x_5);
x_20 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_18, x_19);
x_21 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2___rarg___lambda__1___boxed), 9, 8);
lean_closure_set(x_21, 0, x_9);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_3);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_5);
lean_closure_set(x_21, 6, x_7);
lean_closure_set(x_21, 7, x_8);
x_22 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_20, x_21);
return x_22;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2___rarg), 9, 0);
return x_3;
}
}
lean_object* l_Array_allRangeM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_le(x_4, x_7);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_allM___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_1);
if (x_8 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_inc(x_6);
lean_inc(x_2);
x_10 = l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg(x_1, x_2, x_5, x_6, x_2, x_7, x_3);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
x_12 = l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2___rarg(x_1, x_2, x_4, x_5, x_6, lean_box(0), x_2, x_4, x_3);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_9);
return x_13;
}
}
}
lean_object* l_Array_allRangeM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_allRangeM___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg___lambda__1(x_1, x_3);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_anyRangeMAux___main___at_Array_allRangeM___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_allRangeM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_allRangeM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Array_any___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_10;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_any___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_any___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
uint8_t l_Array_any___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at_Array_any___spec__1___rarg(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_any(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_any___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_any___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Array_any___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_any___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_any___rarg(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Array_anyRange___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_10;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_anyRange___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_anyRange___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Array_anyRange___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
lean_dec(x_3);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_5, x_7);
lean_inc(x_3);
x_11 = lean_apply_1(x_3, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_7, x_13);
lean_dec(x_7);
x_4 = lean_box(0);
x_7 = x_14;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
return x_12;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_anyRange___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_anyRange___spec__2___rarg___boxed), 7, 0);
return x_2;
}
}
uint8_t l_Array_anyRange___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_le(x_3, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Array_anyRangeMAux___main___at_Array_anyRange___spec__1___rarg(x_1, x_4, x_1, x_5, x_2);
lean_dec(x_5);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = l_Array_anyRangeMAux___main___at_Array_anyRange___spec__2___rarg(x_1, x_3, x_4, lean_box(0), x_1, x_3, x_2);
return x_8;
}
}
}
lean_object* l_Array_anyRange(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyRange___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_anyRange___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Array_anyRange___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_anyRange___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at_Array_anyRange___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_anyRange___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRange___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_10;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_2);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_4, x_6);
lean_inc(x_2);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_6, x_12);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_13;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
uint8_t l_Array_anyFrom___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_le(x_4, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__1___rarg(x_1, x_3, x_1, x_4, x_2);
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__2___rarg(x_1, x_3, lean_box(0), x_1, x_4, x_2);
lean_dec(x_4);
return x_7;
}
}
}
lean_object* l_Array_anyFrom(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyFrom___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_anyRangeMAux___main___at_Array_anyFrom___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_anyFrom___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyFrom___rarg(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Array_all___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = 1;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_all___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_all___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
uint8_t l_Array_all___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at_Array_all___spec__1___rarg(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_Array_all(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_all___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_all___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Array_all___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_all___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_all___rarg(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Array_allRange___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = 1;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRange___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_allRange___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Array_allRange___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
lean_dec(x_3);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_5, x_7);
lean_inc(x_3);
x_11 = lean_apply_1(x_3, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_3);
x_13 = 1;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_7, x_14);
lean_dec(x_7);
x_4 = lean_box(0);
x_7 = x_15;
goto _start;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRange___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_allRange___spec__2___rarg___boxed), 7, 0);
return x_2;
}
}
uint8_t l_Array_allRange___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_le(x_3, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Array_anyRangeMAux___main___at_Array_allRange___spec__1___rarg(x_1, x_4, x_1, x_5, x_2);
lean_dec(x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec(x_5);
x_10 = l_Array_anyRangeMAux___main___at_Array_allRange___spec__2___rarg(x_1, x_3, x_4, lean_box(0), x_1, x_3, x_2);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
}
lean_object* l_Array_allRange(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_allRange___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRange___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Array_allRange___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_allRange___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_anyRangeMAux___main___at_Array_allRange___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Array_allRange___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_allRange___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_array_fget(x_3, x_11);
lean_inc(x_4);
lean_inc(x_11);
x_14 = lean_apply_3(x_4, x_11, x_13, x_7);
x_15 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___rarg___boxed), 7, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, lean_box(0));
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_11);
lean_closure_set(x_15, 5, lean_box(0));
x_16 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5, lean_box(0), x_7);
return x_8;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_Array_Basic_3__iterateRevMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateRevM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___rarg(x_1, lean_box(0), x_3, x_5, x_6, lean_box(0), x_4);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Array_iterateRevM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateRevM___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_iterateRevM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateRevM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldrM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_6, x_11);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_fget(x_5, x_12);
lean_inc(x_3);
x_15 = lean_apply_2(x_3, x_14, x_8);
x_16 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldrM___spec__1___rarg___boxed), 8, 7);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, lean_box(0));
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_12);
lean_closure_set(x_16, 6, lean_box(0));
x_17 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldrM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldrM___spec__1___rarg___boxed), 8, 0);
return x_3;
}
}
lean_object* l_Array_foldrM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_5);
lean_inc(x_5);
x_7 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldrM___spec__1___rarg(x_1, lean_box(0), x_3, x_5, x_5, x_6, lean_box(0), x_4);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Array_foldrM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldrM___rarg), 5, 0);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldrM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldrM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldrM___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldrM___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_foldrM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_foldrM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_iterateRev___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_array_fget(x_3, x_10);
lean_inc(x_2);
lean_inc(x_10);
x_12 = lean_apply_3(x_2, x_10, x_11, x_6);
x_4 = x_10;
x_5 = lean_box(0);
x_6 = x_12;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_iterateRev___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_iterateRev___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Array_iterateRev___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_iterateRev___spec__1___rarg(x_1, x_3, x_1, x_4, lean_box(0), x_2);
return x_5;
}
}
lean_object* l_Array_iterateRev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateRev___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_iterateRev___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_iterateRev___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_iterateRev___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_iterateRev___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldr___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_array_fget(x_3, x_10);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, x_11, x_6);
x_4 = x_10;
x_5 = lean_box(0);
x_6 = x_12;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldr___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldr___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Array_foldr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldr___spec__1___rarg(x_1, x_3, x_3, x_4, lean_box(0), x_2);
return x_5;
}
}
lean_object* l_Array_foldr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldr___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldr___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_foldr___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_foldr___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_foldr___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_toList___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_array_fget(x_2, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
x_3 = x_9;
x_4 = lean_box(0);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_3);
return x_5;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_toList___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_toList___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_toList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_array_get_size(x_1);
x_4 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_toList___spec__1___rarg(x_1, x_1, x_3, lean_box(0), x_2);
return x_4;
}
}
lean_object* l_Array_toList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_toList___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_toList___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Array_toList___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_toList___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_toList___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Array_HasRepr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#");
return x_1;
}
}
lean_object* l_Array_HasRepr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Array_toList___rarg(x_2);
x_4 = l_List_repr___rarg(x_1, x_3);
x_5 = l_Array_HasRepr___rarg___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_HasRepr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_HasRepr___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_HasRepr___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_HasRepr___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_HasToString___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Array_toList___rarg(x_2);
x_4 = l_List_toString___rarg(x_1, x_3);
x_5 = l_Array_HasRepr___rarg___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_HasToString___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_HasToString___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_HasToString___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = x_6;
x_10 = lean_array_fset(x_3, x_1, x_9);
x_11 = l_Array_umapMAux___main___rarg(x_4, lean_box(0), x_5, x_8, x_10);
return x_11;
}
}
lean_object* l_Array_umapMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_5);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Array_empty___closed__1;
x_11 = x_5;
x_12 = lean_apply_2(x_9, lean_box(0), x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_array_fget(x_5, x_4);
x_14 = lean_box(0);
x_15 = x_14;
x_16 = lean_array_fset(x_5, x_4, x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_3);
lean_inc(x_13);
lean_inc(x_4);
x_18 = lean_apply_2(x_3, x_4, x_13);
x_19 = lean_alloc_closure((void*)(l_Array_umapMAux___main___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_19, 0, x_4);
lean_closure_set(x_19, 1, x_13);
lean_closure_set(x_19, 2, x_16);
lean_closure_set(x_19, 3, x_1);
lean_closure_set(x_19, 4, x_3);
x_20 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
}
lean_object* l_Array_umapMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_umapMAux___main___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_umapMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_umapMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_umapMAux___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_umapMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_umapMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Array_umapM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = x_6;
x_10 = lean_array_fset(x_3, x_1, x_9);
x_11 = l_Array_umapMAux___main___at_Array_umapM___spec__1___rarg(x_4, lean_box(0), x_5, x_8, x_10);
return x_11;
}
}
lean_object* l_Array_umapMAux___main___at_Array_umapM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_5);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Array_empty___closed__1;
x_11 = x_5;
x_12 = lean_apply_2(x_9, lean_box(0), x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_array_fget(x_5, x_4);
x_14 = lean_box(0);
x_15 = x_14;
x_16 = lean_array_fset(x_5, x_4, x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_3);
lean_inc(x_13);
x_18 = lean_apply_1(x_3, x_13);
x_19 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Array_umapM___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_19, 0, x_4);
lean_closure_set(x_19, 1, x_13);
lean_closure_set(x_19, 2, x_16);
lean_closure_set(x_19, 3, x_1);
lean_closure_set(x_19, 4, x_3);
x_20 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
}
lean_object* l_Array_umapMAux___main___at_Array_umapM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Array_umapM___spec__1___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_umapM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___at_Array_umapM___spec__1___rarg(x_1, lean_box(0), x_3, x_5, x_4);
return x_6;
}
}
lean_object* l_Array_umapM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_umapM___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Array_umapM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at_Array_umapM___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at_Array_umapM___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_umapMAux___main___at_Array_umapM___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_umapM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_umapM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_umapIdxM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___rarg(x_1, lean_box(0), x_3, x_5, x_4);
return x_6;
}
}
lean_object* l_Array_umapIdxM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_umapIdxM___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_umapIdxM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_umapIdxM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_array_push(x_2, x_3);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_fget(x_5, x_6);
lean_inc(x_3);
x_15 = lean_apply_1(x_3, x_14);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_7);
lean_inc(x_13);
x_17 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
x_20 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___boxed), 7, 6);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, lean_box(0));
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
lean_closure_set(x_20, 4, x_5);
lean_closure_set(x_20, 5, x_19);
x_21 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_17, x_20);
return x_21;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Array_mapM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_Array_mapM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_mk_empty_array_with_capacity(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_8 = l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg(x_1, lean_box(0), x_3, x_4, x_4, x_7, x_6);
return x_8;
}
}
lean_object* l_Array_mapM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mapM___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_mapM___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateMAux___main___at_Array_mapM___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mapM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_mapIdxM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_fget(x_5, x_6);
lean_inc(x_3);
lean_inc(x_6);
x_15 = lean_apply_2(x_3, x_6, x_14);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_7);
lean_inc(x_13);
x_17 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_20 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_mapIdxM___spec__1___rarg), 7, 6);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, lean_box(0));
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
lean_closure_set(x_20, 4, x_5);
lean_closure_set(x_20, 5, x_19);
x_21 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_17, x_20);
return x_21;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Array_mapIdxM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_mapIdxM___spec__1___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Array_mapIdxM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_mk_empty_array_with_capacity(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_8 = l_Array_iterateMAux___main___at_Array_mapIdxM___spec__1___rarg(x_1, lean_box(0), x_3, x_4, x_4, x_7, x_6);
return x_8;
}
}
lean_object* l_Array_mapIdxM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mapIdxM___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_mapIdxM___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_iterateMAux___main___at_Array_mapIdxM___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mapIdxM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapIdxM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_modifyM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_modifyM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_array_fset(x_3, x_4, x_2);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_apply_1(x_5, x_11);
x_15 = lean_alloc_closure((void*)(l_Array_modifyM___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_4);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
lean_object* l_Array_modifyM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_modifyM___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_modifyM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_modifyM___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_modifyM___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_modifyM(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_modify___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_array_fset(x_2, x_3, x_1);
x_9 = lean_apply_1(x_4, x_7);
x_10 = lean_array_fset(x_8, x_3, x_9);
return x_10;
}
}
}
lean_object* l_Array_modify(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_modify___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_modify___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_modify___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at_Array_mapIdx___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
lean_dec(x_8);
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_Array_mapIdx___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Array_mapIdx___spec__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Array_mapIdx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_umapMAux___main___at_Array_mapIdx___spec__1___rarg(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Array_mapIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mapIdx___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Array_map___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_1);
lean_inc(x_8);
x_12 = lean_apply_1(x_1, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
lean_dec(x_8);
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_Array_map___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Array_map___spec__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Array_map___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_umapMAux___main___at_Array_map___spec__1___rarg(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Array_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_map___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Array_forMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = l_Array_forMAux___main___rarg(x_2, lean_box(0), lean_box(0), x_3, x_4, x_7);
return x_8;
}
}
lean_object* l_Array_forMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_fget(x_5, x_6);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_4);
x_15 = lean_apply_1(x_4, x_13);
x_16 = lean_alloc_closure((void*)(l_Array_forMAux___main___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_16, 0, x_6);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_4);
lean_closure_set(x_16, 3, x_5);
x_17 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
}
lean_object* l_Array_forMAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forMAux___main___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Array_forMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_forMAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_forMAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forMAux___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Array_forMAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forMAux___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Array_forMAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_forMAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_forMAux___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Array_forM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forM___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Array_forM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_forM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_forRevMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forRevMAux___main___rarg(x_1, lean_box(0), lean_box(0), x_2, x_3, x_4, lean_box(0));
return x_6;
}
}
lean_object* l_Array_forRevMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_6, x_14);
x_16 = lean_array_fget(x_5, x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_4);
x_18 = lean_apply_1(x_4, x_16);
x_19 = lean_alloc_closure((void*)(l_Array_forRevMAux___main___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_4);
lean_closure_set(x_19, 2, x_5);
lean_closure_set(x_19, 3, x_15);
x_20 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
}
lean_object* l_Array_forRevMAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forRevMAux___main___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Array_forRevMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forRevMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_forRevMAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forRevMAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Array_forRevMAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_forRevMAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_forRevMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forRevMAux___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
lean_object* l_Array_forRevMAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forRevMAux___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Array_forRevMAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_forRevMAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Array_forRevMAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_forRevMAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_forRevM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_5);
x_7 = l_Array_forRevMAux___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_6, lean_box(0));
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Array_forRevM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forRevM___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Array_forRevM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_forRevM(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_extractAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_2, x_3);
if (x_6 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
x_9 = lean_array_fget(x_1, x_2);
lean_dec(x_2);
x_10 = lean_array_push(x_5, x_9);
x_2 = x_8;
x_4 = lean_box(0);
x_5 = x_10;
goto _start;
}
}
}
lean_object* l_Array_extractAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_extractAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_extractAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_extractAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_extractAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_extractAux___main___rarg(x_1, x_2, x_3, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Array_extractAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_extractAux___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_extractAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_extractAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_extract___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_nat_sub(x_3, x_2);
x_5 = lean_mk_empty_array_with_capacity(x_4);
lean_dec(x_4);
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_8; 
x_8 = l_Array_extractAux___main___rarg(x_1, x_2, x_3, lean_box(0), x_5);
return x_8;
}
}
}
lean_object* l_Array_extract(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_extract___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_extract___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_extract___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = lean_array_push(x_4, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_append___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_append___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2, x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Array_append(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_append___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_append___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_append___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l_Array_HasAppend___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_append___rarg___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Array_HasAppend(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_HasAppend___closed__1;
return x_2;
}
}
uint8_t l_Array_isEqvAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 1;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_array_fget(x_1, x_5);
x_10 = lean_array_fget(x_2, x_5);
lean_inc(x_4);
x_11 = lean_apply_2(x_4, x_9, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_3 = lean_box(0);
x_5 = x_15;
goto _start;
}
}
}
}
lean_object* l_Array_isEqvAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_isEqvAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_isEqvAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
uint8_t l_Array_isEqvAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___main___rarg(x_1, x_2, lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_Array_isEqvAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_isEqvAux___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_isEqvAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
uint8_t l_Array_isEqv___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_isEqvAux___main___rarg(x_1, x_2, lean_box(0), x_3, x_8);
return x_9;
}
}
}
lean_object* l_Array_isEqv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_isEqv___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_isEqv___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t l_Array_HasBeq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_eq(x_4, x_5);
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
x_9 = l_Array_isEqvAux___main___rarg(x_2, x_3, lean_box(0), x_1, x_8);
return x_9;
}
}
}
lean_object* l_Array_HasBeq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_HasBeq___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_HasBeq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_HasBeq___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_reverseAux___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_div(x_3, x_4);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_nat_sub(x_3, x_2);
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = lean_array_swap(x_1, x_2, x_9);
lean_dec(x_9);
x_11 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_1 = x_10;
x_2 = x_11;
goto _start;
}
}
}
lean_object* l_Array_reverseAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_reverseAux___main___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_reverseAux___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_reverseAux___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_reverseAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_reverseAux___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_reverse___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_reverseAux___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_reverse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_reverse___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Array_filterAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = l_Array_shrink___main___rarg(x_2, x_4);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_17 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_3 = x_16;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_fswap(x_2, x_3, x_4);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_22 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_2 = x_19;
x_3 = x_21;
x_4 = x_22;
goto _start;
}
}
}
}
}
lean_object* l_Array_filterAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_filterAux___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_filterAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_filterAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_filterAux___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_filter___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_filterAux___main___rarg(x_1, x_2, x_3, x_3);
return x_4;
}
}
lean_object* l_Array_filter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_filter___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_indexOfAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_indexOfAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_indexOfAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_indexOfAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_indexOfAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_indexOfAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_indexOfAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_indexOfAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_indexOfAux___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_indexOfAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_indexOfAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_indexOf___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_indexOfAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_indexOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_indexOf___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_indexOf___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_indexOf___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_eraseIdxAux___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_array_pop(x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_nat_add(x_1, x_6);
x_9 = lean_array_fswap(x_2, x_1, x_7);
lean_dec(x_7);
lean_dec(x_1);
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
lean_object* l_Array_eraseIdxAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_eraseIdxAux___main___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_eraseIdxAux___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_eraseIdxAux___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_eraseIdxAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_eraseIdxAux___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_feraseIdx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = l_Array_eraseIdxAux___main___rarg(x_4, x_1);
return x_5;
}
}
lean_object* l_Array_feraseIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_feraseIdx___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_feraseIdx___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_feraseIdx___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_eraseIdx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_2, x_5);
x_7 = l_Array_eraseIdxAux___main___rarg(x_6, x_1);
return x_7;
}
}
}
lean_object* l_Array_eraseIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_eraseIdx___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_eraseIdx___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_eraseIdx___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_eraseIdxSzAuxInstance___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_pop(x_1);
return x_2;
}
}
lean_object* l_Array_eraseIdxSzAuxInstance(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_eraseIdxSzAuxInstance___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Array_eraseIdxSzAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_array_pop(x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
x_10 = lean_nat_add(x_2, x_8);
x_11 = lean_array_fswap(x_3, x_2, x_9);
lean_dec(x_9);
lean_dec(x_2);
x_2 = x_10;
x_3 = x_11;
x_4 = lean_box(0);
goto _start;
}
}
}
lean_object* l_Array_eraseIdxSzAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_eraseIdxSzAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_eraseIdxSzAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_eraseIdxSzAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_eraseIdxSzAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_eraseIdxSzAux___main___rarg(x_1, x_2, x_3, lean_box(0));
return x_5;
}
}
lean_object* l_Array_eraseIdxSzAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_eraseIdxSzAux___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_eraseIdxSzAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_eraseIdxSzAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_eraseIdx_x27___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
lean_inc(x_1);
x_5 = l_Array_eraseIdxSzAux___main___rarg(x_1, x_4, x_1, lean_box(0));
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_eraseIdx_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_eraseIdx_x27___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_eraseIdx_x27___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_eraseIdx_x27___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Array_contains___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_4, x_6);
lean_inc(x_1);
lean_inc(x_3);
x_10 = lean_apply_2(x_1, x_3, x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_6, x_12);
lean_dec(x_6);
x_6 = x_13;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_contains___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyRangeMAux___main___at_Array_contains___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
uint8_t l_Array_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_anyRangeMAux___main___at_Array_contains___spec__1___rarg(x_1, x_2, x_3, x_2, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_contains(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_contains___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Array_contains___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_anyRangeMAux___main___at_Array_contains___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_contains___rarg(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_insertAtAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_3, x_5);
x_7 = lean_array_swap(x_2, x_6, x_3);
lean_dec(x_3);
x_2 = x_7;
x_3 = x_6;
goto _start;
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
lean_object* l_Array_insertAtAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_insertAtAux___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_insertAtAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_insertAtAux___main___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_insertAtAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_insertAtAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_insertAtAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_insertAtAux___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_insertAtAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_insertAtAux___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Array_insertAt___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid index");
return x_1;
}
}
lean_object* _init_l_Array_insertAt___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__3;
x_2 = lean_unsigned_to_nat(586u);
x_3 = lean_unsigned_to_nat(20u);
x_4 = l_Array_insertAt___rarg___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_insertAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_4, x_2);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_array_push(x_1, x_3);
x_7 = lean_array_get_size(x_6);
x_8 = l_Array_insertAtAux___main___rarg(x_2, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = l_Array_empty___closed__1;
x_10 = l_Array_insertAt___rarg___closed__2;
x_11 = lean_panic_fn(x_9, x_10);
return x_11;
}
}
}
lean_object* l_Array_insertAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_insertAt___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_insertAt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_insertAt___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_toArrayAux___main___rarg(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_array_push(x_2, x_3);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
}
}
lean_object* l_List_toArrayAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toArrayAux___main___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_toArrayAux___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_toArrayAux___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_toArrayAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toArrayAux___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_redLength___main___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_List_redLength___main___rarg(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
}
lean_object* l_List_redLength___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_redLength___main___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_List_redLength___main___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_redLength___main___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_redLength___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_redLength___main___rarg(x_1);
return x_2;
}
}
lean_object* l_List_redLength(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_redLength___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_List_redLength___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_redLength___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_toArray___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_List_redLength___main___rarg(x_1);
x_3 = lean_mk_empty_array_with_capacity(x_2);
lean_dec(x_2);
x_4 = l_List_toArrayAux___main___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l_List_toArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_toArray___rarg), 1, 0);
return x_2;
}
}
lean_object* initialize_Init_Data_Nat_Basic(lean_object*);
lean_object* initialize_Init_Data_Fin_Basic(lean_object*);
lean_object* initialize_Init_Data_UInt(lean_object*);
lean_object* initialize_Init_Data_Repr(lean_object*);
lean_object* initialize_Init_Data_ToString(lean_object*);
lean_object* initialize_Init_Control_Id(lean_object*);
lean_object* initialize_Init_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Array_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Repr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Id(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_empty___closed__1 = _init_l_Array_empty___closed__1();
lean_mark_persistent(l_Array_empty___closed__1);
l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__1 = _init_l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__1);
l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__2 = _init_l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__2);
l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__3 = _init_l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__3);
l_Array_find_x21___rarg___closed__1 = _init_l_Array_find_x21___rarg___closed__1();
lean_mark_persistent(l_Array_find_x21___rarg___closed__1);
l_Array_find_x21___rarg___closed__2 = _init_l_Array_find_x21___rarg___closed__2();
lean_mark_persistent(l_Array_find_x21___rarg___closed__2);
l_Array_findRev_x21___rarg___closed__1 = _init_l_Array_findRev_x21___rarg___closed__1();
lean_mark_persistent(l_Array_findRev_x21___rarg___closed__1);
l_Array_findIdx_x21___rarg___closed__1 = _init_l_Array_findIdx_x21___rarg___closed__1();
lean_mark_persistent(l_Array_findIdx_x21___rarg___closed__1);
l_Array_HasRepr___rarg___closed__1 = _init_l_Array_HasRepr___rarg___closed__1();
lean_mark_persistent(l_Array_HasRepr___rarg___closed__1);
l_Array_HasAppend___closed__1 = _init_l_Array_HasAppend___closed__1();
lean_mark_persistent(l_Array_HasAppend___closed__1);
l_Array_insertAt___rarg___closed__1 = _init_l_Array_insertAt___rarg___closed__1();
lean_mark_persistent(l_Array_insertAt___rarg___closed__1);
l_Array_insertAt___rarg___closed__2 = _init_l_Array_insertAt___rarg___closed__2();
lean_mark_persistent(l_Array_insertAt___rarg___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
