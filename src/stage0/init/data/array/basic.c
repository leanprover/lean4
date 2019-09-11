// Lean compiler output
// Module: init.data.array.basic
// Imports: init.data.nat.basic init.data.fin.basic init.data.uint init.data.repr init.data.tostring init.control.id init.util
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
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Array_any___spec__1(lean_object*);
lean_object* l_Array_extractAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Array_map___spec__1(lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlFrom___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummap___boxed(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_iterateFrom___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_mfindRevAux___main___at_Array_findRev___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mforAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdxSzAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findRev(lean_object*, lean_object*);
lean_object* l_Array_toList___rarg___boxed(lean_object*);
lean_object* l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Array_all___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_getOpt(lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1(lean_object*, lean_object*);
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1(lean_object*);
lean_object* l_Array_any(lean_object*);
lean_object* l_List_repr___rarg(lean_object*, lean_object*);
lean_object* l_Array_swap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_revFoldl(lean_object*, lean_object*);
lean_object* l_Array_mfor___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterate___boxed(lean_object*, lean_object*);
lean_object* l_Array_mkArray(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterate___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfoldl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_iterateFrom___spec__1(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_iterate___spec__1(lean_object*, lean_object*);
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse(lean_object*);
lean_object* l_Array_filter(lean_object*);
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfoldl_u2082___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_data_array_basic_2__revIterateAux(lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_all___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
lean_object* l_Array_fswap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extractAux(lean_object*);
lean_object* l_Array_HasRepr(lean_object*);
lean_object* l_Array_ummapAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_allM___boxed(lean_object*, lean_object*);
lean_object* l_Array_eraseIdxAux___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterate_u2082___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterate___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfoldlFrom___boxed(lean_object*, lean_object*);
lean_object* l_Array_HasBeq(lean_object*);
lean_object* l_Array_ummapAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapIdx(lean_object*, lean_object*);
lean_object* l_Array_size___boxed(lean_object*, lean_object*);
lean_object* l_Array_uset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_data_array_basic_2__revIterateAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_iterateFrom___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfindRevAux(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_isEqv___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_fswapAt___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfoldlFrom___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_uget(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Array_anyMAux(lean_object*, lean_object*);
lean_object* l_Array_extractAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_uset(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Array_miterate_u2082___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfindRev___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Array_indexOfAux___main(lean_object*);
lean_object* l_Array_fswap(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_data_array_basic_2__revIterateAux___main(lean_object*, lean_object*);
lean_object* l_Array_mfoldl___boxed(lean_object*, lean_object*);
lean_object* l_Array_mfind(lean_object*, lean_object*);
lean_object* l_Array_mfindAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldl___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfindRev(lean_object*, lean_object*);
lean_object* l_Array_extractAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_swapAt(lean_object*);
lean_object* l_List_redLength___main(lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_mfoldl___spec__1(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_pop___boxed(lean_object*, lean_object*);
lean_object* l_Array_eraseIdxSzAux(lean_object*);
lean_object* l_Array_foldlFrom___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Array_all___spec__1(lean_object*);
lean_object* l_Array_mfindRevAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdxSzAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOfAux(lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_mmapIdx___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_redLength(lean_object*);
lean_object* l_Array_mkEmpty(lean_object*, lean_object*);
lean_object* l_Array_ummap___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_toArrayAux(lean_object*);
lean_object* l_Array_eraseIdxSzAuxInstance(lean_object*);
lean_object* l_Array_feraseIdx(lean_object*);
lean_object* l_Array_mkArray___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract(lean_object*);
lean_object* l_Array_eraseIdx(lean_object*);
lean_object* l_Array_mfindAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_map___rarg(lean_object*, lean_object*);
lean_object* l_Array_feraseIdx___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Array_swap(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_HasEmptyc(lean_object*);
lean_object* l_Array_extractAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg___boxed(lean_object*);
lean_object* l_Array_mapIdx(lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Array_uget___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_HasBeq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_allM(lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfindRev___boxed(lean_object*, lean_object*);
lean_object* l_Array_miterate_u2082Aux___boxed(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx_x27___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_mmapIdx___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterate(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___rarg___boxed__const__1;
lean_object* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfindAux___boxed(lean_object*, lean_object*);
lean_object* l_Array_mfor(lean_object*);
lean_object* l_Array_mfindAux___main___at_Array_find___spec__1(lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx_x27(lean_object*);
lean_object* l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_allM___rarg___lambda__1(uint8_t);
lean_object* l_Array_mfindAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfindRevAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isEqv(lean_object*);
lean_object* l_Array_mfind___boxed(lean_object*, lean_object*);
lean_object* l_Array_mfindAux___main(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_mmapIdx___spec__1(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfindAux___main___boxed(lean_object*, lean_object*);
lean_object* l_List_toString___rarg(lean_object*, lean_object*);
lean_object* l_Array_miterate_u2082Aux(lean_object*, lean_object*);
lean_object* l_Array_revFoldl___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_swapAt___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_miterate_u2082(lean_object*, lean_object*);
lean_object* l_Array_mfindRevAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main(lean_object*, lean_object*);
lean_object* l_Array_mfindAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterate_u2082Aux___main(lean_object*, lean_object*);
lean_object* l_Array_HasBeq___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_allM___rarg___lambda__1___boxed(lean_object*);
lean_object* l_Array_mfindRevAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_foldl(lean_object*, lean_object*);
lean_object* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfindAux___main___at_Array_find___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux(lean_object*, lean_object*);
lean_object* l_Array_mfindRevAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_fget(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___boxed(lean_object*);
lean_object* l_Array_singleton___rarg(lean_object*);
lean_object* l_Array_mfindRevAux___boxed(lean_object*, lean_object*);
lean_object* l_Array_mmapIdx___boxed(lean_object*, lean_object*);
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at_Array_all___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filter___rarg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_findRev___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
uint8_t l_Array_any___rarg(lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Array_mapIdx___spec__1(lean_object*, lean_object*);
lean_object* l_Array_push(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateFrom(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main(lean_object*, lean_object*);
lean_object* l_Array_eraseIdxAux___main(lean_object*);
lean_object* l_Array_mforAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_push___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_fget___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldl_u2082(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverseAux___rarg(lean_object*, lean_object*);
lean_object* l_Array_miterate_u2082Aux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Array_allM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqv___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_map(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Array_any___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Array_ummap___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_mmap___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterate_u2082___boxed(lean_object*, lean_object*);
lean_object* l_Array_mfoldl_u2082(lean_object*, lean_object*);
lean_object* l_Array_filterAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mforAux(lean_object*);
lean_object* l_Array_iterateFrom___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back(lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Array_map___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1(lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main(lean_object*);
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Array_allM___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_ummapAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapIdx___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main(lean_object*);
lean_object* l_Array_anyMAux___boxed(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_mfindRevAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArray(lean_object*);
lean_object* l_Array_getOpt___rarg(lean_object*, lean_object*);
lean_object* l_Array_reverseAux___main(lean_object*);
lean_object* l_Array_mfor___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfindRevAux___main___at_Array_findRev___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapIdx___boxed(lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Array_indexOf(lean_object*);
lean_object* l_Array_sz___boxed(lean_object*, lean_object*);
lean_object* l_Array_Inhabited(lean_object*);
lean_object* l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_modify___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_revIterate___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l_Array_HasToString(lean_object*);
lean_object* l_Array_singleton(lean_object*);
lean_object* l_Array_allM___rarg___closed__1;
lean_object* l_Array_shrink___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_mfindRevAux___main(lean_object*, lean_object*);
lean_object* l_Array_mapIdx___rarg(lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_HasAppend___closed__1;
lean_object* l_Array_isEmpty___rarg___boxed(lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1(lean_object*, lean_object*);
lean_object* l_Array_fswapAt(lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterate___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l_List_toArray___rarg(lean_object*);
lean_object* l_Array_filterAux___main(lean_object*);
lean_object* l_Array_reverseAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_eraseIdxSzAuxInstance___rarg(lean_object*);
lean_object* l_Array_pop(lean_object*, lean_object*);
lean_object* l_Array_findRev___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_sz(lean_object*, lean_object*);
lean_object* l_Array_miterateAux(lean_object*, lean_object*);
lean_object* l_Array_extractAux___main(lean_object*);
lean_object* l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___boxed(lean_object*, lean_object*);
lean_object* l_Array_mfindAux___main___at_Array_find___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_modify___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_size(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx_x27___rarg(lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isEmpty(lean_object*);
lean_object* l_Array_eraseIdxSzAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfoldl_u2082___boxed(lean_object*, lean_object*);
lean_object* l_Array_all(lean_object*);
lean_object* l_Array_eraseIdxAux(lean_object*);
lean_object* l_Array_fset(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mmapIdx(lean_object*, lean_object*);
lean_object* l_Array_indexOf___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldl_u2082___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfoldlFrom___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_get(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummap(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_mfoldl(lean_object*, lean_object*);
lean_object* l_Array_mfind___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterate(lean_object*, lean_object*);
lean_object* l_Array_eraseIdxSzAux___main(lean_object*);
uint8_t l_Array_isEqvAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlFrom(lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at_Array_any___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Array_ummap___spec__1(lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyM(lean_object*, lean_object*);
lean_object* l_Array_HasRepr___rarg(lean_object*);
lean_object* l_Array_find___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_iterate_u2082___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfoldlFrom(lean_object*, lean_object*);
lean_object* l_Array_iterate_u2082(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_revIterate___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_any___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Array_mapIdx___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink(lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_mmapIdx___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_append___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_append___spec__1(lean_object*);
lean_object* l_Array_mfindRevAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_feraseIdx___rarg(lean_object*, lean_object*);
lean_object* l_Array_HasToString___rarg(lean_object*);
lean_object* l___private_init_data_array_basic_2__revIterateAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___boxed__const__1;
lean_object* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
lean_object* l_Array_mfor___boxed(lean_object*);
lean_object* l_Array_eraseIdxAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_mmap___boxed(lean_object*, lean_object*);
lean_object* l_Array_set(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_find(lean_object*, lean_object*);
lean_object* l_Array_swapAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdxSzAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_mmap___spec__1(lean_object*, lean_object*);
lean_object* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterate_u2082Aux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Array_allM___spec__1(lean_object*, lean_object*);
lean_object* l_Array_revIterate(lean_object*, lean_object*);
lean_object* l_Array_mforAux___boxed(lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_getOpt___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_allM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldl_u2082___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyM___boxed(lean_object*, lean_object*);
lean_object* l_Array_mmap(lean_object*, lean_object*);
lean_object* l_Array_mfindRevAux___main___at_Array_findRev___spec__1(lean_object*, lean_object*);
lean_object* l_Array_find___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_toList(lean_object*);
lean_object* l_Array_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOf___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_revFoldl___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverseAux(lean_object*);
lean_object* l_Array_foldl___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1(lean_object*, lean_object*);
lean_object* l_Array_isEqvAux(lean_object*);
lean_object* l_List_toArrayAux___main(lean_object*);
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg___boxed(lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_foldl___spec__1(lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_HasAppend(lean_object*);
lean_object* l_Array_modify(lean_object*);
lean_object* l_Array_mfindAux(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___boxed(lean_object*, lean_object*);
lean_object* l_Array_mkEmpty___boxed(lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateFrom___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_all___rarg(lean_object*, lean_object*);
lean_object* l_Array_fswapAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_fset___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_mmap___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_filterAux(lean_object*);
lean_object* l_Array_miterate_u2082Aux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Array_anyMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mforAux___main(lean_object*);
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
lean_object* l_Array_fget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_get___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_getOpt___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_getOpt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_getOpt___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_getOpt___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_getOpt___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_fset___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_set___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_set(x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_fswap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_fswap(x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_swap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_swap(x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_fswapAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_fswapAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_fswapAt___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_fswapAt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_fswapAt___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_swapAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = lean_array_fset(x_1, x_2, x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
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
lean_object* l_Array_miterateAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_17 = lean_alloc_closure((void*)(l_Array_miterateAux___main___rarg), 6, 5);
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
lean_object* l_Array_miterateAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterateAux___main___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Array_miterateAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_miterateAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_miterateAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_miterateAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Array_miterateAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterateAux___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Array_miterateAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_miterateAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_miterate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_miterateAux___main___rarg(x_1, lean_box(0), x_3, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Array_miterate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterate___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_miterate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_miterate(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_18 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed), 7, 6);
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
lean_object* l_Array_miterateAux___main___at_Array_mfoldl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_Array_mfoldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_7 = l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(x_1, lean_box(0), x_3, x_5, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Array_mfoldl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mfoldl___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_miterateAux___main___at_Array_mfoldl___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mfoldl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mfoldl(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_18 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg___boxed), 7, 6);
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
lean_object* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_Array_mfoldlFrom___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg(x_1, lean_box(0), x_3, x_5, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Array_mfoldlFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mfoldlFrom___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mfoldlFrom___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mfoldlFrom___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Array_mfoldlFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mfoldlFrom(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_miterate_u2082Aux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_25 = lean_alloc_closure((void*)(l_Array_miterate_u2082Aux___main___rarg), 8, 7);
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
lean_object* l_Array_miterate_u2082Aux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterate_u2082Aux___main___rarg), 8, 0);
return x_3;
}
}
lean_object* l_Array_miterate_u2082Aux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_miterate_u2082Aux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_miterate_u2082Aux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_miterate_u2082Aux___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Array_miterate_u2082Aux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterate_u2082Aux___rarg), 8, 0);
return x_3;
}
}
lean_object* l_Array_miterate_u2082Aux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_miterate_u2082Aux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_miterate_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_miterate_u2082Aux___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_7, x_8, x_6);
return x_9;
}
}
lean_object* l_Array_miterate_u2082(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterate_u2082___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Array_miterate_u2082___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_miterate_u2082(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_26 = lean_alloc_closure((void*)(l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg___boxed), 9, 8);
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
lean_object* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg___boxed), 9, 0);
return x_3;
}
}
lean_object* l_Array_mfoldl_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_9 = l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg(x_1, lean_box(0), lean_box(0), x_4, x_6, x_6, x_7, x_8, x_5);
return x_9;
}
}
lean_object* l_Array_mfoldl_u2082(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mfoldl_u2082___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
lean_object* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mfoldl_u2082___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mfoldl_u2082(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mfindAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = l_Array_mfindAux___main___rarg(x_2, lean_box(0), x_3, x_4, x_7);
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
lean_object* l_Array_mfindAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_15 = lean_alloc_closure((void*)(l_Array_mfindAux___main___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_15, 0, x_5);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
x_16 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
lean_object* l_Array_mfindAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mfindAux___main___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_mfindAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mfindAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_mfindAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mfindAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mfindAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mfindAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_mfindAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mfindAux___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_mfindAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mfindAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mfind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_mfindAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_mfind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mfind___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_mfind___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mfind(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mfindRevAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Array_mfindRevAux___main___rarg(x_1, lean_box(0), x_2, x_3, x_4, lean_box(0));
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
lean_object* l_Array_mfindRevAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_18 = lean_alloc_closure((void*)(l_Array_mfindRevAux___main___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_3);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_14);
x_19 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
}
lean_object* l_Array_mfindRevAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mfindRevAux___main___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Array_mfindRevAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mfindRevAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_mfindRevAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mfindRevAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Array_mfindRevAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mfindRevAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mfindRevAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mfindRevAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5, lean_box(0));
return x_7;
}
}
lean_object* l_Array_mfindRevAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mfindRevAux___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Array_mfindRevAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mfindRevAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Array_mfindRevAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mfindRevAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mfindRev___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_get_size(x_3);
x_6 = l_Array_mfindRevAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5, lean_box(0));
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Array_mfindRev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mfindRev___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_mfindRev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mfindRev(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Array_miterateAux___main___at_Array_iterate___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Array_iterate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(x_1, x_3, x_1, x_4, x_2);
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
lean_object* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
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
lean_object* l_Array_miterateAux___main___at_Array_iterateFrom___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Array_miterateAux___main___at_Array_iterateFrom___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Array_iterateFrom___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Array_iterateFrom___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_miterateAux___main___at_Array_iterateFrom___spec__1___rarg(x_1, x_4, x_1, x_3, x_2);
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
lean_object* l_Array_miterateAux___main___at_Array_iterateFrom___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Array_iterateFrom___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
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
lean_object* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Array_miterateAux___main___at_Array_foldl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Array_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(x_1, x_3, x_3, x_4, x_2);
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
lean_object* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
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
lean_object* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Array_foldlFrom___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg(x_1, x_3, x_3, x_4, x_2);
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
lean_object* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
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
lean_object* l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
lean_object* l_Array_iterate_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg(x_1, x_4, x_1, x_2, x_5, x_3);
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
lean_object* l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
lean_object* l_Array_foldl_u2082___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg(x_1, x_3, x_3, x_4, x_5, x_2);
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
lean_object* l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l_Array_mfindAux___main___at_Array_find___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_mfindAux___main___at_Array_find___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mfindAux___main___at_Array_find___spec__1___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_find___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_mfindAux___main___at_Array_find___spec__1___rarg(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_Array_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_find___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Array_mfindAux___main___at_Array_find___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_mfindAux___main___at_Array_find___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_find___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_find___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_mfindRevAux___main___at_Array_findRev___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_mfindRevAux___main___at_Array_findRev___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mfindRevAux___main___at_Array_findRev___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Array_findRev___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = l_Array_mfindRevAux___main___at_Array_findRev___spec__1___rarg(x_2, x_1, x_3, lean_box(0));
return x_4;
}
}
lean_object* l_Array_findRev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_findRev___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Array_mfindRevAux___main___at_Array_findRev___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_mfindRevAux___main___at_Array_findRev___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_findRev___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findRev___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_anyMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = l_Array_anyMAux___main___rarg(x_2, x_3, x_4, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* _init_l_Array_anyMAux___main___rarg___boxed__const__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box(x_1);
return x_2;
}
}
lean_object* l_Array_anyMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 0;
x_10 = l_Array_anyMAux___main___rarg___boxed__const__1;
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_array_fget(x_2, x_4);
lean_inc(x_3);
x_14 = lean_apply_1(x_3, x_13);
x_15 = lean_alloc_closure((void*)(l_Array_anyMAux___main___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
x_16 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
lean_object* l_Array_anyMAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyMAux___main___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_anyMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Array_anyMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_anyMAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_anyMAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_anyMAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_anyMAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyMAux___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_anyMAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_anyMAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyMAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
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
lean_object* l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_1, x_8);
x_10 = l_Array_anyMAux___main___at_Array_allM___spec__1___rarg(x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(x_7);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
}
lean_object* _init_l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___boxed__const__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box(x_1);
return x_2;
}
}
lean_object* l_Array_anyMAux___main___at_Array_allM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
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
x_12 = l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___boxed__const__1;
x_13 = lean_apply_2(x_10, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_array_fget(x_5, x_6);
lean_inc(x_2);
x_16 = lean_apply_1(x_2, x_15);
lean_inc(x_3);
lean_inc(x_4);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_16);
x_18 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_18, 0, x_6);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_4);
lean_closure_set(x_18, 5, x_5);
x_19 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
}
lean_object* l_Array_anyMAux___main___at_Array_allM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_Array_allM___spec__1___rarg), 6, 0);
return x_3;
}
}
uint8_t l_Array_allM___rarg___lambda__1(uint8_t x_1) {
_start:
{
if (x_1 == 0)
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
lean_object* _init_l_Array_allM___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_allM___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Array_allM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Array_allM___rarg___closed__1;
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_9 = l_Array_anyMAux___main___at_Array_allM___spec__1___rarg(x_1, x_3, x_6, x_7, x_2, x_8);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
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
lean_object* l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_anyMAux___main___at_Array_allM___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_anyMAux___main___at_Array_allM___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_allM___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Array_allM___rarg___lambda__1(x_2);
x_4 = lean_box(x_3);
return x_4;
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
uint8_t l_Array_anyMAux___main___at_Array_any___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_anyMAux___main___at_Array_any___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_Array_any___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
uint8_t l_Array_any___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_anyMAux___main___at_Array_any___spec__1___rarg(x_2, x_1, x_3);
return x_4;
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
lean_object* l_Array_anyMAux___main___at_Array_any___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Array_any___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
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
uint8_t l_Array_anyMAux___main___at_Array_all___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_anyMAux___main___at_Array_all___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_anyMAux___main___at_Array_all___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
uint8_t l_Array_all___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_anyMAux___main___at_Array_all___spec__1___rarg(x_2, x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
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
lean_object* l_Array_anyMAux___main___at_Array_all___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Array_all___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
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
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = lean_array_fget(x_1, x_9);
lean_inc(x_2);
lean_inc(x_9);
x_11 = lean_apply_3(x_2, x_9, x_10, x_5);
x_3 = x_9;
x_4 = lean_box(0);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
}
lean_object* l___private_init_data_array_basic_2__revIterateAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_init_data_array_basic_2__revIterateAux___main___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_init_data_array_basic_2__revIterateAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_init_data_array_basic_2__revIterateAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_init_data_array_basic_2__revIterateAux___main___rarg(x_1, x_2, x_3, lean_box(0), x_5);
return x_6;
}
}
lean_object* l___private_init_data_array_basic_2__revIterateAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_init_data_array_basic_2__revIterateAux___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l___private_init_data_array_basic_2__revIterateAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_init_data_array_basic_2__revIterateAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_revIterate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = l___private_init_data_array_basic_2__revIterateAux___main___rarg(x_1, x_3, x_4, lean_box(0), x_2);
return x_5;
}
}
lean_object* l_Array_revIterate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_revIterate___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_revIterate___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_revIterate___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = lean_apply_2(x_2, x_11, x_6);
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
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Array_revFoldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(x_1, x_3, x_1, x_4, lean_box(0), x_2);
return x_5;
}
}
lean_object* l_Array_revFoldl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_revFoldl___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_revFoldl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_revFoldl___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_toList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_array_get_size(x_1);
x_4 = l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___rarg(x_1, x_1, x_3, lean_box(0), x_2);
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
lean_object* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
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
x_1 = lean_alloc_closure((void*)(l_Array_toList___rarg___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Array_HasRepr___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_List_repr___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Array_HasRepr___rarg___closed__1;
x_4 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Array_HasRepr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_HasRepr___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Array_HasToString___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_List_toString___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Array_HasRepr___rarg___closed__1;
x_4 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Array_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_HasToString___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Array_ummapAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = x_6;
x_10 = lean_array_fset(x_3, x_1, x_9);
x_11 = l_Array_ummapAux___main___rarg(x_4, lean_box(0), x_5, x_8, x_10);
return x_11;
}
}
lean_object* l_Array_ummapAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_inc(x_13);
x_15 = x_14;
x_16 = lean_array_fset(x_5, x_4, x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_3);
lean_inc(x_13);
lean_inc(x_4);
x_18 = lean_apply_2(x_3, x_4, x_13);
x_19 = lean_alloc_closure((void*)(l_Array_ummapAux___main___rarg___lambda__1___boxed), 6, 5);
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
lean_object* l_Array_ummapAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_ummapAux___main___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_ummapAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_ummapAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_ummapAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_ummapAux___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_ummapAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_ummapAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_ummapAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_ummapAux___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_ummapAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_ummapAux(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = x_6;
x_10 = lean_array_fset(x_3, x_1, x_9);
x_11 = l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg(x_4, lean_box(0), x_5, x_8, x_10);
return x_11;
}
}
lean_object* l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_inc(x_13);
x_15 = x_14;
x_16 = lean_array_fset(x_5, x_4, x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_3);
lean_inc(x_13);
x_18 = lean_apply_1(x_3, x_13);
x_19 = lean_alloc_closure((void*)(l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg___lambda__1___boxed), 6, 5);
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
lean_object* l_Array_ummapAux___main___at_Array_ummap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Array_ummap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg(x_1, lean_box(0), x_3, x_5, x_4);
return x_6;
}
}
lean_object* l_Array_ummap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_ummap___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_ummapAux___main___at_Array_ummap___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_ummapAux___main___at_Array_ummap___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_ummap___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_ummap(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_ummapIdx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_ummapAux___main___rarg(x_1, lean_box(0), x_3, x_5, x_4);
return x_6;
}
}
lean_object* l_Array_ummapIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_ummapIdx___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_ummapIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_ummapIdx(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_16 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_7);
lean_inc(x_13);
x_17 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
x_20 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___boxed), 7, 6);
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
lean_object* l_Array_miterateAux___main___at_Array_mmap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_Array_mmap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_mk_empty_array_with_capacity(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_8 = l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg(x_1, lean_box(0), x_3, x_4, x_4, x_7, x_6);
return x_8;
}
}
lean_object* l_Array_mmap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mmap___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Array_miterateAux___main___at_Array_mmap___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_miterateAux___main___at_Array_mmap___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mmap___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mmap(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_miterateAux___main___at_Array_mmapIdx___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_16 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_7);
lean_inc(x_13);
x_17 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_20 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Array_mmapIdx___spec__1___rarg), 7, 6);
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
lean_object* l_Array_miterateAux___main___at_Array_mmapIdx___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Array_mmapIdx___spec__1___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Array_mmapIdx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_mk_empty_array_with_capacity(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_8 = l_Array_miterateAux___main___at_Array_mmapIdx___spec__1___rarg(x_1, lean_box(0), x_3, x_4, x_4, x_7, x_6);
return x_8;
}
}
lean_object* l_Array_mmapIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mmapIdx___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_miterateAux___main___at_Array_mmapIdx___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_miterateAux___main___at_Array_mmapIdx___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_mmapIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mmapIdx(x_1, x_2);
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
lean_object* l_Array_ummapAux___main___at_Array_mapIdx___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_inc(x_2);
x_12 = lean_apply_2(x_1, x_2, x_8);
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
lean_object* l_Array_ummapAux___main___at_Array_mapIdx___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_ummapAux___main___at_Array_mapIdx___spec__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Array_mapIdx___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_ummapAux___main___at_Array_mapIdx___spec__1___rarg(x_1, x_3, x_2);
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
lean_object* l_Array_ummapAux___main___at_Array_map___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_ummapAux___main___at_Array_map___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_ummapAux___main___at_Array_map___spec__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Array_map___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_ummapAux___main___at_Array_map___spec__1___rarg(x_1, x_3, x_2);
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
lean_object* l_Array_mforAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_array_fget(x_5, x_6);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_4);
x_16 = lean_apply_1(x_4, x_13);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_6, x_17);
x_19 = l_Array_mforAux___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_18);
lean_dec(x_18);
x_20 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_16, x_19);
return x_20;
}
}
}
lean_object* l_Array_mforAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mforAux___main___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Array_mforAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mforAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Array_mforAux___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_mforAux___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_mforAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mforAux___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Array_mforAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mforAux___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Array_mforAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mforAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Array_mforAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_mforAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_mfor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_mforAux___main___rarg(x_1, lean_box(0), lean_box(0), x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Array_mfor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mfor___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_mfor___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mfor___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Array_mfor___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_mfor(x_1);
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
lean_object* l_Array_miterateAux___main___at_Array_append___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_miterateAux___main___at_Array_append___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_miterateAux___main___at_Array_append___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_append___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_2, x_2, x_3, x_1);
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
lean_object* l_Array_miterateAux___main___at_Array_append___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_1, x_2, x_3, x_4);
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
uint8_t x_4; 
x_4 = l_Array_isEqv___rarg(x_2, x_3, x_1);
return x_4;
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
lean_object* initialize_init_data_nat_basic(lean_object*);
lean_object* initialize_init_data_fin_basic(lean_object*);
lean_object* initialize_init_data_uint(lean_object*);
lean_object* initialize_init_data_repr(lean_object*);
lean_object* initialize_init_data_tostring(lean_object*);
lean_object* initialize_init_control_id(lean_object*);
lean_object* initialize_init_util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_data_array_basic(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_nat_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_fin_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_repr(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_tostring(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_id(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_util(w);
if (lean_io_result_is_error(w)) return w;
l_Array_empty___closed__1 = _init_l_Array_empty___closed__1();
lean_mark_persistent(l_Array_empty___closed__1);
l_Array_anyMAux___main___rarg___boxed__const__1 = _init_l_Array_anyMAux___main___rarg___boxed__const__1();
lean_mark_persistent(l_Array_anyMAux___main___rarg___boxed__const__1);
l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___boxed__const__1 = _init_l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___boxed__const__1();
lean_mark_persistent(l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___boxed__const__1);
l_Array_allM___rarg___closed__1 = _init_l_Array_allM___rarg___closed__1();
lean_mark_persistent(l_Array_allM___rarg___closed__1);
l_Array_HasRepr___rarg___closed__1 = _init_l_Array_HasRepr___rarg___closed__1();
lean_mark_persistent(l_Array_HasRepr___rarg___closed__1);
l_Array_HasAppend___closed__1 = _init_l_Array_HasAppend___closed__1();
lean_mark_persistent(l_Array_HasAppend___closed__1);
return w;
}
#ifdef __cplusplus
}
#endif
