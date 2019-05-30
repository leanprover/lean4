// Lean compiler output
// Module: init.data.array.basic
// Imports: init.data.nat.basic init.data.fin.basic init.data.uint init.data.repr init.data.tostring init.control.id init.util
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_List_toArrayAux___rarg(obj*, obj*);
obj* l_Array_anyMAux___main___at_Array_any___spec__1(obj*);
obj* l_Array_extractAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Array_map___spec__1(obj*, obj*);
obj* l_Array_append(obj*);
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l_Array_foldlFrom___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_ummap___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_iterateFrom___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_shrink___main___rarg___boxed(obj*, obj*);
obj* l_Array_mforAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_toList___rarg___boxed(obj*);
obj* l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1(obj*, obj*, obj*);
obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Array_anyMAux___main___at_Array_all___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_getOpt(obj*);
obj* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1(obj*, obj*);
obj* l_Array_any(obj*);
obj* l_List_repr___rarg(obj*, obj*);
obj* l_Array_swap___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_revFoldl(obj*, obj*);
obj* l_Array_mfor___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_extract___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_miterate___boxed(obj*, obj*, obj*);
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_Array_iterate___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_mfoldl___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_iterateFrom___spec__1(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_reverse(obj*);
obj* l_Array_filter(obj*);
obj* l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfoldl_u2082___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_all___rarg___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___boxed(obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_shrink___rarg(obj*, obj*);
obj* l_Array_fswap___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_extractAux(obj*);
obj* l_Array_HasRepr(obj*);
obj* l_Array_ummapAux___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_allM___boxed(obj*, obj*);
obj* l_Array_iterate_u2082___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_back___rarg___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_append___rarg___boxed(obj*, obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterate___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_mfoldlFrom___boxed(obj*, obj*, obj*);
obj* l_Array_HasBeq(obj*);
obj* l_Array_ummapAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_ummapIdx(obj*, obj*, obj*);
obj* l_Array_size___boxed(obj*, obj*);
obj* l_Array_uset___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_iterateFrom___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_anyMAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l_Array_isEqv___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_fswapAt___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_mfoldlFrom___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_uget(obj*, obj*, usize, obj*);
obj* l_Array_anyMAux(obj*, obj*);
obj* l_Array_extractAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_uset(obj*, obj*, usize, obj*, obj*);
obj* l_Array_miterate_u2082___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_redLength___main___rarg(obj*);
obj* l_Array_fswap(obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfoldl___boxed(obj*, obj*, obj*);
obj* l_Array_mfind(obj*, obj*, obj*);
obj* l_Array_mfindAux___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_foldl___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_extractAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_swapAt(obj*);
obj* l_List_redLength___main(obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_pop___boxed(obj*, obj*);
obj* l_Array_foldlFrom___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at_Array_all___spec__1(obj*);
uint8 l_Array_isEqvAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mmapIdx___spec__1___boxed(obj*, obj*, obj*);
obj* l_List_redLength(obj*);
obj* l_Array_mkEmpty(obj*, obj*);
obj* l_Array_ummap___rarg(obj*, obj*, obj*);
obj* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_List_toArrayAux(obj*);
obj* l_Array_mkArray___boxed(obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_extract(obj*);
obj* l_Array_mfindAux___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_map___rarg(obj*, obj*);
obj* l_Array_empty(obj*);
obj* l_Array_swap(obj*, obj*, obj*, obj*);
obj* l_Array_HasEmptyc(obj*);
obj* l_Array_extractAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_List_redLength___main___rarg___boxed(obj*);
obj* l_Array_mapIdx(obj*, obj*);
obj* l_Array_toList___rarg(obj*);
obj* l_Array_uget___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Array_HasBeq___rarg(obj*, obj*, obj*);
obj* l_Array_allM(obj*, obj*);
obj* l_Array_get___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterate_u2082Aux___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_mmapIdx___rarg(obj*, obj*, obj*);
obj* l_Array_iterate(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfindAux___boxed(obj*, obj*, obj*);
obj* l_Array_mfor(obj*);
obj* l_Array_mfindAux___main___at_Array_find___spec__1(obj*, obj*);
obj* l_Array_extract___rarg(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Array_allM___rarg___lambda__1(uint8);
obj* l_Array_mfindAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_isEqv(obj*);
obj* l_Array_mfind___boxed(obj*, obj*, obj*);
obj* l_Array_mfindAux___main(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mmapIdx___spec__1(obj*, obj*, obj*);
obj* l_Array_miterateAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfindAux___main___boxed(obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main(obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_List_toString___rarg(obj*, obj*);
obj* l_Array_miterate_u2082Aux(obj*, obj*, obj*, obj*);
obj* l_Array_revFoldl___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_swapAt___rarg___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Array_miterate_u2082(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main(obj*, obj*, obj*);
obj* l_Array_mfindAux___main___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterate_u2082Aux___main(obj*, obj*, obj*, obj*);
obj* l_Array_HasBeq___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_allM___rarg___lambda__1___boxed(obj*);
obj* l_Array_foldl(obj*, obj*);
obj* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfindAux___main___at_Array_find___spec__1___rarg(obj*, obj*, obj*);
obj* l_Array_ummapAux(obj*, obj*, obj*);
obj* l_Array_anyMAux___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_filterAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_fget(obj*, obj*, obj*);
obj* l_Array_mforAux___main___boxed(obj*);
obj* l_Array_singleton___rarg(obj*);
obj* l_Array_mmapIdx___boxed(obj*, obj*, obj*);
uint8 l_Array_anyMAux___main___at_Array_all___spec__1___rarg(obj*, obj*, obj*);
obj* l_Array_filter___rarg(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1(obj*, obj*);
uint8 l_Array_isEmpty___rarg(obj*);
uint8 l_Array_any___rarg(obj*, obj*);
obj* l_Array_ummapAux___main___at_Array_mapIdx___spec__1(obj*, obj*);
obj* l_Array_push(obj*, obj*, obj*);
obj* l_Array_iterateFrom(obj*, obj*);
obj* l_Array_anyMAux___main(obj*, obj*);
obj* l_Array_mforAux___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_push___boxed(obj*, obj*, obj*);
obj* l_Array_fget___boxed(obj*, obj*, obj*);
obj* l_Array_foldl_u2082(obj*, obj*, obj*);
obj* l_Array_reverseAux___rarg(obj*, obj*);
obj* l_Array_miterate_u2082Aux___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at_Array_allM___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Array_isEqv___rarg(obj*, obj*, obj*);
obj* l_Array_map(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at_Array_any___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Array_ummap___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_mmap___rarg(obj*, obj*, obj*);
obj* l_Array_miterate_u2082___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_mfoldl_u2082(obj*, obj*, obj*, obj*);
obj* l_Array_filterAux___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_mforAux(obj*);
obj* l_Array_iterateFrom___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_back(obj*);
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Array_map___spec__1___rarg(obj*, obj*, obj*);
obj* l_Array_isEqvAux___main(obj*);
obj* l_Array_anyMAux___main___at_Array_allM___spec__1___boxed(obj*, obj*);
obj* l_Array_ummapAux___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_ummapIdx___rarg(obj*, obj*, obj*);
obj* l_Array_shrink___main(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_anyMAux___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___boxed(obj*, obj*, obj*);
obj* l_List_toArray(obj*);
obj* l_Array_getOpt___rarg(obj*, obj*);
obj* l_Array_reverseAux___main(obj*);
obj* l_Array_mfor___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_ummapIdx___boxed(obj*, obj*, obj*);
obj* l_Array_append___rarg(obj*, obj*);
obj* l_Array_sz___boxed(obj*, obj*);
obj* l_Array_Inhabited(obj*);
obj* l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1(obj*, obj*, obj*);
obj* l_Array_modify___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_revIterate___rarg(obj*, obj*, obj*);
obj* l_Array_HasRepr___rarg___closed__1;
obj* l_Array_HasToString(obj*);
obj* l_Array_singleton(obj*);
obj* l_Array_allM___rarg___closed__1;
obj* l_Array_shrink___rarg___boxed(obj*, obj*);
obj* l_Array_mapIdx___rarg(obj*, obj*);
obj* l_Array_mforAux___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_HasAppend___closed__1;
obj* l_Array_isEmpty___rarg___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1(obj*, obj*, obj*);
obj* l_Array_fswapAt(obj*);
obj* l_Array_shrink___main___rarg(obj*, obj*);
obj* l_Array_iterate___rarg(obj*, obj*, obj*);
obj* l_List_toArray___rarg(obj*);
obj* l_Array_filterAux___main(obj*);
obj* l_Array_reverseAux___main___rarg(obj*, obj*);
obj* l_Array_anyMAux___main___rarg___lambda__1(obj*, obj*, obj*, obj*, uint8);
obj* l_Array_pop(obj*, obj*);
obj* l_Array_sz(obj*, obj*);
obj* l_Array_miterateAux(obj*, obj*, obj*);
obj* l_Array_extractAux___main(obj*);
obj* l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___boxed(obj*, obj*, obj*);
obj* l_Array_mfindAux___main___at_Array_find___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_modify___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Array_mforAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_isEmpty(obj*);
obj* l_Array_mfoldl_u2082___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_all(obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Array_mmapIdx(obj*, obj*, obj*);
obj* l_Array_foldl_u2082___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_mfoldlFrom___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_Array_ummap(obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_Array_mfoldl(obj*, obj*, obj*);
obj* l_Array_mfind___rarg(obj*, obj*, obj*);
obj* l_Array_miterate(obj*, obj*, obj*);
uint8 l_Array_isEqvAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_foldlFrom(obj*, obj*);
uint8 l_Array_anyMAux___main___at_Array_any___spec__1___rarg(obj*, obj*, obj*);
obj* l_Array_anyMAux___main___boxed(obj*, obj*);
obj* l_Array_ummapAux___main___at_Array_ummap___spec__1(obj*, obj*, obj*);
obj* l_Array_isEqvAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux(obj*, obj*);
obj* l_Array_anyM(obj*, obj*);
obj* l_Array_HasRepr___rarg(obj*);
obj* l_Array_find___rarg(obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Array_iterate_u2082___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_mfoldlFrom(obj*, obj*, obj*);
obj* l_Array_iterate_u2082(obj*, obj*, obj*);
obj* l_Array_revIterate___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_any___rarg___boxed(obj*, obj*);
obj* l_Array_ummapAux___main___at_Array_mapIdx___spec__1___rarg(obj*, obj*, obj*);
obj* l_Array_shrink(obj*);
obj* l_Array_miterateAux___main___at_Array_mmapIdx___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_anyM___rarg(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_append___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_Array_isEqvAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_append___spec__1(obj*);
obj* l_Array_HasToString___rarg(obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_reverse___rarg(obj*);
obj* l_Array_mfor___boxed(obj*);
obj* l_Array_mmap___boxed(obj*, obj*, obj*);
obj* l_Array_set(obj*, obj*, obj*, obj*);
obj* l_Array_find(obj*, obj*);
obj* l_Array_swapAt___rarg(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1(obj*, obj*, obj*);
obj* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterate_u2082Aux___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_anyMAux___main___at_Array_allM___spec__1(obj*, obj*);
obj* l_Array_revIterate(obj*, obj*);
obj* l_Array_mforAux___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_getOpt___rarg___boxed(obj*, obj*);
obj* l_Array_allM___rarg(obj*, obj*, obj*);
obj* l_Array_foldl_u2082___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_anyM___boxed(obj*, obj*);
obj* l_Array_mmap(obj*, obj*, obj*);
obj* l_Array_find___rarg___boxed(obj*, obj*);
obj* l_Array_toList(obj*);
obj* l_Array_set___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_append___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_revFoldl___rarg(obj*, obj*, obj*);
obj* l_Array_reverseAux(obj*);
obj* l_Array_foldl___rarg(obj*, obj*, obj*);
obj* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1(obj*, obj*, obj*, obj*);
obj* l_Array_isEqvAux(obj*);
obj* l_List_toArrayAux___main(obj*);
obj* l_List_redLength___rarg___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1(obj*, obj*);
obj* l_Array_ummapAux___main___boxed(obj*, obj*, obj*);
obj* l_Array_HasAppend(obj*);
obj* l_Array_modify(obj*);
obj* l_Array_mfindAux(obj*, obj*, obj*);
obj* l_Array_miterateAux___boxed(obj*, obj*, obj*);
obj* l_Array_mkEmpty___boxed(obj*, obj*);
obj* l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_iterateFrom___rarg(obj*, obj*, obj*, obj*);
uint8 l_Array_all___rarg(obj*, obj*);
obj* l_Array_fswapAt___rarg(obj*, obj*, obj*);
obj* l_Array_fset___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_filterAux(obj*);
obj* l_Array_miterate_u2082Aux___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_back___rarg(obj*, obj*);
obj* l_List_redLength___rarg(obj*);
obj* l_Array_anyMAux___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_mforAux___main(obj*);
obj* l_Array_sz___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::array_sz(x_2);
return x_3;
}
}
obj* l_Array_size___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::array_get_size(x_2);
return x_3;
}
}
obj* l_Array_mkEmpty___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::mk_empty_array(x_2);
return x_3;
}
}
obj* l_Array_push___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::array_push(x_2, x_3);
return x_4;
}
}
obj* l_Array_mkArray___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::mk_array(x_2, x_3);
return x_4;
}
}
obj* _init_l_Array_empty___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::mk_empty_array(x_1);
return x_2;
}
}
obj* l_Array_empty(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
obj* l_Array_HasEmptyc(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
obj* l_Array_Inhabited(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
uint8 l_Array_isEmpty___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_isEmpty(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_isEmpty___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Array_isEmpty___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Array_isEmpty___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_Array_singleton___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(1u);
x_3 = lean::mk_array(x_2, x_1);
return x_3;
}
}
obj* l_Array_singleton(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_singleton___rarg), 1, 0);
return x_2;
}
}
obj* l_Array_fget___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::array_fget(x_2, x_3);
return x_4;
}
}
obj* l_Array_uget___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; obj* x_6; 
x_5 = lean::unbox_size_t(x_3);
x_6 = lean::array_uget(x_2, x_5);
return x_6;
}
}
obj* l_Array_get___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::array_get(x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_back___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_sub(x_3, x_4);
lean::dec(x_3);
x_6 = lean::array_get(x_1, x_2, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Array_back(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_back___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Array_back___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_back___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_getOpt___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::array_fget(x_1, x_2);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
}
obj* l_Array_getOpt(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_getOpt___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Array_getOpt___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_getOpt___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_fset___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::array_fset(x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_uset___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
usize x_6; obj* x_7; 
x_6 = lean::unbox_size_t(x_3);
x_7 = lean::array_uset(x_2, x_6, x_4);
return x_7;
}
}
obj* l_Array_set___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::array_set(x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_fswap___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::array_fswap(x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_swap___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::array_swap(x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_fswapAt___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::array_fget(x_1, x_2);
x_5 = lean::array_fset(x_1, x_2, x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_Array_fswapAt(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_fswapAt___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Array_fswapAt___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_fswapAt___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_swapAt___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; 
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::array_fget(x_1, x_2);
x_8 = lean::array_fset(x_1, x_2, x_3);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_Array_swapAt(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_swapAt___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Array_swapAt___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_swapAt___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_pop___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::array_pop(x_2);
return x_3;
}
}
obj* l_Array_shrink___main___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_le(x_3, x_2);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::array_pop(x_1);
x_1 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
obj* l_Array_shrink___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_shrink___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Array_shrink___main___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_shrink___main___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_shrink___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_shrink___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_Array_shrink(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_shrink___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Array_shrink___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_shrink___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_2);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_10 = lean::apply_2(x_9, lean::box(0), x_5);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
x_12 = lean::array_fget(x_2, x_4);
lean::inc(x_3);
lean::inc(x_4);
x_13 = lean::apply_3(x_3, x_4, x_12, x_5);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_4, x_14);
lean::dec(x_4);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___rarg), 5, 4);
lean::closure_set(x_16, 0, x_1);
lean::closure_set(x_16, 1, x_2);
lean::closure_set(x_16, 2, x_3);
lean::closure_set(x_16, 3, x_15);
x_17 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_13, x_16);
return x_17;
}
}
}
obj* l_Array_miterateAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___rarg), 5, 0);
return x_4;
}
}
obj* l_Array_miterateAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_miterateAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Array_miterateAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___rarg), 5, 0);
return x_4;
}
}
obj* l_Array_miterateAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_miterate___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterateAux___main___rarg(x_1, x_2, x_4, x_5, x_3);
return x_6;
}
}
obj* l_Array_miterate(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate___rarg), 4, 0);
return x_4;
}
}
obj* l_Array_miterate___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterate(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_4);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::apply_2(x_10, lean::box(0), x_6);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_13 = lean::array_fget(x_4, x_5);
lean::inc(x_2);
x_14 = lean::apply_2(x_2, x_6, x_13);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_add(x_5, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed), 6, 5);
lean::closure_set(x_17, 0, x_1);
lean::closure_set(x_17, 1, x_2);
lean::closure_set(x_17, 2, x_3);
lean::closure_set(x_17, 3, x_4);
lean::closure_set(x_17, 4, x_16);
x_18 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_14, x_17);
return x_18;
}
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
obj* l_Array_mfoldl___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_6 = l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(x_1, x_2, x_4, x_4, x_5, x_3);
return x_6;
}
}
obj* l_Array_mfoldl(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfoldl___rarg), 4, 0);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Array_mfoldl___spec__1(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_mfoldl___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mfoldl(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_4);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::apply_2(x_10, lean::box(0), x_6);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_13 = lean::array_fget(x_4, x_5);
lean::inc(x_2);
x_14 = lean::apply_2(x_2, x_6, x_13);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_add(x_5, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg___boxed), 6, 5);
lean::closure_set(x_17, 0, x_1);
lean::closure_set(x_17, 1, x_2);
lean::closure_set(x_17, 2, x_3);
lean::closure_set(x_17, 3, x_4);
lean::closure_set(x_17, 4, x_16);
x_18 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_14, x_17);
return x_18;
}
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
obj* l_Array_mfoldlFrom___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
lean::inc(x_4);
x_6 = l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg(x_1, x_2, x_4, x_4, x_5, x_3);
return x_6;
}
}
obj* l_Array_mfoldlFrom(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfoldlFrom___rarg___boxed), 5, 0);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_mfoldlFrom___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_mfoldlFrom___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Array_mfoldlFrom___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mfoldlFrom(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_miterate_u2082Aux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_2);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::apply_2(x_10, lean::box(0), x_6);
return x_11;
}
else
{
obj* x_12; uint8 x_13; 
x_12 = lean::array_get_size(x_3);
x_13 = lean::nat_dec_lt(x_5, x_12);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_1, 0);
lean::inc(x_14);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
lean::dec(x_14);
x_16 = lean::apply_2(x_15, lean::box(0), x_6);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_17 = lean::cnstr_get(x_1, 1);
lean::inc(x_17);
x_18 = lean::array_fget(x_2, x_5);
x_19 = lean::array_fget(x_3, x_5);
lean::inc(x_4);
lean::inc(x_5);
x_20 = lean::apply_4(x_4, x_5, x_18, x_19, x_6);
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_add(x_5, x_21);
lean::dec(x_5);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u2082Aux___main___rarg), 6, 5);
lean::closure_set(x_23, 0, x_1);
lean::closure_set(x_23, 1, x_2);
lean::closure_set(x_23, 2, x_3);
lean::closure_set(x_23, 3, x_4);
lean::closure_set(x_23, 4, x_22);
x_24 = lean::apply_4(x_17, lean::box(0), lean::box(0), x_20, x_23);
return x_24;
}
}
}
}
obj* l_Array_miterate_u2082Aux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u2082Aux___main___rarg), 6, 0);
return x_5;
}
}
obj* l_Array_miterate_u2082Aux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterate_u2082Aux___main(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Array_miterate_u2082Aux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterate_u2082Aux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l_Array_miterate_u2082Aux(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u2082Aux___rarg), 6, 0);
return x_5;
}
}
obj* l_Array_miterate_u2082Aux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterate_u2082Aux(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Array_miterate_u2082___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_miterate_u2082Aux___main___rarg(x_1, x_2, x_3, x_5, x_6, x_4);
return x_7;
}
}
obj* l_Array_miterate_u2082(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u2082___rarg), 5, 0);
return x_5;
}
}
obj* l_Array_miterate_u2082___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterate_u2082(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_4);
x_9 = lean::nat_dec_lt(x_6, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::dec(x_10);
x_12 = lean::apply_2(x_11, lean::box(0), x_7);
return x_12;
}
else
{
obj* x_13; uint8 x_14; 
x_13 = lean::array_get_size(x_5);
x_14 = lean::nat_dec_lt(x_6, x_13);
lean::dec(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_1, 0);
lean::inc(x_15);
lean::dec(x_1);
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
lean::dec(x_15);
x_17 = lean::apply_2(x_16, lean::box(0), x_7);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_18 = lean::cnstr_get(x_1, 1);
lean::inc(x_18);
x_19 = lean::array_fget(x_4, x_6);
x_20 = lean::array_fget(x_5, x_6);
lean::inc(x_2);
x_21 = lean::apply_3(x_2, x_7, x_19, x_20);
x_22 = lean::mk_nat_obj(1u);
x_23 = lean::nat_add(x_6, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg___boxed), 7, 6);
lean::closure_set(x_24, 0, x_1);
lean::closure_set(x_24, 1, x_2);
lean::closure_set(x_24, 2, x_3);
lean::closure_set(x_24, 3, x_4);
lean::closure_set(x_24, 4, x_5);
lean::closure_set(x_24, 5, x_23);
x_25 = lean::apply_4(x_18, lean::box(0), lean::box(0), x_21, x_24);
return x_25;
}
}
}
}
obj* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg___boxed), 7, 0);
return x_5;
}
}
obj* l_Array_mfoldl_u2082___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_7 = l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg(x_1, x_2, x_4, x_4, x_5, x_6, x_3);
return x_7;
}
}
obj* l_Array_mfoldl_u2082(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfoldl_u2082___rarg), 5, 0);
return x_5;
}
}
obj* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
return x_8;
}
}
obj* l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterate_u2082Aux___main___at_Array_mfoldl_u2082___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Array_mfoldl_u2082___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_mfoldl_u2082(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Array_mfindAux___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_1, x_6);
x_8 = l_Array_mfindAux___main___rarg(x_2, x_3, x_4, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::apply_2(x_10, lean::box(0), x_5);
return x_11;
}
}
}
obj* l_Array_mfindAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_4, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::box(0);
x_10 = lean::apply_2(x_8, lean::box(0), x_9);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
x_12 = lean::array_fget(x_2, x_4);
lean::inc(x_3);
x_13 = lean::apply_1(x_3, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindAux___main___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_14, 0, x_4);
lean::closure_set(x_14, 1, x_1);
lean::closure_set(x_14, 2, x_2);
lean::closure_set(x_14, 3, x_3);
x_15 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
}
obj* l_Array_mfindAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindAux___main___rarg), 4, 0);
return x_4;
}
}
obj* l_Array_mfindAux___main___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_mfindAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_mfindAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mfindAux___main(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_mfindAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_mfindAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_mfindAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindAux___rarg), 4, 0);
return x_4;
}
}
obj* l_Array_mfindAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mfindAux(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_mfind___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_mfindAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_mfind(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfind___rarg), 3, 0);
return x_4;
}
}
obj* l_Array_mfind___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mfind(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_2);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::array_fget(x_3, x_4);
lean::inc(x_2);
lean::inc(x_4);
x_9 = lean::apply_3(x_2, x_4, x_8, x_5);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Array_iterate___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(x_1, x_3, x_1, x_4, x_2);
return x_5;
}
}
obj* l_Array_iterate(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_iterate___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_iterate___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_iterate___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Array_iterateFrom___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_2);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::array_fget(x_3, x_4);
lean::inc(x_2);
lean::inc(x_4);
x_9 = lean::apply_3(x_2, x_4, x_8, x_5);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Array_iterateFrom___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_iterateFrom___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Array_iterateFrom___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Array_iterateFrom___spec__1___rarg(x_1, x_4, x_1, x_3, x_2);
return x_5;
}
}
obj* l_Array_iterateFrom(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_iterateFrom___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Array_iterateFrom___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Array_iterateFrom___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_iterateFrom___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_iterateFrom___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::array_fget(x_3, x_4);
lean::inc(x_1);
x_9 = lean::apply_2(x_1, x_5, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Array_foldl___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(x_1, x_3, x_3, x_4, x_2);
return x_5;
}
}
obj* l_Array_foldl(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_foldl___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_foldl___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_foldl___rarg(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::array_fget(x_3, x_4);
lean::inc(x_1);
x_9 = lean::apply_2(x_1, x_5, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Array_foldlFrom___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg(x_1, x_3, x_3, x_4, x_2);
return x_5;
}
}
obj* l_Array_foldlFrom(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_foldlFrom___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_foldlFrom___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_foldlFrom___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_3);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_5);
lean::dec(x_2);
return x_6;
}
else
{
obj* x_9; uint8 x_10; 
x_9 = lean::array_get_size(x_4);
x_10 = lean::nat_dec_lt(x_5, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
lean::dec(x_5);
lean::dec(x_2);
return x_6;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::array_fget(x_3, x_5);
x_12 = lean::array_fget(x_4, x_5);
lean::inc(x_2);
lean::inc(x_5);
x_13 = lean::apply_4(x_2, x_5, x_11, x_12, x_6);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_5, x_14);
lean::dec(x_5);
x_5 = x_15;
x_6 = x_13;
goto _start;
}
}
}
}
obj* l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
obj* l_Array_iterate_u2082___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg(x_1, x_4, x_1, x_2, x_5, x_3);
return x_6;
}
}
obj* l_Array_iterate_u2082(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_iterate_u2082___rarg___boxed), 4, 0);
return x_4;
}
}
obj* l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterate_u2082Aux___main___at_Array_iterate_u2082___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_7;
}
}
obj* l_Array_iterate_u2082___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_iterate_u2082___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_3);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_5);
lean::dec(x_1);
return x_6;
}
else
{
obj* x_9; uint8 x_10; 
x_9 = lean::array_get_size(x_4);
x_10 = lean::nat_dec_lt(x_5, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
lean::dec(x_5);
lean::dec(x_1);
return x_6;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::array_fget(x_3, x_5);
x_12 = lean::array_fget(x_4, x_5);
lean::inc(x_1);
x_13 = lean::apply_3(x_1, x_6, x_11, x_12);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_5, x_14);
lean::dec(x_5);
x_5 = x_15;
x_6 = x_13;
goto _start;
}
}
}
}
obj* l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
obj* l_Array_foldl_u2082___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg(x_1, x_3, x_3, x_4, x_5, x_2);
return x_6;
}
}
obj* l_Array_foldl_u2082(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_foldl_u2082___rarg___boxed), 4, 0);
return x_4;
}
}
obj* l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterate_u2082Aux___main___at_Array_foldl_u2082___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
}
obj* l_Array_foldl_u2082___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_foldl_u2082___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Array_mfindAux___main___at_Array_find___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; 
lean::dec(x_3);
lean::dec(x_1);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_8; 
x_7 = lean::array_fget(x_2, x_3);
lean::inc(x_1);
x_8 = lean::apply_1(x_1, x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_3, x_9);
lean::dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean::dec(x_3);
lean::dec(x_1);
return x_8;
}
}
}
}
obj* l_Array_mfindAux___main___at_Array_find___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindAux___main___at_Array_find___spec__1___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Array_find___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_mfindAux___main___at_Array_find___spec__1___rarg(x_2, x_1, x_3);
return x_4;
}
}
obj* l_Array_find(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_find___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_Array_mfindAux___main___at_Array_find___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mfindAux___main___at_Array_find___spec__1___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_find___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_find___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_anyMAux___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_1, x_6);
x_8 = l_Array_anyMAux___main___rarg(x_2, x_3, x_4, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::box(x_5);
x_12 = lean::apply_2(x_10, lean::box(0), x_11);
return x_12;
}
}
}
obj* l_Array_anyMAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_4, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = 0;
x_10 = lean::box(x_9);
x_11 = lean::apply_2(x_8, lean::box(0), x_10);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_13 = lean::array_fget(x_2, x_4);
lean::inc(x_3);
x_14 = lean::apply_1(x_3, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_anyMAux___main___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_15, 0, x_4);
lean::closure_set(x_15, 1, x_1);
lean::closure_set(x_15, 2, x_2);
lean::closure_set(x_15, 3, x_3);
x_16 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_14, x_15);
return x_16;
}
}
}
obj* l_Array_anyMAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_anyMAux___main___rarg), 4, 0);
return x_3;
}
}
obj* l_Array_anyMAux___main___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
lean::dec(x_5);
x_7 = l_Array_anyMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_6);
lean::dec(x_1);
return x_7;
}
}
obj* l_Array_anyMAux___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_anyMAux___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_anyMAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_anyMAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_anyMAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_anyMAux___rarg), 4, 0);
return x_3;
}
}
obj* l_Array_anyMAux___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_anyMAux(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_anyM___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_anyMAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_anyM(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_anyM___rarg), 3, 0);
return x_3;
}
}
obj* l_Array_anyM___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_anyM(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, uint8 x_7) {
_start:
{
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_1, x_8);
x_10 = l_Array_anyMAux___main___at_Array_allM___spec__1___rarg(x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::box(x_7);
x_14 = lean::apply_2(x_12, lean::box(0), x_13);
return x_14;
}
}
}
obj* l_Array_anyMAux___main___at_Array_allM___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_5);
x_8 = lean::nat_dec_lt(x_6, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = 0;
x_12 = lean::box(x_11);
x_13 = lean::apply_2(x_10, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
x_15 = lean::array_fget(x_5, x_6);
lean::inc(x_2);
x_16 = lean::apply_1(x_2, x_15);
lean::inc(x_3);
lean::inc(x_4);
x_17 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_4, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___lambda__1___boxed), 7, 6);
lean::closure_set(x_18, 0, x_6);
lean::closure_set(x_18, 1, x_1);
lean::closure_set(x_18, 2, x_2);
lean::closure_set(x_18, 3, x_3);
lean::closure_set(x_18, 4, x_4);
lean::closure_set(x_18, 5, x_5);
x_19 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
}
}
obj* l_Array_anyMAux___main___at_Array_allM___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_anyMAux___main___at_Array_allM___spec__1___rarg), 6, 0);
return x_3;
}
}
uint8 l_Array_allM___rarg___lambda__1(uint8 x_1) {
_start:
{
if (x_1 == 0)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
}
obj* _init_l_Array_allM___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_allM___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
obj* l_Array_allM___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_7 = l_Array_allM___rarg___closed__1;
x_8 = lean::mk_nat_obj(0u);
lean::inc(x_6);
x_9 = l_Array_anyMAux___main___at_Array_allM___spec__1___rarg(x_1, x_3, x_6, x_7, x_2, x_8);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_7, x_9);
return x_10;
}
}
obj* l_Array_allM(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_allM___rarg), 3, 0);
return x_3;
}
}
obj* l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_7);
lean::dec(x_7);
x_9 = l_Array_anyMAux___main___at_Array_allM___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean::dec(x_1);
return x_9;
}
}
obj* l_Array_anyMAux___main___at_Array_allM___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_anyMAux___main___at_Array_allM___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_allM___rarg___lambda__1___boxed(obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox(x_1);
lean::dec(x_1);
x_3 = l_Array_allM___rarg___lambda__1(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Array_allM___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_allM(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
uint8 l_Array_anyMAux___main___at_Array_any___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_3);
lean::dec(x_1);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::array_fget(x_2, x_3);
lean::inc(x_1);
x_8 = lean::apply_1(x_1, x_7);
x_9 = lean::unbox(x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; uint8 x_12; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
lean::dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean::dec(x_3);
lean::dec(x_1);
return x_9;
}
}
}
}
obj* l_Array_anyMAux___main___at_Array_any___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_anyMAux___main___at_Array_any___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
uint8 l_Array_any___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_anyMAux___main___at_Array_any___spec__1___rarg(x_2, x_1, x_3);
return x_4;
}
}
obj* l_Array_any(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_any___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Array_anyMAux___main___at_Array_any___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyMAux___main___at_Array_any___spec__1___rarg(x_1, x_2, x_3);
lean::dec(x_2);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Array_any___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_any___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Array_anyMAux___main___at_Array_all___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_6; 
lean::dec(x_3);
lean::dec(x_1);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::array_fget(x_2, x_3);
lean::inc(x_1);
x_8 = lean::apply_1(x_1, x_7);
x_9 = lean::unbox(x_8);
lean::dec(x_8);
if (x_9 == 0)
{
uint8 x_10; 
lean::dec(x_3);
lean::dec(x_1);
x_10 = 1;
return x_10;
}
else
{
obj* x_11; obj* x_12; uint8 x_13; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_3, x_11);
lean::dec(x_3);
x_3 = x_12;
goto _start;
}
}
}
}
obj* l_Array_anyMAux___main___at_Array_all___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_anyMAux___main___at_Array_all___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
uint8 l_Array_all___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_anyMAux___main___at_Array_all___spec__1___rarg(x_2, x_1, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
}
}
obj* l_Array_all(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_all___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Array_anyMAux___main___at_Array_all___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyMAux___main___at_Array_all___spec__1___rarg(x_1, x_2, x_3);
lean::dec(x_2);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Array_all___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_all___rarg(x_1, x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_3, x_8);
lean::dec(x_3);
x_10 = lean::array_fget(x_1, x_9);
lean::inc(x_2);
lean::inc(x_9);
x_11 = lean::apply_3(x_2, x_9, x_10, x_5);
x_3 = x_9;
x_4 = lean::box(0);
x_5 = x_11;
goto _start;
}
else
{
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__revIterateAux___main___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_array_basic_1__revIterateAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_array_basic_1__revIterateAux___main___rarg(x_1, x_2, x_3, lean::box(0), x_5);
return x_6;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__revIterateAux___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_array_basic_1__revIterateAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_revIterate___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = l___private_init_data_array_basic_1__revIterateAux___main___rarg(x_1, x_3, x_4, lean::box(0), x_2);
return x_5;
}
}
obj* l_Array_revIterate(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_revIterate___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Array_revIterate___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_revIterate___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_4, x_9);
lean::dec(x_4);
x_11 = lean::array_fget(x_3, x_10);
lean::inc(x_2);
x_12 = lean::apply_2(x_2, x_11, x_6);
x_4 = x_10;
x_5 = lean::box(0);
x_6 = x_12;
goto _start;
}
else
{
lean::dec(x_4);
lean::dec(x_2);
return x_6;
}
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_Array_revFoldl___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(x_1, x_3, x_1, x_4, lean::box(0), x_2);
return x_5;
}
}
obj* l_Array_revFoldl(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_revFoldl___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
lean::dec(x_1);
return x_7;
}
}
obj* l_Array_revFoldl___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_revFoldl___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_3, x_8);
lean::dec(x_3);
x_10 = lean::array_fget(x_2, x_9);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_5);
x_3 = x_9;
x_4 = lean::box(0);
x_5 = x_11;
goto _start;
}
else
{
lean::dec(x_3);
return x_5;
}
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_toList___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box(0);
x_3 = lean::array_get_size(x_1);
x_4 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg(x_1, x_1, x_3, lean::box(0), x_2);
return x_4;
}
}
obj* l_Array_toList(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_toList___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_toList___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_toList___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Array_HasRepr___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_toList___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Array_HasRepr___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_repr___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = l_Array_HasRepr___rarg___closed__1;
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Array_HasRepr(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_HasRepr___rarg), 1, 0);
return x_2;
}
}
obj* l_Array_HasToString___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toString___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = l_Array_HasRepr___rarg___closed__1;
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Array_HasToString(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_HasToString___rarg), 1, 0);
return x_2;
}
}
obj* l_Array_ummapAux___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_1, x_7);
x_9 = x_6;
x_10 = lean::array_fset(x_3, x_1, x_9);
x_11 = l_Array_ummapAux___main___rarg(x_4, x_5, x_8, x_10);
return x_11;
}
}
obj* l_Array_ummapAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = l_Array_empty___closed__1;
x_10 = x_4;
x_11 = lean::apply_2(x_8, lean::box(0), x_10);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::array_fget(x_4, x_3);
x_13 = lean::box(0);
lean::inc(x_12);
x_14 = x_13;
x_15 = lean::array_fset(x_4, x_3, x_14);
x_16 = lean::cnstr_get(x_1, 1);
lean::inc(x_16);
lean::inc(x_2);
lean::inc(x_12);
lean::inc(x_3);
x_17 = lean::apply_2(x_2, x_3, x_12);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_18, 0, x_3);
lean::closure_set(x_18, 1, x_12);
lean::closure_set(x_18, 2, x_15);
lean::closure_set(x_18, 3, x_1);
lean::closure_set(x_18, 4, x_2);
x_19 = lean::apply_4(x_16, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
}
}
obj* l_Array_ummapAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___rarg), 4, 0);
return x_4;
}
}
obj* l_Array_ummapAux___main___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_ummapAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
return x_7;
}
}
obj* l_Array_ummapAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_ummapAux___main(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_ummapAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_ummapAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_ummapAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___rarg), 4, 0);
return x_4;
}
}
obj* l_Array_ummapAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_ummapAux(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_1, x_7);
x_9 = x_6;
x_10 = lean::array_fset(x_3, x_1, x_9);
x_11 = l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg(x_4, x_5, x_8, x_10);
return x_11;
}
}
obj* l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = l_Array_empty___closed__1;
x_10 = x_4;
x_11 = lean::apply_2(x_8, lean::box(0), x_10);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::array_fget(x_4, x_3);
x_13 = lean::box(0);
lean::inc(x_12);
x_14 = x_13;
x_15 = lean::array_fset(x_4, x_3, x_14);
x_16 = lean::cnstr_get(x_1, 1);
lean::inc(x_16);
lean::inc(x_2);
lean::inc(x_12);
x_17 = lean::apply_1(x_2, x_12);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_18, 0, x_3);
lean::closure_set(x_18, 1, x_12);
lean::closure_set(x_18, 2, x_15);
lean::closure_set(x_18, 3, x_1);
lean::closure_set(x_18, 4, x_2);
x_19 = lean::apply_4(x_16, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
}
}
obj* l_Array_ummapAux___main___at_Array_ummap___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg), 4, 0);
return x_4;
}
}
obj* l_Array_ummap___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_Array_ummap(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummap___rarg), 3, 0);
return x_4;
}
}
obj* l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_ummapAux___main___at_Array_ummap___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
return x_7;
}
}
obj* l_Array_ummapAux___main___at_Array_ummap___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_ummapAux___main___at_Array_ummap___spec__1(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_ummap___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_ummap(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_ummapIdx___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_ummapAux___main___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_Array_ummapIdx(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapIdx___rarg), 3, 0);
return x_4;
}
}
obj* l_Array_ummapIdx___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_ummapIdx(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::array_push(x_2, x_3);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_4);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::apply_2(x_10, lean::box(0), x_6);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_13 = lean::array_fget(x_4, x_5);
lean::inc(x_2);
x_14 = lean::apply_1(x_2, x_13);
lean::inc(x_1);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___lambda__1), 3, 2);
lean::closure_set(x_15, 0, x_1);
lean::closure_set(x_15, 1, x_6);
lean::inc(x_12);
x_16 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_14, x_15);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_add(x_5, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___boxed), 6, 5);
lean::closure_set(x_19, 0, x_1);
lean::closure_set(x_19, 1, x_2);
lean::closure_set(x_19, 2, x_3);
lean::closure_set(x_19, 3, x_4);
lean::closure_set(x_19, 4, x_18);
x_20 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_16, x_19);
return x_20;
}
}
}
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
obj* l_Array_mmap___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::mk_empty_array(x_4);
lean::dec(x_4);
x_6 = lean::mk_nat_obj(0u);
lean::inc(x_3);
x_7 = l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg(x_1, x_2, x_3, x_3, x_6, x_5);
return x_7;
}
}
obj* l_Array_mmap(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mmap___rarg), 3, 0);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Array_mmap___spec__1(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_mmap___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mmap(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Array_mmapIdx___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_4);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::apply_2(x_10, lean::box(0), x_6);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_13 = lean::array_fget(x_4, x_5);
lean::inc(x_2);
lean::inc(x_5);
x_14 = lean::apply_2(x_2, x_5, x_13);
lean::inc(x_1);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___lambda__1), 3, 2);
lean::closure_set(x_15, 0, x_1);
lean::closure_set(x_15, 1, x_6);
lean::inc(x_12);
x_16 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_14, x_15);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_add(x_5, x_17);
lean::dec(x_5);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mmapIdx___spec__1___rarg), 6, 5);
lean::closure_set(x_19, 0, x_1);
lean::closure_set(x_19, 1, x_2);
lean::closure_set(x_19, 2, x_3);
lean::closure_set(x_19, 3, x_4);
lean::closure_set(x_19, 4, x_18);
x_20 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_16, x_19);
return x_20;
}
}
}
obj* l_Array_miterateAux___main___at_Array_mmapIdx___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mmapIdx___spec__1___rarg), 6, 0);
return x_4;
}
}
obj* l_Array_mmapIdx___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::mk_empty_array(x_4);
lean::dec(x_4);
x_6 = lean::mk_nat_obj(0u);
lean::inc(x_3);
x_7 = l_Array_miterateAux___main___at_Array_mmapIdx___spec__1___rarg(x_1, x_2, x_3, x_3, x_6, x_5);
return x_7;
}
}
obj* l_Array_mmapIdx(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mmapIdx___rarg), 3, 0);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Array_mmapIdx___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Array_mmapIdx___spec__1(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_mmapIdx___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mmapIdx(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_modify___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_2;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = lean::array_fset(x_2, x_3, x_1);
x_9 = lean::apply_1(x_4, x_7);
x_10 = lean::array_fset(x_8, x_3, x_9);
return x_10;
}
}
}
obj* l_Array_modify(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_modify___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Array_modify___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_modify___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Array_ummapAux___main___at_Array_mapIdx___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_2);
lean::dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_8 = lean::array_fget(x_3, x_2);
x_9 = lean::box(0);
lean::inc(x_8);
x_10 = x_9;
x_11 = lean::array_fset(x_3, x_2, x_10);
lean::inc(x_1);
lean::inc(x_8);
lean::inc(x_2);
x_12 = lean::apply_2(x_1, x_2, x_8);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean::array_fset(x_11, x_2, x_15);
lean::dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
obj* l_Array_ummapAux___main___at_Array_mapIdx___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_Array_mapIdx___spec__1___rarg), 3, 0);
return x_3;
}
}
obj* l_Array_mapIdx___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_ummapAux___main___at_Array_mapIdx___spec__1___rarg(x_1, x_3, x_2);
return x_4;
}
}
obj* l_Array_mapIdx(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mapIdx___rarg), 2, 0);
return x_3;
}
}
obj* l_Array_ummapAux___main___at_Array_map___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_2);
lean::dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_8 = lean::array_fget(x_3, x_2);
x_9 = lean::box(0);
lean::inc(x_8);
x_10 = x_9;
x_11 = lean::array_fset(x_3, x_2, x_10);
lean::inc(x_1);
lean::inc(x_8);
x_12 = lean::apply_1(x_1, x_8);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean::array_fset(x_11, x_2, x_15);
lean::dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
obj* l_Array_ummapAux___main___at_Array_map___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_Array_map___spec__1___rarg), 3, 0);
return x_3;
}
}
obj* l_Array_map___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_ummapAux___main___at_Array_map___spec__1___rarg(x_1, x_3, x_2);
return x_4;
}
}
obj* l_Array_map(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_map___rarg), 2, 0);
return x_3;
}
}
obj* l_Array_mforAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_5);
x_8 = lean::nat_dec_lt(x_6, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_4);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::box(0);
x_12 = lean::apply_2(x_10, lean::box(0), x_11);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::array_fget(x_5, x_6);
x_14 = lean::cnstr_get(x_1, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_14, 4);
lean::inc(x_15);
lean::dec(x_14);
lean::inc(x_4);
x_16 = lean::apply_1(x_4, x_13);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_add(x_6, x_17);
x_19 = l_Array_mforAux___main___rarg(x_1, lean::box(0), lean::box(0), x_4, x_5, x_18);
lean::dec(x_18);
x_20 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_16, x_19);
return x_20;
}
}
}
obj* l_Array_mforAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mforAux___main___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Array_mforAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_mforAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
return x_7;
}
}
obj* l_Array_mforAux___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_mforAux___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_mforAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_mforAux___main___rarg(x_1, lean::box(0), lean::box(0), x_4, x_5, x_6);
return x_7;
}
}
obj* l_Array_mforAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mforAux___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Array_mforAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_mforAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
return x_7;
}
}
obj* l_Array_mforAux___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_mforAux(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_mfor___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_mforAux___main___rarg(x_1, lean::box(0), lean::box(0), x_4, x_5, x_6);
return x_7;
}
}
obj* l_Array_mfor(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfor___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_mfor___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_mfor___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Array_mfor___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_mfor(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_extractAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = lean::nat_dec_lt(x_2, x_3);
if (x_6 == 0)
{
lean::dec(x_2);
return x_5;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_2, x_7);
x_9 = lean::array_fget(x_1, x_2);
lean::dec(x_2);
x_10 = lean::array_push(x_5, x_9);
x_2 = x_8;
x_4 = lean::box(0);
x_5 = x_10;
goto _start;
}
}
}
obj* l_Array_extractAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_extractAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_extractAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_extractAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_extractAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_extractAux___main___rarg(x_1, x_2, x_3, lean::box(0), x_5);
return x_6;
}
}
obj* l_Array_extractAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_extractAux___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_extractAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_extractAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_extract___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::nat_sub(x_3, x_2);
x_5 = lean::mk_empty_array(x_4);
lean::dec(x_4);
x_6 = lean::array_get_size(x_1);
x_7 = lean::nat_dec_le(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_2);
return x_5;
}
else
{
obj* x_8; 
x_8 = l_Array_extractAux___main___rarg(x_1, x_2, x_3, lean::box(0), x_5);
return x_8;
}
}
}
obj* l_Array_extract(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_extract___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Array_extract___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_extract___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Array_append___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = lean::array_push(x_4, x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_3, x_9);
lean::dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Array_append___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_append___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Array_append___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_2, x_2, x_3, x_1);
return x_4;
}
}
obj* l_Array_append(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_append___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Array_append___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_append___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_append___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Array_HasAppend___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_append___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Array_HasAppend(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_HasAppend___closed__1;
return x_2;
}
}
uint8 l_Array_isEqvAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_1);
x_7 = lean::nat_dec_lt(x_5, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
uint8 x_8; 
lean::dec(x_5);
lean::dec(x_4);
x_8 = 1;
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_9 = lean::array_fget(x_1, x_5);
x_10 = lean::array_fget(x_2, x_5);
lean::inc(x_4);
x_11 = lean::apply_2(x_4, x_9, x_10);
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
uint8 x_13; 
lean::dec(x_5);
lean::dec(x_4);
x_13 = 0;
return x_13;
}
else
{
obj* x_14; obj* x_15; uint8 x_16; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_5, x_14);
lean::dec(x_5);
x_3 = lean::box(0);
x_5 = x_15;
goto _start;
}
}
}
}
obj* l_Array_isEqvAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_isEqvAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_isEqvAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = l_Array_isEqvAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::box(x_6);
return x_7;
}
}
uint8 l_Array_isEqvAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = l_Array_isEqvAux___main___rarg(x_1, x_2, lean::box(0), x_4, x_5);
return x_6;
}
}
obj* l_Array_isEqvAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_isEqvAux___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_isEqvAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = l_Array_isEqvAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::box(x_6);
return x_7;
}
}
uint8 l_Array_isEqv___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_eq(x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
if (x_6 == 0)
{
uint8 x_7; 
lean::dec(x_3);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_isEqvAux___main___rarg(x_1, x_2, lean::box(0), x_3, x_8);
return x_9;
}
}
}
obj* l_Array_isEqv(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_isEqv___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Array_isEqv___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_isEqv___rarg(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_Array_HasBeq___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_Array_isEqv___rarg(x_2, x_3, x_1);
return x_4;
}
}
obj* l_Array_HasBeq(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_HasBeq___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Array_HasBeq___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_HasBeq___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Array_reverseAux___main___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::mk_nat_obj(2u);
x_5 = lean::nat_div(x_3, x_4);
x_6 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::nat_sub(x_3, x_2);
lean::dec(x_3);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_7, x_8);
lean::dec(x_7);
x_10 = lean::array_swap(x_1, x_2, x_9);
lean::dec(x_9);
x_11 = lean::nat_add(x_2, x_8);
lean::dec(x_2);
x_1 = x_10;
x_2 = x_11;
goto _start;
}
}
}
obj* l_Array_reverseAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_reverseAux___main___rarg), 2, 0);
return x_2;
}
}
obj* l_Array_reverseAux___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_reverseAux___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_Array_reverseAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_reverseAux___rarg), 2, 0);
return x_2;
}
}
obj* l_Array_reverse___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Array_reverseAux___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_Array_reverse(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_reverse___rarg), 1, 0);
return x_2;
}
}
obj* l_Array_filterAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; 
lean::dec(x_3);
lean::dec(x_1);
x_7 = l_Array_shrink___main___rarg(x_2, x_4);
lean::dec(x_4);
return x_7;
}
else
{
obj* x_8; obj* x_9; uint8 x_10; 
x_8 = lean::array_fget(x_2, x_3);
lean::inc(x_1);
x_9 = lean::apply_1(x_1, x_8);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_3, x_11);
lean::dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
uint8 x_14; 
x_14 = lean::nat_dec_lt(x_4, x_3);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_add(x_3, x_15);
lean::dec(x_3);
x_17 = lean::nat_add(x_4, x_15);
lean::dec(x_4);
x_3 = x_16;
x_4 = x_17;
goto _start;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_19 = lean::array_fswap(x_2, x_3, x_4);
x_20 = lean::mk_nat_obj(1u);
x_21 = lean::nat_add(x_3, x_20);
lean::dec(x_3);
x_22 = lean::nat_add(x_4, x_20);
lean::dec(x_4);
x_2 = x_19;
x_3 = x_21;
x_4 = x_22;
goto _start;
}
}
}
}
}
obj* l_Array_filterAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_filterAux___main___rarg), 4, 0);
return x_2;
}
}
obj* l_Array_filterAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_filterAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_filterAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_filterAux___rarg), 4, 0);
return x_2;
}
}
obj* l_Array_filter___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l_Array_filterAux___main___rarg(x_1, x_2, x_3, x_3);
return x_4;
}
}
obj* l_Array_filter(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_filter___rarg), 2, 0);
return x_2;
}
}
obj* l_List_toArrayAux___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::array_push(x_2, x_3);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
}
}
obj* l_List_toArrayAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toArrayAux___main___rarg), 2, 0);
return x_2;
}
}
obj* l_List_toArrayAux___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_toArrayAux___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_toArrayAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toArrayAux___rarg), 2, 0);
return x_2;
}
}
obj* l_List_redLength___main___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::mk_nat_obj(0u);
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_List_redLength___main___rarg(x_3);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_add(x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
}
obj* l_List_redLength___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_redLength___main___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_List_redLength___main___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_redLength___main___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_redLength___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_redLength___main___rarg(x_1);
return x_2;
}
}
obj* l_List_redLength(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_redLength___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_List_redLength___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_redLength___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_toArray___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_List_redLength___main___rarg(x_1);
x_3 = lean::mk_empty_array(x_2);
lean::dec(x_2);
x_4 = l_List_toArrayAux___main___rarg(x_1, x_3);
return x_4;
}
}
obj* l_List_toArray(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toArray___rarg), 1, 0);
return x_2;
}
}
obj* initialize_init_data_nat_basic(obj*);
obj* initialize_init_data_fin_basic(obj*);
obj* initialize_init_data_uint(obj*);
obj* initialize_init_data_repr(obj*);
obj* initialize_init_data_tostring(obj*);
obj* initialize_init_control_id(obj*);
obj* initialize_init_util(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_array_basic(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_nat_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_fin_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_repr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_tostring(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_id(w);
if (io_result_is_error(w)) return w;
w = initialize_init_util(w);
if (io_result_is_error(w)) return w;
l_Array_empty___closed__1 = _init_l_Array_empty___closed__1();
lean::mark_persistent(l_Array_empty___closed__1);
l_Array_allM___rarg___closed__1 = _init_l_Array_allM___rarg___closed__1();
lean::mark_persistent(l_Array_allM___rarg___closed__1);
l_Array_HasRepr___rarg___closed__1 = _init_l_Array_HasRepr___rarg___closed__1();
lean::mark_persistent(l_Array_HasRepr___rarg___closed__1);
l_Array_HasAppend___closed__1 = _init_l_Array_HasAppend___closed__1();
lean::mark_persistent(l_Array_HasAppend___closed__1);
return w;
}
