// Lean compiler output
// Module: init.data.array.basic
// Imports: init.data.nat.basic init.data.fin.basic init.data.uint init.data.repr init.data.tostring init.control.id
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
obj* l_Array_extractAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_append(obj*);
obj* l_Array_foldlFrom___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_append___spec__1___boxed(obj*);
obj* l_Array_hmmapAux___main___at_Array_hmapIdx___spec__1(obj*);
obj* l_Array_shrink___main___rarg___boxed(obj*, obj*);
obj* l_Array_hmap(obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Array_foldl_u_2082___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_hmmap___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_toList___rarg___boxed(obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Array_foldl_u_2082___spec__1(obj*, obj*);
obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Array_getOpt(obj*);
obj* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1(obj*, obj*);
obj* l_Array_any(obj*);
obj* l_List_repr___rarg(obj*, obj*);
obj* l_Array_update___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_swap___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_revFoldl(obj*, obj*);
obj* l_Array_back___boxed(obj*);
obj* l_Array_extract___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_miterate___boxed(obj*, obj*, obj*);
uint8 l_Array_anyAux___rarg(obj*, obj*, obj*);
obj* l_Array_isEmpty___boxed(obj*);
obj* l_Array_iterate___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_mfoldl___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_reverse(obj*);
obj* l_Array_hmmapAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfoldl_u_2082___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_all___rarg___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___boxed(obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_shrink___rarg(obj*, obj*);
obj* l_Array_fswap___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Array_hmapIdx___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_any___boxed(obj*);
obj* l_Array_extractAux(obj*);
obj* l_Array_HasRepr(obj*);
obj* l_Array_singleton___boxed(obj*);
obj* l_Array_anyAux___main___at_Array_all___spec__1(obj*);
obj* l_Array_hmmapAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_iterate_u_2082___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_back___rarg___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_append___rarg___boxed(obj*, obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterate___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfoldlFrom___boxed(obj*, obj*, obj*);
obj* l_Array_HasBeq(obj*);
obj* l_Array_iterate___boxed(obj*, obj*);
obj* l_Array_size___boxed(obj*, obj*);
obj* l_Array_isEqvAux___main___boxed(obj*);
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l_Array_isEqv___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_mfoldlFrom___rarg(obj*, obj*, obj*, obj*, obj*);
uint8 l_Array_anyAux___main___at_Array_all___spec__1___rarg(obj*, obj*, obj*);
obj* l_Array_extractAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterate_u_2082___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Array_hmap___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_List_redLength___main___rarg(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfoldl___boxed(obj*, obj*, obj*);
obj* l_Array_mfind(obj*, obj*, obj*);
obj* l_Array_mfindAux___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_foldl___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_extractAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Array_hmmap___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_hmmap(obj*, obj*);
obj* l_List_redLength___main(obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_pop___boxed(obj*, obj*);
obj* l_Array_foldlFrom___rarg___boxed(obj*, obj*, obj*, obj*);
uint8 l_Array_isEqvAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Array_hmap___spec__1___boxed(obj*);
obj* l_Array_Inhabited___boxed(obj*);
obj* l_List_redLength(obj*);
obj* l_List_toArrayAux___main___boxed(obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Array_mfoldl_u_2082___spec__1___boxed(obj*, obj*, obj*);
obj* l_List_toArrayAux(obj*);
obj* l_Array_miterateAux___main___at_Array_map___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mkArray___boxed(obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_extract(obj*);
obj* l_Array_toList___boxed(obj*);
obj* l_Array_all___boxed(obj*);
obj* l_Array_mfindAux___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_map___rarg(obj*, obj*);
obj* l_Array_empty(obj*);
obj* l_Array_HasEmptyc(obj*);
obj* l_Array_extractAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_reverseAux___boxed(obj*);
obj* l_List_redLength___main___rarg___boxed(obj*);
obj* l_Array_toList___rarg(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Array_HasBeq___rarg(obj*, obj*, obj*);
obj* l_Array_hmapIdx(obj*);
obj* l_Array_get___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterate_u_2082Aux___boxed(obj*, obj*, obj*);
obj* l_Array_iterate(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfindAux___boxed(obj*, obj*, obj*);
obj* l_Array_reverseAux___main___boxed(obj*);
obj* l_Array_mfindAux___main___at_Array_find___spec__1(obj*, obj*);
obj* l_Array_extract___rarg(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main(obj*, obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Array_iterate_u_2082___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfindAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_anyAux(obj*);
obj* l_Array_isEqv(obj*);
obj* l_Array_mfind___boxed(obj*, obj*, obj*);
obj* l_Array_mfindAux___main(obj*, obj*, obj*);
obj* l_Array_miterateAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfindAux___main___boxed(obj*, obj*, obj*);
obj* l_Array_mfindAux___main___at_Array_find___spec__1___boxed(obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main(obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_List_toString___rarg(obj*, obj*);
obj* l_Array_miterate_u_2082Aux(obj*, obj*, obj*);
obj* l_Array_revIterate___boxed(obj*, obj*);
obj* l_Array_revFoldl___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Array_miterate_u_2082(obj*, obj*, obj*);
obj* l_Array_miterateAux___main(obj*, obj*, obj*);
obj* l_Array_mfindAux___main___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterate_u_2082Aux___main(obj*, obj*, obj*);
obj* l_Array_HasBeq___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_foldl(obj*, obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Array_mfoldl_u_2082___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfindAux___main___at_Array_find___spec__1___rarg(obj*, obj*, obj*);
obj* l_Array_hmap___rarg(obj*, obj*, obj*);
obj* l_Array_append___boxed(obj*);
obj* l_Array_hmmapAux___main___at_Array_hmmap___spec__1(obj*, obj*);
obj* l_Array_foldl___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_singleton___rarg(obj*);
obj* l_Array_HasEmptyc___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___boxed(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Array_hmmapAux___main___at_Array_hmmap___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_iterate_u_2082___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1(obj*, obj*);
obj* l_Array_extractAux___main___boxed(obj*);
obj* l_Array_isEqvAux___boxed(obj*);
uint8 l_Array_isEmpty___rarg(obj*);
uint8 l_Array_any___rarg(obj*, obj*);
obj* l_Array_map___rarg___boxed(obj*, obj*);
obj* l_Array_push___boxed(obj*, obj*, obj*);
uint8 l_Array_anyAux___main___rarg(obj*, obj*, obj*);
obj* l_Array_foldl_u_2082(obj*, obj*);
obj* l_Array_reverseAux___rarg(obj*, obj*);
obj* l_Array_miterate_u_2082Aux___main___boxed(obj*, obj*, obj*);
obj* l_Array_anyAux___boxed(obj*);
uint8 l_Array_isEqv___rarg(obj*, obj*, obj*);
obj* l_Array_map(obj*, obj*);
obj* l_Array_map___boxed(obj*, obj*);
obj* l_Array_hmap___boxed(obj*);
obj* l_Array_foldl_u_2082___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mmap___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___boxed(obj*, obj*);
obj* l_Array_miterate_u_2082___boxed(obj*, obj*, obj*);
obj* l_Array_mfoldl_u_2082(obj*, obj*, obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Array_foldl_u_2082___spec__1___boxed(obj*, obj*);
obj* l_Array_back(obj*);
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___lambda__1(obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___boxed(obj*);
obj* l_Array_isEqvAux___main(obj*);
obj* l_Array_shrink___main(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___boxed(obj*, obj*, obj*);
obj* l_List_toArray(obj*);
obj* l_List_redLength___boxed(obj*);
obj* l_Array_getOpt___rarg(obj*, obj*);
obj* l_Array_reverseAux___main(obj*);
obj* l_Array_hmmapAux___main___at_Array_hmap___spec__1(obj*);
obj* l_List_toArrayAux___boxed(obj*);
obj* l_Array_hmmapAux___main___at_Array_hmapIdx___spec__1___boxed(obj*);
obj* l_Array_append___rarg(obj*, obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Array_iterate_u_2082___spec__1___boxed(obj*, obj*);
obj* l_Array_mmap___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_anyAux___main___at_Array_all___spec__1___boxed(obj*);
obj* l_Array_Inhabited(obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Array_iterate_u_2082___spec__1(obj*, obj*);
obj* l_Array_modify___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_revIterate___rarg(obj*, obj*, obj*);
obj* l_Array_HasRepr___rarg___closed__1;
obj* l_Array_HasToString(obj*);
obj* l_Array_singleton(obj*);
obj* l_Array_shrink___rarg___boxed(obj*, obj*);
obj* l_Array_updt___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_toArray___boxed(obj*);
obj* l_Array_hmapIdx___boxed(obj*);
obj* l_Array_HasAppend___closed__1;
obj* l_Array_isEmpty___rarg___boxed(obj*);
obj* l_Array_isEqv___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Array_hmmap___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_shrink___main___rarg(obj*, obj*);
obj* l_Array_iterate___rarg(obj*, obj*, obj*);
obj* l_Array_hmmapAux___boxed(obj*, obj*);
obj* l_Array_shrink___boxed(obj*);
obj* l_List_toArray___rarg(obj*);
obj* l_Array_empty___boxed(obj*);
obj* l_Array_reverseAux___main___rarg(obj*, obj*);
obj* l_Array_HasToString___boxed(obj*);
obj* l_List_redLength___main___boxed(obj*);
obj* l_Array_anyAux___main(obj*);
obj* l_Array_miterateAux(obj*, obj*, obj*);
obj* l_Array_anyAux___main___boxed(obj*);
obj* l_Array_extractAux___main(obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Array_iterate_u_2082___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Array_hmmap___spec__1___boxed(obj*, obj*);
obj* l_Array_modify___boxed(obj*);
obj* l_Array_mfindAux___main___at_Array_find___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_modify___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_map___spec__1(obj*, obj*);
obj* l_Array_isEmpty(obj*);
obj* l_Array_mfoldl_u_2082___boxed(obj*, obj*, obj*);
obj* l_Array_all(obj*);
obj* l_Array_hmmapAux(obj*, obj*);
obj* l_Array_reverse___boxed(obj*);
obj* l_Array_foldl_u_2082___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_mfoldlFrom___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_anyAux___main___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_HasAppend___boxed(obj*);
obj* l_Array_mfoldl(obj*, obj*, obj*);
obj* l_Array_anyAux___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_mfind___rarg(obj*, obj*, obj*);
obj* l_Array_miterate(obj*, obj*, obj*);
obj* l_Array_index___boxed(obj*, obj*, obj*);
obj* l_Array_revFoldl___boxed(obj*, obj*);
uint8 l_Array_isEqvAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_foldlFrom(obj*, obj*);
obj* l_Array_isEqvAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_HasRepr___boxed(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux(obj*, obj*);
obj* l_Array_extract___boxed(obj*);
obj* l_Array_hmmapAux___main___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_HasRepr___rarg(obj*);
obj* l_Array_find___rarg(obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Array_iterate_u_2082___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_mfoldlFrom(obj*, obj*, obj*);
obj* l_Array_iterate_u_2082(obj*, obj*);
obj* l_Array_revIterate___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_any___rarg___boxed(obj*, obj*);
obj* l_Array_hmapIdx___rarg(obj*, obj*, obj*);
obj* l_Array_getOpt___boxed(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___boxed(obj*, obj*);
obj* l_Array_shrink(obj*);
obj* l_Array_miterateAux___main___at_Array_append___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_Array_isEqvAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_append___spec__1(obj*);
obj* l_Array_hmmap___boxed(obj*, obj*);
obj* l_Array_HasToString___rarg(obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_reverse___rarg(obj*);
obj* l_Array_mmap___boxed(obj*, obj*);
obj* l_Array_shrink___main___boxed(obj*);
obj* l_Array_find(obj*, obj*);
obj* l_Array_extractAux___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1(obj*, obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Array_mfoldl_u_2082___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterate_u_2082Aux___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_revIterate(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_getOpt___rarg___boxed(obj*, obj*);
obj* l_Array_foldl_u_2082___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Array_foldl_u_2082___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mmap(obj*, obj*);
obj* l_Array_find___rarg___boxed(obj*, obj*);
obj* l_Array_toList(obj*);
obj* l_Array_set___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_append___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_revFoldl___rarg(obj*, obj*, obj*);
obj* l_Array_reverseAux(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___boxed(obj*, obj*);
obj* l_Array_idx___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_foldl___rarg(obj*, obj*, obj*);
obj* l_Array_HasBeq___boxed(obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Array_mfoldl_u_2082___spec__1(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___boxed(obj*, obj*);
obj* l_Array_isEqvAux(obj*);
obj* l_List_toArrayAux___main(obj*);
obj* l_List_redLength___rarg___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1(obj*, obj*);
obj* l_Array_HasAppend(obj*);
obj* l_Array_foldlFrom___boxed(obj*, obj*);
obj* l_Array_modify(obj*);
obj* l_Array_mfindAux(obj*, obj*, obj*);
obj* l_Array_miterateAux___boxed(obj*, obj*, obj*);
obj* l_Array_anyAux___main___at_Array_all___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_mkEmpty___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_map___spec__1___boxed(obj*, obj*);
uint8 l_Array_all___rarg(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_map___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___boxed(obj*, obj*);
obj* l_Array_miterate_u_2082Aux___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_back___rarg(obj*, obj*);
obj* l_List_redLength___rarg(obj*);
obj* l_Array_find___boxed(obj*, obj*);
obj* l_Array_size___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::array_get_size(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_mkEmpty___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::mk_empty_array(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_push___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::array_push(x_1, x_2);
return x_3;
}
}
obj* l_Array_mkArray___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::mk_array(x_1, x_2);
return x_3;
}
}
obj* _init_l_Array_empty___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = lean::mk_empty_array(x_0);
return x_1;
}
}
obj* l_Array_empty(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
obj* l_Array_empty___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_empty(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_HasEmptyc(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
obj* l_Array_HasEmptyc___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_HasEmptyc(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_Inhabited(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
obj* l_Array_Inhabited___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_Inhabited(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Array_isEmpty___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::array_get_size(x_0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_isEmpty(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_isEmpty___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Array_isEmpty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Array_isEmpty___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Array_isEmpty___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_isEmpty(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_singleton___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(1ul);
x_2 = lean::mk_array(x_1, x_0);
return x_2;
}
}
obj* l_Array_singleton(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_singleton___rarg), 1, 0);
return x_1;
}
}
obj* l_Array_singleton___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_singleton(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_index___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::array_index(x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_idx___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; obj* x_5; 
x_4 = lean::unbox_size_t(x_2);
x_5 = lean::array_idx(x_1, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_get___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::array_get(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_back___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::mk_nat_obj(1ul);
x_4 = lean::nat_sub(x_2, x_3);
lean::dec(x_2);
x_6 = lean::array_get(x_0, x_1, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l_Array_back(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_back___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Array_back___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_back___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_back___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_back(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_getOpt___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_0);
x_3 = lean::nat_dec_lt(x_1, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::array_index(x_0, x_1);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
}
obj* l_Array_getOpt(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_getOpt___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Array_getOpt___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_getOpt___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_getOpt___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_getOpt(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_update___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::array_update(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_updt___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; obj* x_6; 
x_5 = lean::unbox_size_t(x_2);
x_6 = lean::array_updt(x_1, x_5, x_3);
return x_6;
}
}
obj* l_Array_set___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::array_set(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_fswap___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::array_fswap(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_swap___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::array_swap(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_pop___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::array_pop(x_1);
return x_2;
}
}
obj* l_Array_shrink___main___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_0);
x_3 = lean::nat_dec_le(x_2, x_1);
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; 
x_5 = lean::array_pop(x_0);
x_0 = x_5;
goto _start;
}
else
{
return x_0;
}
}
}
obj* l_Array_shrink___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_shrink___main___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Array_shrink___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_shrink___main___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_shrink___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_shrink___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_shrink___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_shrink___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_Array_shrink(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_shrink___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Array_shrink___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_shrink___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_shrink___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_shrink(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_miterateAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_1);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_11; obj* x_14; obj* x_17; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::apply_2(x_14, lean::box(0), x_4);
return x_17;
}
else
{
obj* x_18; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; 
x_18 = lean::cnstr_get(x_0, 1);
lean::inc(x_18);
x_20 = lean::array_index(x_1, x_3);
lean::inc(x_3);
lean::inc(x_2);
x_23 = lean::apply_3(x_2, x_3, x_20, x_4);
x_24 = lean::mk_nat_obj(1ul);
x_25 = lean::nat_add(x_3, x_24);
lean::dec(x_3);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___rarg), 5, 4);
lean::closure_set(x_27, 0, x_0);
lean::closure_set(x_27, 1, x_1);
lean::closure_set(x_27, 2, x_2);
lean::closure_set(x_27, 3, x_25);
x_28 = lean::apply_4(x_18, lean::box(0), lean::box(0), x_23, x_27);
return x_28;
}
}
}
obj* l_Array_miterateAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___rarg), 5, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterateAux___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_miterateAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___rarg), 5, 0);
return x_3;
}
}
obj* l_Array_miterateAux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterateAux(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterate___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Array_miterateAux___main___rarg(x_0, x_1, x_3, x_4, x_2);
return x_5;
}
}
obj* l_Array_miterate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate___rarg), 4, 0);
return x_3;
}
}
obj* l_Array_miterate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterate(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_12; obj* x_15; obj* x_18; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::apply_2(x_15, lean::box(0), x_5);
return x_18;
}
else
{
obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
x_21 = lean::array_index(x_3, x_4);
lean::inc(x_2);
x_23 = lean::apply_2(x_2, x_5, x_21);
x_24 = lean::mk_nat_obj(1ul);
x_25 = lean::nat_add(x_4, x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed), 6, 5);
lean::closure_set(x_26, 0, x_0);
lean::closure_set(x_26, 1, x_1);
lean::closure_set(x_26, 2, x_2);
lean::closure_set(x_26, 3, x_3);
lean::closure_set(x_26, 4, x_25);
x_27 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_23, x_26);
return x_27;
}
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_Array_mfoldl___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; 
x_4 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_6 = l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(x_0, x_1, x_3, x_1, x_4, x_2);
return x_6;
}
}
obj* l_Array_mfoldl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfoldl___rarg), 4, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterateAux___main___at_Array_mfoldl___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_mfoldl___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mfoldl(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_12; obj* x_15; obj* x_18; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::apply_2(x_15, lean::box(0), x_5);
return x_18;
}
else
{
obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
x_21 = lean::array_index(x_3, x_4);
lean::inc(x_2);
x_23 = lean::apply_2(x_2, x_5, x_21);
x_24 = lean::mk_nat_obj(1ul);
x_25 = lean::nat_add(x_4, x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg___boxed), 6, 5);
lean::closure_set(x_26, 0, x_0);
lean::closure_set(x_26, 1, x_1);
lean::closure_set(x_26, 2, x_2);
lean::closure_set(x_26, 3, x_3);
lean::closure_set(x_26, 4, x_25);
x_27 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_23, x_26);
return x_27;
}
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_Array_mfoldlFrom___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; 
lean::inc(x_1);
x_6 = l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg(x_0, x_1, x_3, x_1, x_4, x_2);
return x_6;
}
}
obj* l_Array_mfoldlFrom(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfoldlFrom___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterateAux___main___at_Array_mfoldlFrom___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_mfoldlFrom___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_mfoldlFrom___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Array_mfoldlFrom___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mfoldlFrom(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterate_u_2082Aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_1);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_13; obj* x_16; obj* x_19; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::apply_2(x_16, lean::box(0), x_5);
return x_19;
}
else
{
obj* x_20; uint8 x_21; 
x_20 = lean::array_get_size(x_2);
x_21 = lean::nat_dec_lt(x_4, x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_27; obj* x_30; obj* x_33; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_27 = lean::cnstr_get(x_0, 0);
lean::inc(x_27);
lean::dec(x_0);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
x_33 = lean::apply_2(x_30, lean::box(0), x_5);
return x_33;
}
else
{
obj* x_34; obj* x_36; obj* x_37; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; 
x_34 = lean::cnstr_get(x_0, 1);
lean::inc(x_34);
x_36 = lean::array_index(x_1, x_4);
x_37 = lean::array_index(x_2, x_4);
lean::inc(x_4);
lean::inc(x_3);
x_40 = lean::apply_4(x_3, x_4, x_36, x_37, x_5);
x_41 = lean::mk_nat_obj(1ul);
x_42 = lean::nat_add(x_4, x_41);
lean::dec(x_4);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u_2082Aux___main___rarg), 6, 5);
lean::closure_set(x_44, 0, x_0);
lean::closure_set(x_44, 1, x_1);
lean::closure_set(x_44, 2, x_2);
lean::closure_set(x_44, 3, x_3);
lean::closure_set(x_44, 4, x_42);
x_45 = lean::apply_4(x_34, lean::box(0), lean::box(0), x_40, x_44);
return x_45;
}
}
}
}
obj* l_Array_miterate_u_2082Aux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u_2082Aux___main___rarg), 6, 0);
return x_3;
}
}
obj* l_Array_miterate_u_2082Aux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterate_u_2082Aux___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterate_u_2082Aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterate_u_2082Aux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Array_miterate_u_2082Aux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u_2082Aux___rarg), 6, 0);
return x_3;
}
}
obj* l_Array_miterate_u_2082Aux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterate_u_2082Aux(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterate_u_2082___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = l_Array_miterate_u_2082Aux___main___rarg(x_0, x_1, x_2, x_4, x_5, x_3);
return x_6;
}
}
obj* l_Array_miterate_u_2082(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u_2082___rarg), 5, 0);
return x_3;
}
}
obj* l_Array_miterate_u_2082___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterate_u_2082(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterate_u_2082Aux___main___at_Array_mfoldl_u_2082___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_3);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_14; obj* x_17; obj* x_20; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = lean::apply_2(x_17, lean::box(0), x_6);
return x_20;
}
else
{
obj* x_21; uint8 x_22; 
x_21 = lean::array_get_size(x_4);
x_22 = lean::nat_dec_lt(x_5, x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_28; obj* x_31; obj* x_34; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_28 = lean::cnstr_get(x_0, 0);
lean::inc(x_28);
lean::dec(x_0);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
x_34 = lean::apply_2(x_31, lean::box(0), x_6);
return x_34;
}
else
{
obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_35 = lean::cnstr_get(x_0, 1);
lean::inc(x_35);
x_37 = lean::array_index(x_3, x_5);
x_38 = lean::array_index(x_4, x_5);
lean::inc(x_2);
x_40 = lean::apply_3(x_2, x_6, x_37, x_38);
x_41 = lean::mk_nat_obj(1ul);
x_42 = lean::nat_add(x_5, x_41);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u_2082Aux___main___at_Array_mfoldl_u_2082___spec__1___rarg___boxed), 7, 6);
lean::closure_set(x_43, 0, x_0);
lean::closure_set(x_43, 1, x_1);
lean::closure_set(x_43, 2, x_2);
lean::closure_set(x_43, 3, x_3);
lean::closure_set(x_43, 4, x_4);
lean::closure_set(x_43, 5, x_42);
x_44 = lean::apply_4(x_35, lean::box(0), lean::box(0), x_40, x_43);
return x_44;
}
}
}
}
obj* l_Array_miterate_u_2082Aux___main___at_Array_mfoldl_u_2082___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u_2082Aux___main___at_Array_mfoldl_u_2082___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_Array_mfoldl_u_2082___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; 
x_5 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_7 = l_Array_miterate_u_2082Aux___main___at_Array_mfoldl_u_2082___spec__1___rarg(x_0, x_1, x_4, x_1, x_2, x_5, x_3);
return x_7;
}
}
obj* l_Array_mfoldl_u_2082(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfoldl_u_2082___rarg), 5, 0);
return x_3;
}
}
obj* l_Array_miterate_u_2082Aux___main___at_Array_mfoldl_u_2082___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterate_u_2082Aux___main___at_Array_mfoldl_u_2082___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
return x_7;
}
}
obj* l_Array_miterate_u_2082Aux___main___at_Array_mfoldl_u_2082___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterate_u_2082Aux___main___at_Array_mfoldl_u_2082___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_mfoldl_u_2082___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mfoldl_u_2082(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_mfindAux___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::mk_nat_obj(1ul);
x_6 = lean::nat_add(x_0, x_5);
x_7 = l_Array_mfindAux___main___rarg(x_1, x_2, x_3, x_6);
return x_7;
}
else
{
obj* x_10; obj* x_13; obj* x_16; 
lean::dec(x_3);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::apply_2(x_13, lean::box(0), x_4);
return x_16;
}
}
}
obj* l_Array_mfindAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_10; obj* x_13; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::box(0);
x_17 = lean::apply_2(x_13, lean::box(0), x_16);
return x_17;
}
else
{
obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
x_18 = lean::cnstr_get(x_0, 1);
lean::inc(x_18);
x_20 = lean::array_index(x_1, x_3);
lean::inc(x_2);
x_22 = lean::apply_1(x_2, x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindAux___main___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_23, 0, x_3);
lean::closure_set(x_23, 1, x_0);
lean::closure_set(x_23, 2, x_1);
lean::closure_set(x_23, 3, x_2);
x_24 = lean::apply_4(x_18, lean::box(0), lean::box(0), x_22, x_23);
return x_24;
}
}
}
obj* l_Array_mfindAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindAux___main___rarg), 4, 0);
return x_3;
}
}
obj* l_Array_mfindAux___main___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_mfindAux___main___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_Array_mfindAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mfindAux___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_mfindAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mfindAux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Array_mfindAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindAux___rarg), 4, 0);
return x_3;
}
}
obj* l_Array_mfindAux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mfindAux(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_mfind___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_mfindAux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Array_mfind(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfind___rarg), 3, 0);
return x_3;
}
}
obj* l_Array_mfind___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mfind(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
else
{
obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::array_index(x_2, x_3);
lean::inc(x_3);
lean::inc(x_1);
x_13 = lean::apply_3(x_1, x_3, x_10, x_4);
x_14 = lean::mk_nat_obj(1ul);
x_15 = lean::nat_add(x_3, x_14);
lean::dec(x_3);
x_3 = x_15;
x_4 = x_13;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_iterate___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(x_0, x_2, x_0, x_3, x_1);
return x_4;
}
}
obj* l_Array_iterate(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_iterate___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_miterateAux___main___at_Array_iterate___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_iterate___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_iterate___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_iterate___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_iterate(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
else
{
obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::array_index(x_2, x_3);
lean::inc(x_1);
x_12 = lean::apply_2(x_1, x_4, x_10);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_foldl___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(x_0, x_1, x_0, x_3, x_2);
return x_4;
}
}
obj* l_Array_foldl(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_foldl___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_miterateAux___main___at_Array_foldl___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_foldl___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_foldl___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_foldl___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_foldl(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
else
{
obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::array_index(x_2, x_3);
lean::inc(x_1);
x_12 = lean::apply_2(x_1, x_4, x_10);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_foldlFrom___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg(x_0, x_1, x_0, x_3, x_2);
return x_4;
}
}
obj* l_Array_foldlFrom(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_foldlFrom___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Array_foldlFrom___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_miterateAux___main___at_Array_foldlFrom___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_foldlFrom___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_foldlFrom___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Array_foldlFrom___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_foldlFrom(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_miterate_u_2082Aux___main___at_Array_iterate_u_2082___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_2);
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
obj* x_11; uint8 x_12; 
x_11 = lean::array_get_size(x_3);
x_12 = lean::nat_dec_lt(x_4, x_11);
lean::dec(x_11);
if (x_12 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_16; obj* x_17; obj* x_20; obj* x_21; obj* x_22; 
x_16 = lean::array_index(x_2, x_4);
x_17 = lean::array_index(x_3, x_4);
lean::inc(x_4);
lean::inc(x_1);
x_20 = lean::apply_4(x_1, x_4, x_16, x_17, x_5);
x_21 = lean::mk_nat_obj(1ul);
x_22 = lean::nat_add(x_4, x_21);
lean::dec(x_4);
x_4 = x_22;
x_5 = x_20;
goto _start;
}
}
}
}
obj* l_Array_miterate_u_2082Aux___main___at_Array_iterate_u_2082___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u_2082Aux___main___at_Array_iterate_u_2082___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Array_iterate_u_2082___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Array_miterate_u_2082Aux___main___at_Array_iterate_u_2082___spec__1___rarg(x_0, x_3, x_0, x_1, x_4, x_2);
return x_5;
}
}
obj* l_Array_iterate_u_2082(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_iterate_u_2082___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Array_miterate_u_2082Aux___main___at_Array_iterate_u_2082___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterate_u_2082Aux___main___at_Array_iterate_u_2082___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_6;
}
}
obj* l_Array_miterate_u_2082Aux___main___at_Array_iterate_u_2082___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_miterate_u_2082Aux___main___at_Array_iterate_u_2082___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_iterate_u_2082___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_iterate_u_2082___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_iterate_u_2082___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_iterate_u_2082(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_miterate_u_2082Aux___main___at_Array_foldl_u_2082___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_2);
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
obj* x_11; uint8 x_12; 
x_11 = lean::array_get_size(x_3);
x_12 = lean::nat_dec_lt(x_4, x_11);
lean::dec(x_11);
if (x_12 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_16 = lean::array_index(x_2, x_4);
x_17 = lean::array_index(x_3, x_4);
lean::inc(x_1);
x_19 = lean::apply_3(x_1, x_5, x_16, x_17);
x_20 = lean::mk_nat_obj(1ul);
x_21 = lean::nat_add(x_4, x_20);
lean::dec(x_4);
x_4 = x_21;
x_5 = x_19;
goto _start;
}
}
}
}
obj* l_Array_miterate_u_2082Aux___main___at_Array_foldl_u_2082___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate_u_2082Aux___main___at_Array_foldl_u_2082___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Array_foldl_u_2082___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Array_miterate_u_2082Aux___main___at_Array_foldl_u_2082___spec__1___rarg(x_0, x_2, x_0, x_1, x_4, x_3);
return x_5;
}
}
obj* l_Array_foldl_u_2082(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_foldl_u_2082___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Array_miterate_u_2082Aux___main___at_Array_foldl_u_2082___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterate_u_2082Aux___main___at_Array_foldl_u_2082___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_6;
}
}
obj* l_Array_miterate_u_2082Aux___main___at_Array_foldl_u_2082___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_miterate_u_2082Aux___main___at_Array_foldl_u_2082___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_foldl_u_2082___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_foldl_u_2082___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_foldl_u_2082___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_foldl_u_2082(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_mfindAux___main___at_Array_find___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_8 = lean::box(0);
return x_8;
}
else
{
obj* x_9; obj* x_11; 
x_9 = lean::array_index(x_1, x_2);
lean::inc(x_0);
x_11 = lean::apply_1(x_0, x_9);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
lean::dec(x_2);
x_2 = x_13;
goto _start;
}
else
{
lean::dec(x_0);
lean::dec(x_2);
return x_11;
}
}
}
}
obj* l_Array_mfindAux___main___at_Array_find___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindAux___main___at_Array_find___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Array_find___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_mfindAux___main___at_Array_find___spec__1___rarg(x_1, x_0, x_2);
return x_3;
}
}
obj* l_Array_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_find___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Array_mfindAux___main___at_Array_find___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mfindAux___main___at_Array_find___spec__1___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_mfindAux___main___at_Array_find___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_mfindAux___main___at_Array_find___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_find___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_find___rarg(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Array_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Array_anyAux___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_0);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_8; 
lean::dec(x_1);
lean::dec(x_2);
x_8 = 0;
return x_8;
}
else
{
obj* x_9; obj* x_11; uint8 x_12; 
x_9 = lean::array_index(x_0, x_2);
lean::inc(x_1);
x_11 = lean::apply_1(x_1, x_9);
x_12 = lean::unbox(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_2, x_13);
lean::dec(x_2);
x_2 = x_14;
goto _start;
}
else
{
uint8 x_19; 
lean::dec(x_1);
lean::dec(x_2);
x_19 = 1;
return x_19;
}
}
}
}
obj* l_Array_anyAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_anyAux___main___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Array_anyAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyAux___main___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Array_anyAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_anyAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Array_anyAux___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Array_anyAux___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_anyAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_anyAux___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Array_anyAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyAux___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Array_anyAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_anyAux(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Array_any___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_anyAux___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_any(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_any___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Array_any___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Array_any___rarg(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_any___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_any(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Array_anyAux___main___at_Array_all___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_8 = 0;
return x_8;
}
else
{
obj* x_9; obj* x_11; uint8 x_12; 
x_9 = lean::array_index(x_1, x_2);
lean::inc(x_0);
x_11 = lean::apply_1(x_0, x_9);
x_12 = lean::unbox(x_11);
if (x_12 == 0)
{
uint8 x_15; 
lean::dec(x_0);
lean::dec(x_2);
x_15 = 1;
return x_15;
}
else
{
obj* x_16; obj* x_17; 
x_16 = lean::mk_nat_obj(1ul);
x_17 = lean::nat_add(x_2, x_16);
lean::dec(x_2);
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_Array_anyAux___main___at_Array_all___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_anyAux___main___at_Array_all___spec__1___rarg___boxed), 3, 0);
return x_1;
}
}
uint8 l_Array_all___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_anyAux___main___at_Array_all___spec__1___rarg(x_1, x_0, x_2);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
}
}
obj* l_Array_all(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_all___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Array_anyAux___main___at_Array_all___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyAux___main___at_Array_all___spec__1___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_anyAux___main___at_Array_all___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_anyAux___main___at_Array_all___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_all___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Array_all___rarg(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_all___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_all(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_13; 
x_7 = lean::mk_nat_obj(1ul);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_2);
x_10 = lean::array_index(x_0, x_8);
lean::inc(x_8);
lean::inc(x_1);
x_13 = lean::apply_3(x_1, x_8, x_10, x_4);
x_2 = x_8;
x_3 = lean::box(0);
x_4 = x_13;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__revIterateAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_1__revIterateAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_3);
return x_5;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_array_basic_1__revIterateAux___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_1__revIterateAux___main___rarg(x_0, x_1, x_2, lean::box(0), x_4);
return x_5;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__revIterateAux___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_1__revIterateAux___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_3);
return x_5;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_array_basic_1__revIterateAux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_revIterate___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::array_get_size(x_0);
x_4 = l___private_init_data_array_basic_1__revIterateAux___main___rarg(x_0, x_2, x_3, lean::box(0), x_1);
return x_4;
}
}
obj* l_Array_revIterate(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_revIterate___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Array_revIterate___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_revIterate___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_revIterate___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_revIterate(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0ul);
x_7 = lean::nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_8 = lean::mk_nat_obj(1ul);
x_9 = lean::nat_sub(x_3, x_8);
lean::dec(x_3);
x_11 = lean::array_index(x_2, x_9);
lean::inc(x_1);
x_13 = lean::apply_2(x_1, x_11, x_5);
x_3 = x_9;
x_4 = lean::box(0);
x_5 = x_13;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_3);
return x_5;
}
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Array_revFoldl___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::array_get_size(x_0);
x_4 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(x_0, x_2, x_0, x_3, lean::box(0), x_1);
return x_4;
}
}
obj* l_Array_revFoldl(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_revFoldl___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_4);
return x_6;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_revFoldl___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_revFoldl___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_revFoldl___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_revFoldl(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
x_7 = lean::mk_nat_obj(1ul);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_2);
x_10 = lean::array_index(x_1, x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_4);
x_2 = x_8;
x_3 = lean::box(0);
x_4 = x_11;
goto _start;
}
else
{
lean::dec(x_2);
return x_4;
}
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Array_toList___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::array_get_size(x_0);
x_3 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg(x_0, x_0, x_2, lean::box(0), x_1);
return x_3;
}
}
obj* l_Array_toList(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_toList___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
return x_5;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_toList___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_toList___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_toList___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_toList(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Array_HasRepr___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_toList___rarg___boxed), 1, 0);
return x_0;
}
}
obj* l_Array_HasRepr___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_repr___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = l_Array_HasRepr___rarg___closed__1;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Array_HasRepr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_HasRepr___rarg), 1, 0);
return x_1;
}
}
obj* l_Array_HasRepr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_HasRepr(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_HasToString___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toString___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = l_Array_HasRepr___rarg___closed__1;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Array_HasToString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_HasToString___rarg), 1, 0);
return x_1;
}
}
obj* l_Array_HasToString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_HasToString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::array_push(x_1, x_2);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_4);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_13; obj* x_16; obj* x_19; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::apply_2(x_16, lean::box(0), x_6);
return x_19;
}
else
{
obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_20 = lean::cnstr_get(x_0, 1);
lean::inc(x_20);
x_22 = lean::array_index(x_4, x_5);
lean::inc(x_2);
x_24 = lean::apply_1(x_2, x_22);
lean::inc(x_0);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___lambda__1), 3, 2);
lean::closure_set(x_26, 0, x_0);
lean::closure_set(x_26, 1, x_6);
lean::inc(x_20);
x_28 = lean::apply_4(x_20, lean::box(0), lean::box(0), x_24, x_26);
x_29 = lean::mk_nat_obj(1ul);
x_30 = lean::nat_add(x_5, x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___boxed), 7, 6);
lean::closure_set(x_31, 0, x_0);
lean::closure_set(x_31, 1, lean::box(0));
lean::closure_set(x_31, 2, x_2);
lean::closure_set(x_31, 3, x_3);
lean::closure_set(x_31, 4, x_4);
lean::closure_set(x_31, 5, x_30);
x_32 = lean::apply_4(x_20, lean::box(0), lean::box(0), x_28, x_31);
return x_32;
}
}
}
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l_Array_mmap___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::mk_empty_array(x_4);
lean::dec(x_4);
x_7 = lean::mk_nat_obj(0ul);
lean::inc(x_3);
x_9 = l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg(x_0, lean::box(0), x_2, x_3, x_3, x_7, x_5);
return x_9;
}
}
obj* l_Array_mmap(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mmap___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
lean::dec(x_5);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_miterateAux___main___at_Array_mmap___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_mmap___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mmap___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_mmap___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_mmap(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_modify___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_3);
lean::dec(x_0);
return x_1;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::array_index(x_1, x_2);
x_10 = lean::array_update(x_1, x_2, x_0);
x_11 = lean::apply_1(x_3, x_9);
x_12 = lean::array_update(x_10, x_2, x_11);
return x_12;
}
}
}
obj* l_Array_modify(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_modify___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Array_modify___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_modify___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_modify___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_modify(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_hmmapAux___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::mk_nat_obj(1ul);
x_7 = lean::nat_add(x_0, x_6);
x_8 = lean::array_update(x_1, x_0, x_5);
x_9 = l_Array_hmmapAux___main___rarg(x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
obj* l_Array_hmmapAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_11; obj* x_14; obj* x_17; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::apply_2(x_14, lean::box(0), x_4);
return x_17;
}
else
{
obj* x_18; obj* x_20; obj* x_21; obj* x_25; obj* x_26; obj* x_27; 
x_18 = lean::array_index(x_4, x_3);
lean::inc(x_1);
x_20 = lean::array_update(x_4, x_3, x_1);
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::inc(x_3);
lean::inc(x_2);
x_25 = lean::apply_2(x_2, x_3, x_18);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_hmmapAux___main___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_26, 0, x_3);
lean::closure_set(x_26, 1, x_20);
lean::closure_set(x_26, 2, x_0);
lean::closure_set(x_26, 3, x_1);
lean::closure_set(x_26, 4, x_2);
x_27 = lean::apply_4(x_21, lean::box(0), lean::box(0), x_25, x_26);
return x_27;
}
}
}
obj* l_Array_hmmapAux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_hmmapAux___main___rarg), 5, 0);
return x_2;
}
}
obj* l_Array_hmmapAux___main___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_hmmapAux___main___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
return x_6;
}
}
obj* l_Array_hmmapAux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_hmmapAux___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_hmmapAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_hmmapAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_hmmapAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_hmmapAux___rarg), 5, 0);
return x_2;
}
}
obj* l_Array_hmmapAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_hmmapAux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_hmmapAux___main___at_Array_hmmap___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::mk_nat_obj(1ul);
x_7 = lean::nat_add(x_0, x_6);
x_8 = lean::array_update(x_1, x_0, x_5);
x_9 = l_Array_hmmapAux___main___at_Array_hmmap___spec__1___rarg(x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
obj* l_Array_hmmapAux___main___at_Array_hmmap___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_11; obj* x_14; obj* x_17; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::apply_2(x_14, lean::box(0), x_4);
return x_17;
}
else
{
obj* x_18; obj* x_20; obj* x_21; obj* x_24; obj* x_25; obj* x_26; 
x_18 = lean::array_index(x_4, x_3);
lean::inc(x_1);
x_20 = lean::array_update(x_4, x_3, x_1);
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::inc(x_2);
x_24 = lean::apply_1(x_2, x_18);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_hmmapAux___main___at_Array_hmmap___spec__1___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_25, 0, x_3);
lean::closure_set(x_25, 1, x_20);
lean::closure_set(x_25, 2, x_0);
lean::closure_set(x_25, 3, x_1);
lean::closure_set(x_25, 4, x_2);
x_26 = lean::apply_4(x_21, lean::box(0), lean::box(0), x_24, x_25);
return x_26;
}
}
}
obj* l_Array_hmmapAux___main___at_Array_hmmap___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_hmmapAux___main___at_Array_hmmap___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* l_Array_hmmap___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Array_hmmapAux___main___at_Array_hmmap___spec__1___rarg(x_0, x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_Array_hmmap(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_hmmap___rarg), 4, 0);
return x_2;
}
}
obj* l_Array_hmmapAux___main___at_Array_hmmap___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_hmmapAux___main___at_Array_hmmap___spec__1___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
return x_6;
}
}
obj* l_Array_hmmapAux___main___at_Array_hmmap___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_hmmapAux___main___at_Array_hmmap___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_hmmap___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_hmmap(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_hmmapAux___main___at_Array_hmap___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_10 = lean::array_index(x_3, x_2);
lean::inc(x_0);
x_12 = lean::array_update(x_3, x_2, x_0);
lean::inc(x_1);
x_14 = lean::apply_1(x_1, x_10);
x_15 = lean::mk_nat_obj(1ul);
x_16 = lean::nat_add(x_2, x_15);
x_17 = lean::array_update(x_12, x_2, x_14);
lean::dec(x_2);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at_Array_hmap___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_hmmapAux___main___at_Array_hmap___spec__1___rarg), 4, 0);
return x_1;
}
}
obj* l_Array_hmap___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_hmmapAux___main___at_Array_hmap___spec__1___rarg(x_0, x_1, x_3, x_2);
return x_4;
}
}
obj* l_Array_hmap(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_hmap___rarg), 3, 0);
return x_1;
}
}
obj* l_Array_hmmapAux___main___at_Array_hmap___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_hmmapAux___main___at_Array_hmap___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_hmap___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_hmap(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_hmmapAux___main___at_Array_hmapIdx___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_10 = lean::array_index(x_3, x_2);
lean::inc(x_0);
x_12 = lean::array_update(x_3, x_2, x_0);
lean::inc(x_2);
lean::inc(x_1);
x_15 = lean::apply_2(x_1, x_2, x_10);
x_16 = lean::mk_nat_obj(1ul);
x_17 = lean::nat_add(x_2, x_16);
x_18 = lean::array_update(x_12, x_2, x_15);
lean::dec(x_2);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at_Array_hmapIdx___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_hmmapAux___main___at_Array_hmapIdx___spec__1___rarg), 4, 0);
return x_1;
}
}
obj* l_Array_hmapIdx___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_hmmapAux___main___at_Array_hmapIdx___spec__1___rarg(x_0, x_1, x_3, x_2);
return x_4;
}
}
obj* l_Array_hmapIdx(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_hmapIdx___rarg), 3, 0);
return x_1;
}
}
obj* l_Array_hmmapAux___main___at_Array_hmapIdx___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_hmmapAux___main___at_Array_hmapIdx___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_hmapIdx___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_hmapIdx(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at_Array_map___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_0);
return x_4;
}
else
{
obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::array_index(x_2, x_3);
lean::inc(x_0);
x_12 = lean::apply_1(x_0, x_10);
x_13 = lean::array_push(x_4, x_12);
x_14 = lean::mk_nat_obj(1ul);
x_15 = lean::nat_add(x_3, x_14);
lean::dec(x_3);
x_3 = x_15;
x_4 = x_13;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Array_map___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_map___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_map___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::mk_empty_array(x_2);
lean::dec(x_2);
x_5 = lean::mk_nat_obj(0ul);
x_6 = l_Array_miterateAux___main___at_Array_map___spec__1___rarg(x_0, x_1, x_1, x_5, x_3);
return x_6;
}
}
obj* l_Array_map(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_map___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Array_map___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Array_map___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Array_map___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_miterateAux___main___at_Array_map___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_map___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_map___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_map___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_map(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_extractAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_lt(x_1, x_2);
if (x_5 == 0)
{
lean::dec(x_1);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_11; 
x_7 = lean::mk_nat_obj(1ul);
x_8 = lean::nat_add(x_1, x_7);
x_9 = lean::array_index(x_0, x_1);
lean::dec(x_1);
x_11 = lean::array_push(x_4, x_9);
x_1 = x_8;
x_3 = lean::box(0);
x_4 = x_11;
goto _start;
}
}
}
obj* l_Array_extractAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_extractAux___main___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Array_extractAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_extractAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_Array_extractAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_extractAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_extractAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_extractAux___main___rarg(x_0, x_1, x_2, lean::box(0), x_4);
return x_5;
}
}
obj* l_Array_extractAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_extractAux___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Array_extractAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_extractAux___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_Array_extractAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_extractAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_extract___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; uint8 x_7; 
x_3 = lean::nat_sub(x_2, x_1);
x_4 = lean::mk_empty_array(x_3);
lean::dec(x_3);
x_6 = lean::array_get_size(x_0);
x_7 = lean::nat_dec_le(x_2, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_1);
return x_4;
}
else
{
obj* x_10; 
x_10 = l_Array_extractAux___main___rarg(x_0, x_1, x_2, lean::box(0), x_4);
return x_10;
}
}
}
obj* l_Array_extract(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_extract___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Array_extract___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_extract___rarg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_extract___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_extract(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at_Array_append___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::array_index(x_1, x_2);
x_9 = lean::array_push(x_3, x_8);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_2, x_10);
lean::dec(x_2);
x_2 = x_11;
x_3 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Array_append___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_append___spec__1___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Array_append___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_2, x_0);
return x_3;
}
}
obj* l_Array_append(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_append___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at_Array_append___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Array_append___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_miterateAux___main___at_Array_append___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_append___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_append___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_append___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_append(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Array_HasAppend___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_append___rarg___boxed), 2, 0);
return x_0;
}
}
obj* l_Array_HasAppend(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_HasAppend___closed__1;
return x_1;
}
}
obj* l_Array_HasAppend___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_HasAppend(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Array_isEqvAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_0);
x_6 = lean::nat_dec_lt(x_4, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
uint8 x_10; 
lean::dec(x_4);
lean::dec(x_3);
x_10 = 1;
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_14; uint8 x_15; 
x_11 = lean::array_index(x_0, x_4);
x_12 = lean::array_index(x_1, x_4);
lean::inc(x_3);
x_14 = lean::apply_2(x_3, x_11, x_12);
x_15 = lean::unbox(x_14);
if (x_15 == 0)
{
uint8 x_18; 
lean::dec(x_4);
lean::dec(x_3);
x_18 = 0;
return x_18;
}
else
{
obj* x_19; obj* x_20; 
x_19 = lean::mk_nat_obj(1ul);
x_20 = lean::nat_add(x_4, x_19);
lean::dec(x_4);
x_2 = lean::box(0);
x_4 = x_20;
goto _start;
}
}
}
}
obj* l_Array_isEqvAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_isEqvAux___main___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Array_isEqvAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_Array_isEqvAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
x_6 = lean::box(x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_isEqvAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_isEqvAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Array_isEqvAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = l_Array_isEqvAux___main___rarg(x_0, x_1, lean::box(0), x_3, x_4);
return x_5;
}
}
obj* l_Array_isEqvAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_isEqvAux___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Array_isEqvAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_Array_isEqvAux___rarg(x_0, x_1, x_2, x_3, x_4);
x_6 = lean::box(x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_isEqvAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_isEqvAux(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Array_isEqv___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::array_get_size(x_0);
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_eq(x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
if (x_5 == 0)
{
uint8 x_9; 
lean::dec(x_2);
x_9 = 0;
return x_9;
}
else
{
obj* x_10; uint8 x_11; 
x_10 = lean::mk_nat_obj(0ul);
x_11 = l_Array_isEqvAux___main___rarg(x_0, x_1, lean::box(0), x_2, x_10);
return x_11;
}
}
}
obj* l_Array_isEqv(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_isEqv___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Array_isEqv___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_isEqv___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_isEqv___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_isEqv(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Array_HasBeq___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Array_isEqv___rarg(x_1, x_2, x_0);
return x_3;
}
}
obj* l_Array_HasBeq(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_HasBeq___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Array_HasBeq___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_HasBeq___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_HasBeq___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_HasBeq(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_reverseAux___main___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; 
x_2 = lean::array_get_size(x_0);
x_3 = lean::mk_nat_obj(2ul);
x_4 = lean::nat_div(x_2, x_3);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_1);
lean::dec(x_2);
return x_0;
}
else
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; 
x_9 = lean::nat_sub(x_2, x_1);
lean::dec(x_2);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_sub(x_9, x_11);
lean::dec(x_9);
x_14 = lean::array_swap(x_0, x_1, x_12);
lean::dec(x_12);
x_16 = lean::nat_add(x_1, x_11);
lean::dec(x_1);
x_0 = x_14;
x_1 = x_16;
goto _start;
}
}
}
obj* l_Array_reverseAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_reverseAux___main___rarg), 2, 0);
return x_1;
}
}
obj* l_Array_reverseAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_reverseAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_reverseAux___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_reverseAux___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_Array_reverseAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_reverseAux___rarg), 2, 0);
return x_1;
}
}
obj* l_Array_reverseAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_reverseAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_reverse___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Array_reverseAux___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_Array_reverse(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_reverse___rarg), 1, 0);
return x_1;
}
}
obj* l_Array_reverse___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_reverse(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_toArrayAux___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::array_push(x_1, x_2);
x_0 = x_4;
x_1 = x_7;
goto _start;
}
}
}
obj* l_List_toArrayAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toArrayAux___main___rarg), 2, 0);
return x_1;
}
}
obj* l_List_toArrayAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_toArrayAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_toArrayAux___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_toArrayAux___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_List_toArrayAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toArrayAux___rarg), 2, 0);
return x_1;
}
}
obj* l_List_toArrayAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_toArrayAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_redLength___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::mk_nat_obj(0ul);
return x_1;
}
else
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 1);
x_3 = l_List_redLength___main___rarg(x_2);
x_4 = lean::mk_nat_obj(1ul);
x_5 = lean::nat_add(x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
}
obj* l_List_redLength___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_redLength___main___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_List_redLength___main___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_redLength___main___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_redLength___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_redLength___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_redLength___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_redLength___main___rarg(x_0);
return x_1;
}
}
obj* l_List_redLength(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_redLength___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_List_redLength___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_redLength___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_redLength___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_redLength(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_toArray___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_1 = l_List_redLength___main___rarg(x_0);
x_2 = lean::mk_empty_array(x_1);
lean::dec(x_1);
x_4 = l_List_toArrayAux___main___rarg(x_0, x_2);
return x_4;
}
}
obj* l_List_toArray(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toArray___rarg), 1, 0);
return x_1;
}
}
obj* l_List_toArray___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_toArray(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* initialize_init_data_nat_basic(obj*);
obj* initialize_init_data_fin_basic(obj*);
obj* initialize_init_data_uint(obj*);
obj* initialize_init_data_repr(obj*);
obj* initialize_init_data_tostring(obj*);
obj* initialize_init_control_id(obj*);
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
 l_Array_empty___closed__1 = _init_l_Array_empty___closed__1();
lean::mark_persistent(l_Array_empty___closed__1);
 l_Array_HasRepr___rarg___closed__1 = _init_l_Array_HasRepr___rarg___closed__1();
lean::mark_persistent(l_Array_HasRepr___rarg___closed__1);
 l_Array_HasAppend___closed__1 = _init_l_Array_HasAppend___closed__1();
lean::mark_persistent(l_Array_HasAppend___closed__1);
return w;
}
