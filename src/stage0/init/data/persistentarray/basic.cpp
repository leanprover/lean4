// Lean compiler output
// Module: init.data.persistentarray.basic
// Imports: init.data.array.default
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
obj* l_PersistentArray_empty___closed__2;
obj* l_Array_ummapAux___main___at_PersistentArray_map___spec__4___rarg(obj*, obj*, obj*);
obj* l_PersistentArray_mmapAux___main___rarg___closed__1;
obj* l_PersistentArray_mforAux___rarg(obj*, obj*, obj*, obj*);
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfoldlFrom___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__4(obj*);
obj* l_List_toPersistentArrayAux___main(obj*);
obj* l_PersistentArray_collectStats(obj*);
obj* l_PersistentArray_mfindRevAux___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfind___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_collectStats___main___rarg___boxed(obj*, obj*, obj*);
obj* l_PersistentArray_mfindRev___at_PersistentArray_findRev___spec__1(obj*, obj*);
obj* l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1___boxed(obj*, obj*);
obj* l_PersistentArray_stats(obj*);
obj* l_PersistentArray_mkNewTail(obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_collectStats___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__1(obj*, obj*);
obj* l_PersistentArray_mmap___rarg(obj*, obj*, obj*, obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_PersistentArray_mfoldlFromAux___main___rarg(obj*, obj*, obj*, obj*, usize, usize, obj*);
obj* l_PersistentArray_setAux___rarg(obj*, usize, usize, obj*);
usize l_PersistentArray_mul2Shift(usize, usize);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__2(obj*, obj*);
obj* l_PersistentArray_mfindAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfindRevAux___boxed(obj*, obj*);
obj* l_PersistentArray_modifyAux(obj*);
obj* l_PersistentArray_mmap___at_PersistentArray_map___spec__1(obj*, obj*);
obj* l_PersistentArray_mmapAux___main___rarg___lambda__1(obj*);
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__4___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__5___rarg___boxed(obj*, obj*, obj*);
obj* l_PersistentArray_mfoldlAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArrayNode_isNode___rarg___boxed(obj*);
obj* l_PersistentArray_popLeaf___rarg(obj*);
obj* l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfind(obj*, obj*);
obj* l_PersistentArray_mmap___at_PersistentArray_map___spec__1___rarg(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__1___boxed(obj*, obj*);
obj* l_PersistentArray_popLeaf___main___rarg___closed__1;
obj* l_PersistentArray_insertNewLeaf___main(obj*);
obj* l_PersistentArray_mfindAux___main(obj*, obj*);
uint8 l_USize_decLt(usize, usize);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__9(obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_map___spec__5(obj*, obj*);
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_getAux___main___rarg(obj*, obj*, usize, usize);
obj* l_Array_ummapAux___main___at_PersistentArray_map___spec__4(obj*, obj*);
usize l_USize_shift__right(usize, usize);
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__5___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mkNewPath___main(obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__3___rarg(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__4(obj*, obj*);
obj* l_PersistentArray_insertNewLeaf___rarg(obj*, usize, usize, obj*);
obj* l_PersistentArray_mfoldlFromAux___main___at_PersistentArray_foldlFrom___spec__2___rarg(obj*, obj*, usize, usize, obj*);
obj* l_PersistentArray_get___rarg___boxed(obj*, obj*, obj*);
obj* l_PersistentArray_toList___rarg___boxed(obj*);
obj* l_PersistentArray_mfoldl___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_List_toPersistentArrayAux___main___rarg(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfind___at_PersistentArray_find___spec__1(obj*, obj*);
obj* l_PersistentArray_mkNewPath___rarg___boxed(obj*, obj*);
obj* l_PersistentArray_mfoldlAux___main(obj*, obj*);
obj* l_PersistentArray_mfoldlFromAux___rarg(obj*, obj*, obj*, obj*, usize, usize, obj*);
obj* l_PersistentArray_insertNewLeaf___main___rarg(obj*, usize, usize, obj*);
obj* l_PersistentArray_mfoldlFrom(obj*, obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__6(obj*, obj*);
obj* l_List_toPersistentArrayAux(obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfindRev___at_PersistentArray_findRev___spec__1___rarg(obj*, obj*);
obj* l_PersistentArray_Stats_toString___closed__2;
obj* l_PersistentArray_mfor___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_getAux(obj*);
obj* l_PersistentArray_mfind___boxed(obj*, obj*);
obj* l_PersistentArray_isEmpty___rarg___boxed(obj*);
usize l_USize_sub(usize, usize);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__5___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfindAux(obj*, obj*);
obj* l_PersistentArray_mmapAux___boxed(obj*, obj*);
obj* l_PersistentArray_mfindAux___main___at_PersistentArray_find___spec__2___rarg___boxed(obj*, obj*);
obj* l_PersistentArray_mfoldlFromAux___main___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mmap___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_foldlFrom(obj*, obj*);
obj* l_PersistentArray_mfoldlFrom___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfoldlFromAux___main___at_PersistentArray_foldlFrom___spec__2(obj*, obj*);
obj* l_PersistentArray_mfoldl___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfindAux___main___at_PersistentArray_find___spec__2(obj*, obj*);
obj* l_PersistentArray_getAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1___boxed(obj*, obj*);
obj* l_PersistentArray_mfoldlFromAux___main___at_PersistentArray_foldlFrom___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfoldlFromAux___main___boxed(obj*, obj*);
obj* l_PersistentArray_mfoldlAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfoldl___at_PersistentArray_toList___spec__1___rarg(obj*, obj*);
obj* l_PersistentArray_findRev(obj*, obj*);
obj* l_PersistentArray_push(obj*);
obj* l_PersistentArray_mkNewTail___rarg(obj*);
obj* l_PersistentArray_modifyAux___main___rarg(obj*, obj*, obj*, usize, usize);
obj* l_PersistentArray_get___rarg(obj*, obj*, obj*);
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__4(obj*, obj*);
obj* l_PersistentArray_mfoldlFromAux___boxed(obj*, obj*);
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__5(obj*, obj*);
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__5___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfoldlFromAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__3(obj*, obj*);
obj* l_PersistentArray_mfoldl___at_PersistentArray_foldl___spec__1(obj*, obj*);
obj* l_PersistentArray_mul2Shift___boxed(obj*, obj*);
obj* l_Array_mkEmpty(obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfor___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_map(obj*, obj*);
obj* l_PersistentArray_set___rarg(obj*, obj*, obj*);
obj* l_PersistentArray_collectStats___main___rarg(obj*, obj*, obj*);
obj* l_PersistentArray_mkEmptyArray(obj*);
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_toList___spec__2(obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__5___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfindRev___at_PersistentArray_findRev___spec__1___rarg___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_pop___rarg(obj*);
usize l_PersistentArray_initShift;
obj* l_PersistentArray_mfoldl___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__5___rarg(obj*, obj*, obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__4(obj*, obj*);
obj* l_PersistentArrayNode_Inhabited(obj*);
obj* l_PersistentArray_mfoldlAux(obj*, obj*);
obj* l_PersistentArray_mfindRevAux___main___at_PersistentArray_findRev___spec__3___rarg___boxed(obj*, obj*);
obj* l_PersistentArray_mfoldlFrom___at_PersistentArray_foldlFrom___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfor(obj*, obj*);
obj* l_PersistentArray_mmapAux___main(obj*, obj*);
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_Stats_toString___closed__4;
obj* l_PersistentArray_setAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_setAux(obj*);
obj* l_List_toPersistentArray___rarg(obj*);
obj* l_PersistentArray_mforAux___main(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__2(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__1(obj*, obj*);
obj* l_PersistentArray_tooBig___closed__1;
obj* l_PersistentArray_mfindAux___boxed(obj*, obj*);
uint8 l_USize_decEq(usize, usize);
obj* l_Array_mfindAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_empty___closed__3;
obj* l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_toList___rarg(obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_empty___closed__1;
obj* l_PersistentArray_mfindRevAux___main___boxed(obj*, obj*);
obj* l_PersistentArray_mmapAux___main___at_PersistentArray_map___spec__2(obj*, obj*);
obj* l_PersistentArray_Stats_toString(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_PersistentArray_push___rarg(obj*, obj*);
obj* l_PersistentArray_mfindRevAux(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfindRevAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_foldl(obj*, obj*);
usize l_USize_add(usize, usize);
obj* l_PersistentArray_toList(obj*);
obj* l_PersistentArray_mforAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mkNewPath___main___rarg___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_PersistentArray_collectStats___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__4___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldl___spec__2___rarg___boxed(obj*, obj*, obj*);
obj* l_PersistentArray_isEmpty(obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldl___spec__1(obj*, obj*);
obj* l_PersistentArray_mmapAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__5(obj*, obj*);
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__4___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__1___boxed(obj*, obj*);
obj* l_PersistentArray_mfoldl___at_PersistentArray_foldl___spec__1___rarg(obj*, obj*, obj*);
obj* l_PersistentArray_empty(obj*);
obj* l_PersistentArray_mmapAux___main___at_PersistentArray_map___spec__2___rarg(obj*, obj*);
obj* l_PersistentArray_foldl___rarg(obj*, obj*, obj*);
obj* l_PersistentArray_set(obj*);
obj* l_PersistentArray_stats___rarg(obj*);
obj* l_PersistentArray_mforAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldl___spec__2___rarg(obj*, obj*, obj*);
obj* l_Array_fget(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_collectStats___main___spec__1(obj*);
obj* l_PersistentArray_mkNewPath___rarg(usize, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_PersistentArray_setAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_HasToString;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_toList___spec__2___rarg(obj*, obj*);
obj* l_PersistentArray_mfindRev___boxed(obj*, obj*);
obj* l_PersistentArray_popLeaf___main___rarg(obj*);
obj* l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldlFrom___spec__3___rarg(obj*, obj*, obj*);
obj* l_PersistentArray_findRev___rarg___boxed(obj*, obj*);
uint8 l_Array_isEmpty___rarg(obj*);
obj* l_PersistentArray_mfoldl___at_PersistentArray_foldl___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_PersistentArray_collectStats___main(obj*);
obj* l_Array_push(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__7___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfindRevAux___main___at_PersistentArray_findRev___spec__3___rarg(obj*, obj*);
obj* l_PersistentArray_mfoldlFrom___at_PersistentArray_foldlFrom___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_collectStats___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__9___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__1___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__2___boxed(obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_PersistentArray_mforAux___main___spec__1___boxed(obj*, obj*);
obj* l_PersistentArray_mmapAux___main___boxed(obj*, obj*);
obj* l_PersistentArray_find___rarg___boxed(obj*, obj*);
obj* l_PersistentArray_mfindRev___rarg___lambda__1(obj*, obj*, obj*, obj*);
usize l_PersistentArray_mod2Shift(usize, usize);
obj* l_PersistentArray_mforAux___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__8(obj*, obj*);
obj* l_PersistentArray_mmapAux___main___rarg___lambda__2(obj*);
obj* l_PersistentArray_mfindRev(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldl___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfind___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__5___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_map___spec__3(obj*, obj*);
obj* l_PersistentArray_mforAux(obj*, obj*);
obj* l_List_toPersistentArrayAux___rarg(obj*, obj*);
obj* l_PersistentArray_setAux___main(obj*);
obj* l_PersistentArray_popLeaf(obj*);
obj* l_PersistentArray_Stats_toString___closed__1;
obj* l_PersistentArray_getAux___main___rarg___closed__1;
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__2(obj*, obj*);
obj* l_PersistentArray_mmapAux___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__3___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__2___boxed(obj*, obj*);
obj* l_PersistentArray_tooBig;
obj* l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___boxed(obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1(obj*, obj*);
obj* l_PersistentArray_popLeaf___main(obj*);
obj* l_PersistentArray_Inhabited(obj*);
obj* l_PersistentArray_mfoldlFromAux___main(obj*, obj*);
obj* l_PersistentArray_mfoldlAux___main___boxed(obj*, obj*);
obj* l_PersistentArrayNode_Inhabited___closed__1;
obj* l_PersistentArray_modify___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__2___boxed(obj*, obj*);
obj* l_PersistentArray_collectStats___rarg(obj*, obj*, obj*);
obj* l_PersistentArrayNode_isNode(obj*);
obj* l_PersistentArray_modify___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mkNewPath___main___rarg(usize, obj*);
obj* l_PersistentArray_modifyAux___main(obj*);
obj* l_PersistentArray_mfindAux___main___at_PersistentArray_find___spec__2___rarg(obj*, obj*);
obj* l_Array_mforAux___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1___boxed(obj*, obj*);
obj* l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_insertNewLeaf___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__7(obj*, obj*);
obj* l_PersistentArray_getAux___rarg(obj*, obj*, usize, usize);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__7___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfoldlFromAux___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_stats___rarg___boxed(obj*);
obj* l_PersistentArray_mfor___boxed(obj*, obj*);
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__5(obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_find___rarg(obj*, obj*);
obj* l_PersistentArray_mfoldl(obj*, obj*);
obj* l_Array_pop(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__4(obj*, obj*);
obj* l_PersistentArray_mmap___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mmapAux(obj*, obj*);
obj* l_PersistentArray_mfindRevAux___main(obj*, obj*);
obj* l_PersistentArray_div2Shift___boxed(obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2(obj*, obj*);
obj* l_PersistentArray_mfoldlFrom___at_PersistentArray_foldlFrom___spec__1(obj*, obj*);
obj* l_PersistentArray_getAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_Stats_toString___closed__3;
usize l_PersistentArray_div2Shift(usize, usize);
obj* l_PersistentArray_mfoldlFrom___boxed(obj*, obj*);
obj* l_PersistentArray_set___rarg___boxed(obj*, obj*, obj*);
obj* l_PersistentArray_find(obj*, obj*);
obj* l_PersistentArray_mfoldlFromAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_persistentarray_basic_1__emptyArray(obj*);
obj* l_PersistentArray_modifyAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__5(obj*);
obj* l_PersistentArray_mmap___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfoldlFromAux(obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l_PersistentArray_foldlFrom___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__5___rarg(obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1(obj*, obj*);
obj* l_PersistentArray_HasToString___closed__1;
obj* l_PersistentArray_mforAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mmap(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_map___rarg(obj*, obj*);
obj* l_PersistentArray_insertNewLeaf___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfind___at_PersistentArray_find___spec__1___rarg(obj*, obj*);
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__2___rarg(obj*, obj*, obj*, obj*);
usize l_PersistentArray_branching;
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__4___rarg(obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_modify(obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_map___spec__3___rarg(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__6___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
extern obj* l_usizeSz;
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__3(obj*, obj*);
namespace lean {
usize usize_of_nat(obj*);
}
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_toList___spec__2___rarg___boxed(obj*, obj*);
uint8 l_PersistentArrayNode_isNode___rarg(obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__1(obj*, obj*);
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__2(obj*, obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_PersistentArray_mfindRev___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__9___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_pop(obj*);
obj* l_PersistentArray_mfoldlAux___boxed(obj*, obj*);
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__5___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_modifyAux___rarg(obj*, obj*, obj*, usize, usize);
obj* l_Array_mfindRevAux___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
usize l_USize_shift__left(usize, usize);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldl___spec__1___boxed(obj*, obj*);
obj* l_Array_mforAux___main___at_PersistentArray_mforAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_set(obj*, obj*, obj*, obj*);
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__3___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2___boxed(obj*, obj*);
obj* l_PersistentArray_mforAux___main___boxed(obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_map___spec__5___rarg(obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_get(obj*);
obj* l_Array_mforAux___main___at_PersistentArray_mforAux___main___spec__1(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__8___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__5(obj*, obj*);
obj* l_PersistentArray_mmapAux___main___rarg___closed__2;
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_getAux___main(obj*);
obj* l_PersistentArray_mfoldl___at_PersistentArray_toList___spec__1___rarg___boxed(obj*, obj*);
obj* l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mod2Shift___boxed(obj*, obj*);
usize l_USize_land(usize, usize);
obj* l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__3(obj*);
obj* l_PersistentArray_mfindAux___main___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Nat_max(obj*, obj*);
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldlFrom___spec__3(obj*, obj*);
obj* l_PersistentArray_mfind___at_PersistentArray_find___spec__1___rarg___boxed(obj*, obj*);
obj* l_PersistentArray_foldlFrom___rarg(obj*, obj*, obj*, obj*);
namespace lean {
obj* usize_to_nat(usize);
}
obj* l_PersistentArray_findRev___rarg(obj*, obj*);
obj* l_PersistentArray_setAux___main___rarg(obj*, usize, usize, obj*);
obj* l_List_toPersistentArray(obj*);
obj* l_PersistentArray_insertNewLeaf(obj*);
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldl___spec__2(obj*, obj*);
obj* l_PersistentArray_mfoldl___at_PersistentArray_toList___spec__1(obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__5___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_PersistentArray_mforAux___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_foldl___rarg___boxed(obj*, obj*, obj*);
obj* l_PersistentArray_mmap___boxed(obj*, obj*);
obj* l_PersistentArray_mkNewPath(obj*);
obj* l_PersistentArray_modifyAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfindRevAux___main___at_PersistentArray_findRev___spec__3(obj*, obj*);
obj* l_PersistentArray_mfoldlFrom___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldlFrom___spec__3___rarg___boxed(obj*, obj*, obj*);
uint8 l_PersistentArray_isEmpty___rarg(obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__8___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentArray_mfindAux___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldl___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _init_l_PersistentArrayNode_Inhabited___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_PersistentArrayNode_Inhabited(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentArrayNode_Inhabited___closed__1;
return x_2;
}
}
uint8 l_PersistentArrayNode_isNode___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
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
obj* l_PersistentArrayNode_isNode(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArrayNode_isNode___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_PersistentArrayNode_isNode___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_PersistentArrayNode_isNode___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
usize _init_l_PersistentArray_initShift() {
_start:
{
usize x_1; 
x_1 = 5;
return x_1;
}
}
usize _init_l_PersistentArray_branching() {
_start:
{
usize x_1; 
x_1 = 32;
return x_1;
}
}
obj* _init_l_PersistentArray_empty___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(32u);
x_2 = lean::mk_empty_array(x_1);
return x_2;
}
}
obj* _init_l_PersistentArray_empty___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_PersistentArray_empty___closed__1;
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_PersistentArray_empty___closed__3() {
_start:
{
usize x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = 5;
x_2 = l_PersistentArray_empty___closed__2;
x_3 = l_PersistentArray_empty___closed__1;
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_cnstr(0, 4, sizeof(size_t)*1);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_4);
lean::cnstr_set(x_5, 3, x_4);
lean::cnstr_set_usize(x_5, 4, x_1);
return x_5;
}
}
obj* l_PersistentArray_empty(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentArray_empty___closed__3;
return x_2;
}
}
uint8 l_PersistentArray_isEmpty___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_1, 2);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
return x_4;
}
}
obj* l_PersistentArray_isEmpty(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_isEmpty___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_PersistentArray_isEmpty___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_PersistentArray_isEmpty___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_PersistentArray_Inhabited(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentArray_empty___closed__3;
return x_2;
}
}
obj* l_PersistentArray_mkEmptyArray(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentArray_empty___closed__1;
return x_2;
}
}
usize l_PersistentArray_mul2Shift(usize x_1, usize x_2) {
_start:
{
usize x_3; 
x_3 = x_1 << x_2;
return x_3;
}
}
obj* l_PersistentArray_mul2Shift___boxed(obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; usize x_5; obj* x_6; 
x_3 = lean::unbox_size_t(x_1);
lean::dec(x_1);
x_4 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_5 = l_PersistentArray_mul2Shift(x_3, x_4);
x_6 = lean::box_size_t(x_5);
return x_6;
}
}
usize l_PersistentArray_div2Shift(usize x_1, usize x_2) {
_start:
{
usize x_3; 
x_3 = x_1 >> x_2;
return x_3;
}
}
obj* l_PersistentArray_div2Shift___boxed(obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; usize x_5; obj* x_6; 
x_3 = lean::unbox_size_t(x_1);
lean::dec(x_1);
x_4 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_5 = l_PersistentArray_div2Shift(x_3, x_4);
x_6 = lean::box_size_t(x_5);
return x_6;
}
}
usize l_PersistentArray_mod2Shift(usize x_1, usize x_2) {
_start:
{
usize x_3; usize x_4; usize x_5; usize x_6; 
x_3 = 1;
x_4 = x_3 << x_2;
x_5 = x_4 - x_3;
x_6 = x_1 & x_5;
return x_6;
}
}
obj* l_PersistentArray_mod2Shift___boxed(obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; usize x_5; obj* x_6; 
x_3 = lean::unbox_size_t(x_1);
lean::dec(x_1);
x_4 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_5 = l_PersistentArray_mod2Shift(x_3, x_4);
x_6 = lean::box_size_t(x_5);
return x_6;
}
}
obj* _init_l_PersistentArray_getAux___main___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = l_PersistentArrayNode_Inhabited(lean::box(0));
return x_1;
}
}
obj* l_PersistentArray_getAux___main___rarg(obj* x_1, obj* x_2, usize x_3, usize x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; usize x_6; obj* x_7; obj* x_8; obj* x_9; usize x_10; usize x_11; usize x_12; usize x_13; usize x_14; usize x_15; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_6 = x_3 >> x_4;
x_7 = lean::usize_to_nat(x_6);
x_8 = l_PersistentArray_getAux___main___rarg___closed__1;
x_9 = lean::array_get(x_8, x_5, x_7);
lean::dec(x_7);
lean::dec(x_5);
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
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::cnstr_get(x_2, 0);
lean::inc(x_17);
lean::dec(x_2);
x_18 = lean::usize_to_nat(x_3);
x_19 = lean::array_get(x_1, x_17, x_18);
lean::dec(x_18);
lean::dec(x_17);
return x_19;
}
}
}
obj* l_PersistentArray_getAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_getAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_PersistentArray_getAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; usize x_6; obj* x_7; 
x_5 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_6 = lean::unbox_size_t(x_4);
lean::dec(x_4);
x_7 = l_PersistentArray_getAux___main___rarg(x_1, x_2, x_5, x_6);
return x_7;
}
}
obj* l_PersistentArray_getAux___rarg(obj* x_1, obj* x_2, usize x_3, usize x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentArray_getAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_PersistentArray_getAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_getAux___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_PersistentArray_getAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; usize x_6; obj* x_7; 
x_5 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_6 = lean::unbox_size_t(x_4);
lean::dec(x_4);
x_7 = l_PersistentArray_getAux___rarg(x_1, x_2, x_5, x_6);
return x_7;
}
}
obj* l_PersistentArray_get___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_2, 3);
lean::inc(x_4);
x_5 = lean::nat_dec_le(x_4, x_3);
if (x_5 == 0)
{
obj* x_6; usize x_7; usize x_8; obj* x_9; 
lean::dec(x_4);
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_7 = lean::usize_of_nat(x_3);
x_8 = lean::cnstr_get_usize(x_2, 4);
lean::dec(x_2);
x_9 = l_PersistentArray_getAux___main___rarg(x_1, x_6, x_7, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
lean::dec(x_2);
x_11 = lean::nat_sub(x_3, x_4);
lean::dec(x_4);
x_12 = lean::array_get(x_1, x_10, x_11);
lean::dec(x_11);
lean::dec(x_10);
return x_12;
}
}
}
obj* l_PersistentArray_get(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_get___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_PersistentArray_get___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentArray_get___rarg(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_PersistentArray_setAux___main___rarg(obj* x_1, usize x_2, usize x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_1);
if (x_5 == 0)
{
obj* x_6; usize x_7; usize x_8; usize x_9; usize x_10; usize x_11; usize x_12; usize x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = x_2 >> x_3;
x_8 = 1;
x_9 = x_8 << x_3;
x_10 = x_9 - x_8;
x_11 = x_2 & x_10;
x_12 = 5;
x_13 = x_3 - x_12;
x_14 = lean::usize_to_nat(x_7);
x_15 = lean::array_get_size(x_6);
x_16 = lean::nat_dec_lt(x_14, x_15);
lean::dec(x_15);
if (x_16 == 0)
{
lean::dec(x_14);
lean::dec(x_4);
return x_1;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_17 = lean::array_fget(x_6, x_14);
x_18 = l_PersistentArrayNode_Inhabited___closed__1;
x_19 = lean::array_fset(x_6, x_14, x_18);
x_20 = l_PersistentArray_setAux___main___rarg(x_17, x_11, x_13, x_4);
x_21 = lean::array_fset(x_19, x_14, x_20);
lean::dec(x_14);
lean::cnstr_set(x_1, 0, x_21);
return x_1;
}
}
else
{
obj* x_22; usize x_23; usize x_24; usize x_25; usize x_26; usize x_27; usize x_28; usize x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_22 = lean::cnstr_get(x_1, 0);
lean::inc(x_22);
lean::dec(x_1);
x_23 = x_2 >> x_3;
x_24 = 1;
x_25 = x_24 << x_3;
x_26 = x_25 - x_24;
x_27 = x_2 & x_26;
x_28 = 5;
x_29 = x_3 - x_28;
x_30 = lean::usize_to_nat(x_23);
x_31 = lean::array_get_size(x_22);
x_32 = lean::nat_dec_lt(x_30, x_31);
lean::dec(x_31);
if (x_32 == 0)
{
obj* x_33; 
lean::dec(x_30);
lean::dec(x_4);
x_33 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_33, 0, x_22);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_34 = lean::array_fget(x_22, x_30);
x_35 = l_PersistentArrayNode_Inhabited___closed__1;
x_36 = lean::array_fset(x_22, x_30, x_35);
x_37 = l_PersistentArray_setAux___main___rarg(x_34, x_27, x_29, x_4);
x_38 = lean::array_fset(x_36, x_30, x_37);
lean::dec(x_30);
x_39 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
uint8 x_40; 
x_40 = !lean::is_exclusive(x_1);
if (x_40 == 0)
{
obj* x_41; obj* x_42; obj* x_43; 
x_41 = lean::cnstr_get(x_1, 0);
x_42 = lean::usize_to_nat(x_2);
x_43 = lean::array_set(x_41, x_42, x_4);
lean::dec(x_42);
lean::cnstr_set(x_1, 0, x_43);
return x_1;
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_44 = lean::cnstr_get(x_1, 0);
lean::inc(x_44);
lean::dec(x_1);
x_45 = lean::usize_to_nat(x_2);
x_46 = lean::array_set(x_44, x_45, x_4);
lean::dec(x_45);
x_47 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_47, 0, x_46);
return x_47;
}
}
}
}
obj* l_PersistentArray_setAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_setAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_PersistentArray_setAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; usize x_6; obj* x_7; 
x_5 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_6 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_7 = l_PersistentArray_setAux___main___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
obj* l_PersistentArray_setAux___rarg(obj* x_1, usize x_2, usize x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentArray_setAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_PersistentArray_setAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_setAux___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_PersistentArray_setAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; usize x_6; obj* x_7; 
x_5 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_6 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_7 = l_PersistentArray_setAux___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
obj* l_PersistentArray_set___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_1);
if (x_4 == 0)
{
obj* x_5; obj* x_6; usize x_7; obj* x_8; uint8 x_9; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::cnstr_get_usize(x_1, 4);
x_8 = lean::cnstr_get(x_1, 3);
x_9 = lean::nat_dec_le(x_8, x_2);
if (x_9 == 0)
{
usize x_10; obj* x_11; 
x_10 = lean::usize_of_nat(x_2);
x_11 = l_PersistentArray_setAux___main___rarg(x_5, x_10, x_7, x_3);
lean::cnstr_set(x_1, 0, x_11);
return x_1;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::nat_sub(x_2, x_8);
x_13 = lean::array_set(x_6, x_12, x_3);
lean::dec(x_12);
lean::cnstr_set(x_1, 1, x_13);
return x_1;
}
}
else
{
obj* x_14; obj* x_15; obj* x_16; usize x_17; obj* x_18; uint8 x_19; 
x_14 = lean::cnstr_get(x_1, 0);
x_15 = lean::cnstr_get(x_1, 1);
x_16 = lean::cnstr_get(x_1, 2);
x_17 = lean::cnstr_get_usize(x_1, 4);
x_18 = lean::cnstr_get(x_1, 3);
lean::inc(x_18);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_1);
x_19 = lean::nat_dec_le(x_18, x_2);
if (x_19 == 0)
{
usize x_20; obj* x_21; obj* x_22; 
x_20 = lean::usize_of_nat(x_2);
x_21 = l_PersistentArray_setAux___main___rarg(x_14, x_20, x_17, x_3);
x_22 = lean::alloc_cnstr(0, 4, sizeof(size_t)*1);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_15);
lean::cnstr_set(x_22, 2, x_16);
lean::cnstr_set(x_22, 3, x_18);
lean::cnstr_set_usize(x_22, 4, x_17);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = lean::nat_sub(x_2, x_18);
x_24 = lean::array_set(x_15, x_23, x_3);
lean::dec(x_23);
x_25 = lean::alloc_cnstr(0, 4, sizeof(size_t)*1);
lean::cnstr_set(x_25, 0, x_14);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set(x_25, 2, x_16);
lean::cnstr_set(x_25, 3, x_18);
lean::cnstr_set_usize(x_25, 4, x_17);
return x_25;
}
}
}
}
obj* l_PersistentArray_set(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_set___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_PersistentArray_set___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentArray_set___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_PersistentArray_modifyAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, usize x_4, usize x_5) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; usize x_8; usize x_9; usize x_10; usize x_11; usize x_12; usize x_13; usize x_14; obj* x_15; obj* x_16; uint8 x_17; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = x_4 >> x_5;
x_9 = 1;
x_10 = x_9 << x_5;
x_11 = x_10 - x_9;
x_12 = x_4 & x_11;
x_13 = 5;
x_14 = x_5 - x_13;
x_15 = lean::usize_to_nat(x_8);
x_16 = lean::array_get_size(x_7);
x_17 = lean::nat_dec_lt(x_15, x_16);
lean::dec(x_16);
if (x_17 == 0)
{
lean::dec(x_15);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_18 = lean::array_fget(x_7, x_15);
x_19 = l_PersistentArrayNode_Inhabited___closed__1;
x_20 = lean::array_fset(x_7, x_15, x_19);
x_21 = l_PersistentArray_modifyAux___main___rarg(x_1, x_2, x_18, x_12, x_14);
x_22 = lean::array_fset(x_20, x_15, x_21);
lean::dec(x_15);
lean::cnstr_set(x_3, 0, x_22);
return x_3;
}
}
else
{
obj* x_23; usize x_24; usize x_25; usize x_26; usize x_27; usize x_28; usize x_29; usize x_30; obj* x_31; obj* x_32; uint8 x_33; 
x_23 = lean::cnstr_get(x_3, 0);
lean::inc(x_23);
lean::dec(x_3);
x_24 = x_4 >> x_5;
x_25 = 1;
x_26 = x_25 << x_5;
x_27 = x_26 - x_25;
x_28 = x_4 & x_27;
x_29 = 5;
x_30 = x_5 - x_29;
x_31 = lean::usize_to_nat(x_24);
x_32 = lean::array_get_size(x_23);
x_33 = lean::nat_dec_lt(x_31, x_32);
lean::dec(x_32);
if (x_33 == 0)
{
obj* x_34; 
lean::dec(x_31);
lean::dec(x_2);
lean::dec(x_1);
x_34 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_34, 0, x_23);
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_35 = lean::array_fget(x_23, x_31);
x_36 = l_PersistentArrayNode_Inhabited___closed__1;
x_37 = lean::array_fset(x_23, x_31, x_36);
x_38 = l_PersistentArray_modifyAux___main___rarg(x_1, x_2, x_35, x_28, x_30);
x_39 = lean::array_fset(x_37, x_31, x_38);
lean::dec(x_31);
x_40 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8 x_41; 
x_41 = !lean::is_exclusive(x_3);
if (x_41 == 0)
{
obj* x_42; obj* x_43; obj* x_44; uint8 x_45; 
x_42 = lean::cnstr_get(x_3, 0);
x_43 = lean::usize_to_nat(x_4);
x_44 = lean::array_get_size(x_42);
x_45 = lean::nat_dec_lt(x_43, x_44);
lean::dec(x_44);
if (x_45 == 0)
{
lean::dec(x_43);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_46 = lean::array_fget(x_42, x_43);
x_47 = lean::array_fset(x_42, x_43, x_1);
x_48 = lean::apply_1(x_2, x_46);
x_49 = lean::array_fset(x_47, x_43, x_48);
lean::dec(x_43);
lean::cnstr_set(x_3, 0, x_49);
return x_3;
}
}
else
{
obj* x_50; obj* x_51; obj* x_52; uint8 x_53; 
x_50 = lean::cnstr_get(x_3, 0);
lean::inc(x_50);
lean::dec(x_3);
x_51 = lean::usize_to_nat(x_4);
x_52 = lean::array_get_size(x_50);
x_53 = lean::nat_dec_lt(x_51, x_52);
lean::dec(x_52);
if (x_53 == 0)
{
obj* x_54; 
lean::dec(x_51);
lean::dec(x_2);
lean::dec(x_1);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_50);
return x_54;
}
else
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_55 = lean::array_fget(x_50, x_51);
x_56 = lean::array_fset(x_50, x_51, x_1);
x_57 = lean::apply_1(x_2, x_55);
x_58 = lean::array_fset(x_56, x_51, x_57);
lean::dec(x_51);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
}
}
}
}
obj* l_PersistentArray_modifyAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_modifyAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_PersistentArray_modifyAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
usize x_6; usize x_7; obj* x_8; 
x_6 = lean::unbox_size_t(x_4);
lean::dec(x_4);
x_7 = lean::unbox_size_t(x_5);
lean::dec(x_5);
x_8 = l_PersistentArray_modifyAux___main___rarg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
obj* l_PersistentArray_modifyAux___rarg(obj* x_1, obj* x_2, obj* x_3, usize x_4, usize x_5) {
_start:
{
obj* x_6; 
x_6 = l_PersistentArray_modifyAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_PersistentArray_modifyAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_modifyAux___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_PersistentArray_modifyAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
usize x_6; usize x_7; obj* x_8; 
x_6 = lean::unbox_size_t(x_4);
lean::dec(x_4);
x_7 = lean::unbox_size_t(x_5);
lean::dec(x_5);
x_8 = l_PersistentArray_modifyAux___rarg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
obj* l_PersistentArray_modify___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_2);
if (x_5 == 0)
{
obj* x_6; obj* x_7; usize x_8; obj* x_9; uint8 x_10; 
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
x_8 = lean::cnstr_get_usize(x_2, 4);
x_9 = lean::cnstr_get(x_2, 3);
x_10 = lean::nat_dec_le(x_9, x_3);
if (x_10 == 0)
{
usize x_11; obj* x_12; 
x_11 = lean::usize_of_nat(x_3);
x_12 = l_PersistentArray_modifyAux___main___rarg(x_1, x_4, x_6, x_11, x_8);
lean::cnstr_set(x_2, 0, x_12);
return x_2;
}
else
{
obj* x_13; obj* x_14; uint8 x_15; 
x_13 = lean::nat_sub(x_3, x_9);
x_14 = lean::array_get_size(x_7);
x_15 = lean::nat_dec_lt(x_13, x_14);
lean::dec(x_14);
if (x_15 == 0)
{
lean::dec(x_13);
lean::dec(x_4);
lean::dec(x_1);
return x_2;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = lean::array_fget(x_7, x_13);
x_17 = lean::array_fset(x_7, x_13, x_1);
x_18 = lean::apply_1(x_4, x_16);
x_19 = lean::array_fset(x_17, x_13, x_18);
lean::dec(x_13);
lean::cnstr_set(x_2, 1, x_19);
return x_2;
}
}
}
else
{
obj* x_20; obj* x_21; obj* x_22; usize x_23; obj* x_24; uint8 x_25; 
x_20 = lean::cnstr_get(x_2, 0);
x_21 = lean::cnstr_get(x_2, 1);
x_22 = lean::cnstr_get(x_2, 2);
x_23 = lean::cnstr_get_usize(x_2, 4);
x_24 = lean::cnstr_get(x_2, 3);
lean::inc(x_24);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_2);
x_25 = lean::nat_dec_le(x_24, x_3);
if (x_25 == 0)
{
usize x_26; obj* x_27; obj* x_28; 
x_26 = lean::usize_of_nat(x_3);
x_27 = l_PersistentArray_modifyAux___main___rarg(x_1, x_4, x_20, x_26, x_23);
x_28 = lean::alloc_cnstr(0, 4, sizeof(size_t)*1);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_21);
lean::cnstr_set(x_28, 2, x_22);
lean::cnstr_set(x_28, 3, x_24);
lean::cnstr_set_usize(x_28, 4, x_23);
return x_28;
}
else
{
obj* x_29; obj* x_30; uint8 x_31; 
x_29 = lean::nat_sub(x_3, x_24);
x_30 = lean::array_get_size(x_21);
x_31 = lean::nat_dec_lt(x_29, x_30);
lean::dec(x_30);
if (x_31 == 0)
{
obj* x_32; 
lean::dec(x_29);
lean::dec(x_4);
lean::dec(x_1);
x_32 = lean::alloc_cnstr(0, 4, sizeof(size_t)*1);
lean::cnstr_set(x_32, 0, x_20);
lean::cnstr_set(x_32, 1, x_21);
lean::cnstr_set(x_32, 2, x_22);
lean::cnstr_set(x_32, 3, x_24);
lean::cnstr_set_usize(x_32, 4, x_23);
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_33 = lean::array_fget(x_21, x_29);
x_34 = lean::array_fset(x_21, x_29, x_1);
x_35 = lean::apply_1(x_4, x_33);
x_36 = lean::array_fset(x_34, x_29, x_35);
lean::dec(x_29);
x_37 = lean::alloc_cnstr(0, 4, sizeof(size_t)*1);
lean::cnstr_set(x_37, 0, x_20);
lean::cnstr_set(x_37, 1, x_36);
lean::cnstr_set(x_37, 2, x_22);
lean::cnstr_set(x_37, 3, x_24);
lean::cnstr_set_usize(x_37, 4, x_23);
return x_37;
}
}
}
}
}
obj* l_PersistentArray_modify(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_modify___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_PersistentArray_modify___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentArray_modify___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_PersistentArray_mkNewPath___main___rarg(usize x_1, obj* x_2) {
_start:
{
usize x_3; uint8 x_4; 
x_3 = 0;
x_4 = x_1 == x_3;
if (x_4 == 0)
{
usize x_5; usize x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = 5;
x_6 = x_1 - x_5;
x_7 = l_PersistentArray_mkNewPath___main___rarg(x_6, x_2);
x_8 = l_PersistentArray_empty___closed__1;
x_9 = lean::array_push(x_8, x_7);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_2);
return x_11;
}
}
}
obj* l_PersistentArray_mkNewPath___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mkNewPath___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_PersistentArray_mkNewPath___main___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
usize x_3; obj* x_4; 
x_3 = lean::unbox_size_t(x_1);
lean::dec(x_1);
x_4 = l_PersistentArray_mkNewPath___main___rarg(x_3, x_2);
return x_4;
}
}
obj* l_PersistentArray_mkNewPath___rarg(usize x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mkNewPath___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_PersistentArray_mkNewPath(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mkNewPath___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_PersistentArray_mkNewPath___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
usize x_3; obj* x_4; 
x_3 = lean::unbox_size_t(x_1);
lean::dec(x_1);
x_4 = l_PersistentArray_mkNewPath___rarg(x_3, x_2);
return x_4;
}
}
obj* l_PersistentArray_insertNewLeaf___main___rarg(obj* x_1, usize x_2, usize x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_1);
if (x_5 == 0)
{
obj* x_6; usize x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = 32;
x_8 = x_2 < x_7;
if (x_8 == 0)
{
usize x_9; usize x_10; usize x_11; usize x_12; usize x_13; usize x_14; usize x_15; obj* x_16; obj* x_17; uint8 x_18; 
x_9 = x_2 >> x_3;
x_10 = 1;
x_11 = x_10 << x_3;
x_12 = x_11 - x_10;
x_13 = x_2 & x_12;
x_14 = 5;
x_15 = x_3 - x_14;
x_16 = lean::usize_to_nat(x_9);
x_17 = lean::array_get_size(x_6);
x_18 = lean::nat_dec_lt(x_16, x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_16);
x_19 = l_PersistentArray_mkNewPath___main___rarg(x_15, x_4);
x_20 = lean::array_push(x_6, x_19);
lean::cnstr_set(x_1, 0, x_20);
return x_1;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_21 = lean::array_fget(x_6, x_16);
x_22 = l_PersistentArrayNode_Inhabited___closed__1;
x_23 = lean::array_fset(x_6, x_16, x_22);
x_24 = l_PersistentArray_insertNewLeaf___main___rarg(x_21, x_13, x_15, x_4);
x_25 = lean::array_fset(x_23, x_16, x_24);
lean::dec(x_16);
lean::cnstr_set(x_1, 0, x_25);
return x_1;
}
}
else
{
obj* x_26; obj* x_27; 
lean::cnstr_set_tag(x_1, 1);
lean::cnstr_set(x_1, 0, x_4);
x_26 = lean::array_push(x_6, x_1);
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
}
else
{
obj* x_28; usize x_29; uint8 x_30; 
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
lean::dec(x_1);
x_29 = 32;
x_30 = x_2 < x_29;
if (x_30 == 0)
{
usize x_31; usize x_32; usize x_33; usize x_34; usize x_35; usize x_36; usize x_37; obj* x_38; obj* x_39; uint8 x_40; 
x_31 = x_2 >> x_3;
x_32 = 1;
x_33 = x_32 << x_3;
x_34 = x_33 - x_32;
x_35 = x_2 & x_34;
x_36 = 5;
x_37 = x_3 - x_36;
x_38 = lean::usize_to_nat(x_31);
x_39 = lean::array_get_size(x_28);
x_40 = lean::nat_dec_lt(x_38, x_39);
lean::dec(x_39);
if (x_40 == 0)
{
obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_38);
x_41 = l_PersistentArray_mkNewPath___main___rarg(x_37, x_4);
x_42 = lean::array_push(x_28, x_41);
x_43 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
return x_43;
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_44 = lean::array_fget(x_28, x_38);
x_45 = l_PersistentArrayNode_Inhabited___closed__1;
x_46 = lean::array_fset(x_28, x_38, x_45);
x_47 = l_PersistentArray_insertNewLeaf___main___rarg(x_44, x_35, x_37, x_4);
x_48 = lean::array_fset(x_46, x_38, x_47);
lean::dec(x_38);
x_49 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
return x_49;
}
}
else
{
obj* x_50; obj* x_51; obj* x_52; 
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_4);
x_51 = lean::array_push(x_28, x_50);
x_52 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
lean::dec(x_4);
return x_1;
}
}
}
obj* l_PersistentArray_insertNewLeaf___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_insertNewLeaf___main___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_PersistentArray_insertNewLeaf___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; usize x_6; obj* x_7; 
x_5 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_6 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_7 = l_PersistentArray_insertNewLeaf___main___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
obj* l_PersistentArray_insertNewLeaf___rarg(obj* x_1, usize x_2, usize x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentArray_insertNewLeaf___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_PersistentArray_insertNewLeaf(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_insertNewLeaf___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_PersistentArray_insertNewLeaf___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; usize x_6; obj* x_7; 
x_5 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_6 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_7 = l_PersistentArray_insertNewLeaf___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
obj* l_PersistentArray_mkNewTail___rarg(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; usize x_6; obj* x_7; usize x_8; usize x_9; usize x_10; usize x_11; obj* x_12; uint8 x_13; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_1, 2);
x_6 = lean::cnstr_get_usize(x_1, 4);
x_7 = lean::cnstr_get(x_1, 3);
lean::dec(x_7);
x_8 = 1;
x_9 = 5;
x_10 = x_6 + x_9;
x_11 = x_8 << x_10;
x_12 = lean::usize_to_nat(x_11);
x_13 = lean::nat_dec_le(x_5, x_12);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_14 = l_PersistentArray_empty___closed__1;
x_15 = lean::array_push(x_14, x_3);
x_16 = l_PersistentArray_mkNewPath___main___rarg(x_6, x_4);
x_17 = lean::array_push(x_15, x_16);
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = l_Array_empty___closed__1;
lean::inc(x_5);
lean::cnstr_set(x_1, 3, x_5);
lean::cnstr_set(x_1, 1, x_19);
lean::cnstr_set(x_1, 0, x_18);
lean::cnstr_set_usize(x_1, 4, x_10);
return x_1;
}
else
{
obj* x_20; obj* x_21; usize x_22; obj* x_23; obj* x_24; 
x_20 = lean::mk_nat_obj(1u);
x_21 = lean::nat_sub(x_5, x_20);
x_22 = lean::usize_of_nat(x_21);
lean::dec(x_21);
x_23 = l_PersistentArray_insertNewLeaf___main___rarg(x_3, x_22, x_6, x_4);
x_24 = l_PersistentArray_empty___closed__1;
lean::inc(x_5);
lean::cnstr_set(x_1, 3, x_5);
lean::cnstr_set(x_1, 1, x_24);
lean::cnstr_set(x_1, 0, x_23);
return x_1;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; usize x_28; usize x_29; usize x_30; usize x_31; usize x_32; obj* x_33; uint8 x_34; 
x_25 = lean::cnstr_get(x_1, 0);
x_26 = lean::cnstr_get(x_1, 1);
x_27 = lean::cnstr_get(x_1, 2);
x_28 = lean::cnstr_get_usize(x_1, 4);
lean::inc(x_27);
lean::inc(x_26);
lean::inc(x_25);
lean::dec(x_1);
x_29 = 1;
x_30 = 5;
x_31 = x_28 + x_30;
x_32 = x_29 << x_31;
x_33 = lean::usize_to_nat(x_32);
x_34 = lean::nat_dec_le(x_27, x_33);
lean::dec(x_33);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_35 = l_PersistentArray_empty___closed__1;
x_36 = lean::array_push(x_35, x_25);
x_37 = l_PersistentArray_mkNewPath___main___rarg(x_28, x_26);
x_38 = lean::array_push(x_36, x_37);
x_39 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
x_40 = l_Array_empty___closed__1;
lean::inc(x_27);
x_41 = lean::alloc_cnstr(0, 4, sizeof(size_t)*1);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_40);
lean::cnstr_set(x_41, 2, x_27);
lean::cnstr_set(x_41, 3, x_27);
lean::cnstr_set_usize(x_41, 4, x_31);
return x_41;
}
else
{
obj* x_42; obj* x_43; usize x_44; obj* x_45; obj* x_46; obj* x_47; 
x_42 = lean::mk_nat_obj(1u);
x_43 = lean::nat_sub(x_27, x_42);
x_44 = lean::usize_of_nat(x_43);
lean::dec(x_43);
x_45 = l_PersistentArray_insertNewLeaf___main___rarg(x_25, x_44, x_28, x_26);
x_46 = l_PersistentArray_empty___closed__1;
lean::inc(x_27);
x_47 = lean::alloc_cnstr(0, 4, sizeof(size_t)*1);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_46);
lean::cnstr_set(x_47, 2, x_27);
lean::cnstr_set(x_47, 3, x_27);
lean::cnstr_set_usize(x_47, 4, x_28);
return x_47;
}
}
}
}
obj* l_PersistentArray_mkNewTail(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mkNewTail___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_PersistentArray_tooBig___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_usizeSz;
x_2 = lean::mk_nat_obj(8u);
x_3 = lean::nat_div(x_1, x_2);
return x_3;
}
}
obj* _init_l_PersistentArray_tooBig() {
_start:
{
obj* x_1; 
x_1 = l_PersistentArray_tooBig___closed__1;
return x_1;
}
}
obj* l_PersistentArray_push___rarg(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_1, 2);
x_6 = lean::array_push(x_4, x_2);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_5, x_7);
lean::inc(x_6);
lean::cnstr_set(x_1, 2, x_8);
lean::cnstr_set(x_1, 1, x_6);
x_9 = lean::array_get_size(x_6);
lean::dec(x_6);
x_10 = lean::mk_nat_obj(32u);
x_11 = lean::nat_dec_lt(x_9, x_10);
lean::dec(x_9);
if (x_11 == 0)
{
obj* x_12; uint8 x_13; 
x_12 = l_PersistentArray_tooBig;
x_13 = lean::nat_dec_le(x_12, x_5);
lean::dec(x_5);
if (x_13 == 0)
{
obj* x_14; 
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
lean::dec(x_5);
return x_1;
}
}
else
{
obj* x_15; obj* x_16; obj* x_17; usize x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; uint8 x_26; 
x_15 = lean::cnstr_get(x_1, 0);
x_16 = lean::cnstr_get(x_1, 1);
x_17 = lean::cnstr_get(x_1, 2);
x_18 = lean::cnstr_get_usize(x_1, 4);
x_19 = lean::cnstr_get(x_1, 3);
lean::inc(x_19);
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_1);
x_20 = lean::array_push(x_16, x_2);
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_add(x_17, x_21);
lean::inc(x_20);
x_23 = lean::alloc_cnstr(0, 4, sizeof(size_t)*1);
lean::cnstr_set(x_23, 0, x_15);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set(x_23, 2, x_22);
lean::cnstr_set(x_23, 3, x_19);
lean::cnstr_set_usize(x_23, 4, x_18);
x_24 = lean::array_get_size(x_20);
lean::dec(x_20);
x_25 = lean::mk_nat_obj(32u);
x_26 = lean::nat_dec_lt(x_24, x_25);
lean::dec(x_24);
if (x_26 == 0)
{
obj* x_27; uint8 x_28; 
x_27 = l_PersistentArray_tooBig;
x_28 = lean::nat_dec_le(x_27, x_17);
lean::dec(x_17);
if (x_28 == 0)
{
obj* x_29; 
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
lean::dec(x_17);
return x_23;
}
}
}
}
obj* l_PersistentArray_push(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_push___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_data_persistentarray_basic_1__emptyArray(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentArray_empty___closed__1;
return x_2;
}
}
obj* _init_l_PersistentArray_popLeaf___main___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_PersistentArray_empty___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_PersistentArray_popLeaf___main___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::array_get_size(x_3);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_4, x_7);
lean::dec(x_4);
x_9 = lean::array_fget(x_3, x_8);
x_10 = l_PersistentArrayNode_Inhabited___closed__1;
x_11 = lean::array_fset(x_3, x_8, x_10);
x_12 = l_PersistentArray_popLeaf___main___rarg(x_9);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
uint8 x_14; 
lean::dec(x_11);
lean::dec(x_8);
lean::free_heap_obj(x_1);
x_14 = !lean::is_exclusive(x_12);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_12, 1);
lean::dec(x_15);
x_16 = lean::cnstr_get(x_12, 0);
lean::dec(x_16);
x_17 = l_PersistentArray_empty___closed__1;
lean::cnstr_set(x_12, 1, x_17);
return x_12;
}
else
{
obj* x_18; obj* x_19; 
lean::dec(x_12);
x_18 = l_PersistentArray_empty___closed__1;
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_13);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8 x_20; 
x_20 = !lean::is_exclusive(x_12);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_21 = lean::cnstr_get(x_12, 1);
x_22 = lean::cnstr_get(x_12, 0);
lean::dec(x_22);
x_23 = lean::array_get_size(x_21);
x_24 = lean::nat_dec_eq(x_23, x_5);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_25; 
lean::cnstr_set(x_1, 0, x_21);
x_25 = lean::array_fset(x_11, x_8, x_1);
lean::dec(x_8);
lean::cnstr_set(x_12, 1, x_25);
return x_12;
}
else
{
obj* x_26; uint8 x_27; 
lean::dec(x_21);
lean::dec(x_8);
lean::free_heap_obj(x_1);
x_26 = lean::array_pop(x_11);
x_27 = l_Array_isEmpty___rarg(x_26);
if (x_27 == 0)
{
lean::cnstr_set(x_12, 1, x_26);
return x_12;
}
else
{
obj* x_28; 
lean::dec(x_26);
x_28 = l_PersistentArray_empty___closed__1;
lean::cnstr_set(x_12, 1, x_28);
return x_12;
}
}
}
else
{
obj* x_29; obj* x_30; uint8 x_31; 
x_29 = lean::cnstr_get(x_12, 1);
lean::inc(x_29);
lean::dec(x_12);
x_30 = lean::array_get_size(x_29);
x_31 = lean::nat_dec_eq(x_30, x_5);
lean::dec(x_30);
if (x_31 == 0)
{
obj* x_32; obj* x_33; 
lean::cnstr_set(x_1, 0, x_29);
x_32 = lean::array_fset(x_11, x_8, x_1);
lean::dec(x_8);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_13);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
else
{
obj* x_34; uint8 x_35; 
lean::dec(x_29);
lean::dec(x_8);
lean::free_heap_obj(x_1);
x_34 = lean::array_pop(x_11);
x_35 = l_Array_isEmpty___rarg(x_34);
if (x_35 == 0)
{
obj* x_36; 
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_13);
lean::cnstr_set(x_36, 1, x_34);
return x_36;
}
else
{
obj* x_37; obj* x_38; 
lean::dec(x_34);
x_37 = l_PersistentArray_empty___closed__1;
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_13);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
else
{
obj* x_39; 
lean::dec(x_4);
lean::free_heap_obj(x_1);
lean::dec(x_3);
x_39 = l_PersistentArray_popLeaf___main___rarg___closed__1;
return x_39;
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; uint8 x_43; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
lean::dec(x_1);
x_41 = lean::array_get_size(x_40);
x_42 = lean::mk_nat_obj(0u);
x_43 = lean::nat_dec_eq(x_41, x_42);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_44 = lean::mk_nat_obj(1u);
x_45 = lean::nat_sub(x_41, x_44);
lean::dec(x_41);
x_46 = lean::array_fget(x_40, x_45);
x_47 = l_PersistentArrayNode_Inhabited___closed__1;
x_48 = lean::array_fset(x_40, x_45, x_47);
x_49 = l_PersistentArray_popLeaf___main___rarg(x_46);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_48);
lean::dec(x_45);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_51 = x_49;
} else {
 lean::dec_ref(x_49);
 x_51 = lean::box(0);
}
x_52 = l_PersistentArray_empty___closed__1;
if (lean::is_scalar(x_51)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_51;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set(x_53, 1, x_52);
return x_53;
}
else
{
obj* x_54; obj* x_55; obj* x_56; uint8 x_57; 
x_54 = lean::cnstr_get(x_49, 1);
lean::inc(x_54);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_55 = x_49;
} else {
 lean::dec_ref(x_49);
 x_55 = lean::box(0);
}
x_56 = lean::array_get_size(x_54);
x_57 = lean::nat_dec_eq(x_56, x_42);
lean::dec(x_56);
if (x_57 == 0)
{
obj* x_58; obj* x_59; obj* x_60; 
x_58 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_58, 0, x_54);
x_59 = lean::array_fset(x_48, x_45, x_58);
lean::dec(x_45);
if (lean::is_scalar(x_55)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_55;
}
lean::cnstr_set(x_60, 0, x_50);
lean::cnstr_set(x_60, 1, x_59);
return x_60;
}
else
{
obj* x_61; uint8 x_62; 
lean::dec(x_54);
lean::dec(x_45);
x_61 = lean::array_pop(x_48);
x_62 = l_Array_isEmpty___rarg(x_61);
if (x_62 == 0)
{
obj* x_63; 
if (lean::is_scalar(x_55)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_55;
}
lean::cnstr_set(x_63, 0, x_50);
lean::cnstr_set(x_63, 1, x_61);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
lean::dec(x_61);
x_64 = l_PersistentArray_empty___closed__1;
if (lean::is_scalar(x_55)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_55;
}
lean::cnstr_set(x_65, 0, x_50);
lean::cnstr_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
obj* x_66; 
lean::dec(x_41);
lean::dec(x_40);
x_66 = l_PersistentArray_popLeaf___main___rarg___closed__1;
return x_66;
}
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_67 = lean::cnstr_get(x_1, 0);
lean::inc(x_67);
lean::dec(x_1);
x_68 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_68, 0, x_67);
x_69 = l_PersistentArray_empty___closed__1;
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_69);
return x_70;
}
}
}
obj* l_PersistentArray_popLeaf___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_popLeaf___main___rarg), 1, 0);
return x_2;
}
}
obj* l_PersistentArray_popLeaf___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentArray_popLeaf___main___rarg(x_1);
return x_2;
}
}
obj* l_PersistentArray_popLeaf(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_popLeaf___rarg), 1, 0);
return x_2;
}
}
obj* l_PersistentArray_pop___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; usize x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 2);
lean::inc(x_4);
x_5 = lean::cnstr_get_usize(x_1, 4);
x_6 = lean::cnstr_get(x_1, 3);
lean::inc(x_6);
x_7 = lean::array_get_size(x_3);
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::nat_dec_lt(x_8, x_7);
lean::dec(x_7);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
lean::dec(x_6);
lean::dec(x_3);
x_10 = l_PersistentArray_popLeaf___main___rarg(x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
lean::dec(x_10);
lean::dec(x_4);
return x_1;
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_1);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; 
x_13 = lean::cnstr_get(x_1, 3);
lean::dec(x_13);
x_14 = lean::cnstr_get(x_1, 2);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_1, 1);
lean::dec(x_15);
x_16 = lean::cnstr_get(x_1, 0);
lean::dec(x_16);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
lean::dec(x_10);
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
lean::dec(x_11);
x_19 = lean::array_pop(x_18);
x_20 = lean::mk_nat_obj(1u);
x_21 = lean::nat_sub(x_4, x_20);
lean::dec(x_4);
x_22 = lean::array_get_size(x_19);
x_23 = lean::nat_sub(x_21, x_22);
lean::dec(x_22);
x_24 = lean::array_get_size(x_17);
x_25 = lean::nat_dec_eq(x_24, x_20);
lean::dec(x_24);
if (x_25 == 0)
{
obj* x_26; 
x_26 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_26, 0, x_17);
lean::cnstr_set(x_1, 3, x_23);
lean::cnstr_set(x_1, 2, x_21);
lean::cnstr_set(x_1, 1, x_19);
lean::cnstr_set(x_1, 0, x_26);
return x_1;
}
else
{
obj* x_27; obj* x_28; uint8 x_29; 
x_27 = l_PersistentArray_getAux___main___rarg___closed__1;
x_28 = lean::array_get(x_27, x_17, x_8);
x_29 = l_PersistentArrayNode_isNode___rarg(x_28);
if (x_29 == 0)
{
obj* x_30; 
lean::dec(x_28);
x_30 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_30, 0, x_17);
lean::cnstr_set(x_1, 3, x_23);
lean::cnstr_set(x_1, 2, x_21);
lean::cnstr_set(x_1, 1, x_19);
lean::cnstr_set(x_1, 0, x_30);
return x_1;
}
else
{
usize x_31; usize x_32; 
lean::dec(x_17);
x_31 = 5;
x_32 = x_5 - x_31;
lean::cnstr_set(x_1, 3, x_23);
lean::cnstr_set(x_1, 2, x_21);
lean::cnstr_set(x_1, 1, x_19);
lean::cnstr_set(x_1, 0, x_28);
lean::cnstr_set_usize(x_1, 4, x_32);
return x_1;
}
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; uint8 x_41; 
lean::dec(x_1);
x_33 = lean::cnstr_get(x_10, 1);
lean::inc(x_33);
lean::dec(x_10);
x_34 = lean::cnstr_get(x_11, 0);
lean::inc(x_34);
lean::dec(x_11);
x_35 = lean::array_pop(x_34);
x_36 = lean::mk_nat_obj(1u);
x_37 = lean::nat_sub(x_4, x_36);
lean::dec(x_4);
x_38 = lean::array_get_size(x_35);
x_39 = lean::nat_sub(x_37, x_38);
lean::dec(x_38);
x_40 = lean::array_get_size(x_33);
x_41 = lean::nat_dec_eq(x_40, x_36);
lean::dec(x_40);
if (x_41 == 0)
{
obj* x_42; obj* x_43; 
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_33);
x_43 = lean::alloc_cnstr(0, 4, sizeof(size_t)*1);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_35);
lean::cnstr_set(x_43, 2, x_37);
lean::cnstr_set(x_43, 3, x_39);
lean::cnstr_set_usize(x_43, 4, x_5);
return x_43;
}
else
{
obj* x_44; obj* x_45; uint8 x_46; 
x_44 = l_PersistentArray_getAux___main___rarg___closed__1;
x_45 = lean::array_get(x_44, x_33, x_8);
x_46 = l_PersistentArrayNode_isNode___rarg(x_45);
if (x_46 == 0)
{
obj* x_47; obj* x_48; 
lean::dec(x_45);
x_47 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_47, 0, x_33);
x_48 = lean::alloc_cnstr(0, 4, sizeof(size_t)*1);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_35);
lean::cnstr_set(x_48, 2, x_37);
lean::cnstr_set(x_48, 3, x_39);
lean::cnstr_set_usize(x_48, 4, x_5);
return x_48;
}
else
{
usize x_49; usize x_50; obj* x_51; 
lean::dec(x_33);
x_49 = 5;
x_50 = x_5 - x_49;
x_51 = lean::alloc_cnstr(0, 4, sizeof(size_t)*1);
lean::cnstr_set(x_51, 0, x_45);
lean::cnstr_set(x_51, 1, x_35);
lean::cnstr_set(x_51, 2, x_37);
lean::cnstr_set(x_51, 3, x_39);
lean::cnstr_set_usize(x_51, 4, x_50);
return x_51;
}
}
}
}
}
else
{
uint8 x_52; 
x_52 = !lean::is_exclusive(x_1);
if (x_52 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_53 = lean::cnstr_get(x_1, 3);
lean::dec(x_53);
x_54 = lean::cnstr_get(x_1, 2);
lean::dec(x_54);
x_55 = lean::cnstr_get(x_1, 1);
lean::dec(x_55);
x_56 = lean::cnstr_get(x_1, 0);
lean::dec(x_56);
x_57 = lean::array_pop(x_3);
x_58 = lean::mk_nat_obj(1u);
x_59 = lean::nat_sub(x_4, x_58);
lean::dec(x_4);
lean::cnstr_set(x_1, 2, x_59);
lean::cnstr_set(x_1, 1, x_57);
return x_1;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_1);
x_60 = lean::array_pop(x_3);
x_61 = lean::mk_nat_obj(1u);
x_62 = lean::nat_sub(x_4, x_61);
lean::dec(x_4);
x_63 = lean::alloc_cnstr(0, 4, sizeof(size_t)*1);
lean::cnstr_set(x_63, 0, x_2);
lean::cnstr_set(x_63, 1, x_60);
lean::cnstr_set(x_63, 2, x_62);
lean::cnstr_set(x_63, 3, x_6);
lean::cnstr_set_usize(x_63, 4, x_5);
return x_63;
}
}
}
}
obj* l_PersistentArray_pop(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_pop___rarg), 1, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_5);
x_9 = lean::nat_dec_lt(x_6, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
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
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
x_14 = lean::array_fget(x_5, x_6);
lean::inc(x_3);
lean::inc(x_1);
x_15 = l_PersistentArray_mfoldlAux___main___rarg(x_1, lean::box(0), x_3, x_14, x_7);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_6, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__1___rarg___boxed), 7, 6);
lean::closure_set(x_18, 0, x_1);
lean::closure_set(x_18, 1, lean::box(0));
lean::closure_set(x_18, 2, x_3);
lean::closure_set(x_18, 3, x_4);
lean::closure_set(x_18, 4, x_5);
lean::closure_set(x_18, 5, x_17);
x_19 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_15, x_18);
return x_19;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_5);
x_9 = lean::nat_dec_lt(x_6, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
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
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
x_14 = lean::array_fget(x_5, x_6);
lean::inc(x_3);
x_15 = lean::apply_2(x_3, x_7, x_14);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_6, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__2___rarg___boxed), 7, 6);
lean::closure_set(x_18, 0, x_1);
lean::closure_set(x_18, 1, lean::box(0));
lean::closure_set(x_18, 2, x_3);
lean::closure_set(x_18, 3, x_4);
lean::closure_set(x_18, 4, x_5);
lean::closure_set(x_18, 5, x_17);
x_19 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_15, x_18);
return x_19;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__2___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_PersistentArray_mfoldlAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = lean::mk_nat_obj(0u);
lean::inc(x_6);
x_8 = l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__1___rarg(x_1, lean::box(0), x_3, x_6, x_6, x_7, x_5);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_10 = lean::mk_nat_obj(0u);
lean::inc(x_9);
x_11 = l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__2___rarg(x_1, lean::box(0), x_3, x_9, x_9, x_10, x_5);
return x_11;
}
}
}
obj* l_PersistentArray_mfoldlAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldlAux___main___rarg), 5, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
return x_8;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
return x_8;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterateAux___main___at_PersistentArray_mfoldlAux___main___spec__2(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mfoldlAux___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfoldlAux___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mfoldlAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_PersistentArray_mfoldlAux___main___rarg(x_1, lean::box(0), x_3, x_4, x_5);
return x_6;
}
}
obj* l_PersistentArray_mfoldlAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldlAux___rarg), 5, 0);
return x_3;
}
}
obj* l_PersistentArray_mfoldlAux___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfoldlAux(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldl___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_5);
x_9 = lean::nat_dec_lt(x_6, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
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
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
x_14 = lean::array_fget(x_5, x_6);
lean::inc(x_4);
x_15 = lean::apply_2(x_4, x_7, x_14);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_6, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_mfoldl___spec__1___rarg___boxed), 7, 6);
lean::closure_set(x_18, 0, x_1);
lean::closure_set(x_18, 1, lean::box(0));
lean::closure_set(x_18, 2, x_3);
lean::closure_set(x_18, 3, x_4);
lean::closure_set(x_18, 4, x_5);
lean::closure_set(x_18, 5, x_17);
x_19 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_15, x_18);
return x_19;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldl___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_mfoldl___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_PersistentArray_mfoldl___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_miterateAux___main___at_PersistentArray_mfoldl___spec__1___rarg(x_2, lean::box(0), x_1, x_3, x_5, x_6, x_4);
return x_7;
}
}
obj* l_PersistentArray_mfoldl___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
lean::inc(x_4);
lean::inc(x_1);
x_8 = l_PersistentArray_mfoldlAux___main___rarg(x_1, lean::box(0), x_4, x_7, x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldl___rarg___lambda__1), 4, 3);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_1);
lean::closure_set(x_9, 2, x_4);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_PersistentArray_mfoldl(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldl___rarg), 5, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldl___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterateAux___main___at_PersistentArray_mfoldl___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
return x_8;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldl___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterateAux___main___at_PersistentArray_mfoldl___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mfoldl___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfoldl(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_1, x_6);
x_8 = l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1___rarg(x_2, lean::box(0), x_3, x_4, x_7);
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
obj* l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_4);
x_7 = lean::nat_dec_lt(x_5, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_10 = lean::box(0);
x_11 = lean::apply_2(x_9, lean::box(0), x_10);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_13 = lean::array_fget(x_4, x_5);
lean::inc(x_3);
lean::inc(x_1);
x_14 = l_PersistentArray_mfindAux___main___rarg(x_1, lean::box(0), x_3, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_15, 0, x_5);
lean::closure_set(x_15, 1, x_1);
lean::closure_set(x_15, 2, x_3);
lean::closure_set(x_15, 3, x_4);
x_16 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_14, x_15);
return x_16;
}
}
}
obj* l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1___rarg), 5, 0);
return x_3;
}
}
obj* l_PersistentArray_mfindAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1___rarg(x_1, lean::box(0), x_3, x_5, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_Array_mfindAux___main___rarg(x_1, lean::box(0), x_8, x_3, x_9);
return x_10;
}
}
}
obj* l_PersistentArray_mfindAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfindAux___main___rarg), 4, 0);
return x_3;
}
}
obj* l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mfindAux___main___at_PersistentArray_mfindAux___main___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mfindAux___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfindAux___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mfindAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentArray_mfindAux___main___rarg(x_1, lean::box(0), x_3, x_4);
return x_5;
}
}
obj* l_PersistentArray_mfindAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfindAux___rarg), 4, 0);
return x_3;
}
}
obj* l_PersistentArray_mfindAux___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfindAux(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mfind___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_mfindAux___main___rarg(x_2, lean::box(0), x_5, x_3, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_3);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_10 = lean::apply_2(x_9, lean::box(0), x_4);
return x_10;
}
}
}
obj* l_PersistentArray_mfind___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::inc(x_4);
lean::inc(x_1);
x_7 = l_PersistentArray_mfindAux___main___rarg(x_1, lean::box(0), x_4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfind___rarg___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_3);
lean::closure_set(x_8, 1, x_1);
lean::closure_set(x_8, 2, x_4);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_PersistentArray_mfind(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfind___rarg), 4, 0);
return x_3;
}
}
obj* l_PersistentArray_mfind___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfind(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; 
x_6 = l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___rarg(x_1, lean::box(0), x_2, x_3, x_4, lean::box(0));
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::apply_2(x_8, lean::box(0), x_5);
return x_9;
}
}
}
obj* l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::nat_dec_lt(x_7, x_5);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_4);
lean::dec(x_3);
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
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_5, x_13);
x_15 = lean::cnstr_get(x_1, 1);
lean::inc(x_15);
x_16 = lean::array_fget(x_4, x_14);
lean::inc(x_3);
lean::inc(x_1);
x_17 = l_PersistentArray_mfindRevAux___main___rarg(x_1, lean::box(0), x_3, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_18, 0, x_1);
lean::closure_set(x_18, 1, x_3);
lean::closure_set(x_18, 2, x_4);
lean::closure_set(x_18, 3, x_14);
x_19 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
}
}
obj* l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_PersistentArray_mfindRevAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::array_get_size(x_5);
x_7 = l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___rarg(x_1, lean::box(0), x_3, x_5, x_6, lean::box(0));
lean::dec(x_6);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_9 = lean::array_get_size(x_8);
x_10 = l_Array_mfindRevAux___main___rarg(x_1, lean::box(0), x_8, x_3, x_9, lean::box(0));
lean::dec(x_9);
return x_10;
}
}
}
obj* l_PersistentArray_mfindRevAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfindRevAux___main___rarg), 4, 0);
return x_3;
}
}
obj* l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
return x_7;
}
}
obj* l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mfindRevAux___main___at_PersistentArray_mfindRevAux___main___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mfindRevAux___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfindRevAux___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mfindRevAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentArray_mfindRevAux___main___rarg(x_1, lean::box(0), x_3, x_4);
return x_5;
}
}
obj* l_PersistentArray_mfindRevAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfindRevAux___rarg), 4, 0);
return x_3;
}
}
obj* l_PersistentArray_mfindRevAux___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfindRevAux(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mfindRev___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = l_PersistentArray_mfindRevAux___main___rarg(x_2, lean::box(0), x_3, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::apply_2(x_8, lean::box(0), x_4);
return x_9;
}
}
}
obj* l_PersistentArray_mfindRev___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_7 = lean::array_get_size(x_6);
lean::inc(x_4);
lean::inc(x_1);
x_8 = l_Array_mfindRevAux___main___rarg(x_1, lean::box(0), x_6, x_4, x_7, lean::box(0));
lean::dec(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfindRev___rarg___lambda__1), 4, 3);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_1);
lean::closure_set(x_9, 2, x_4);
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_PersistentArray_mfindRev(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfindRev___rarg), 4, 0);
return x_3;
}
}
obj* l_PersistentArray_mfindRev___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfindRev(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_5);
x_9 = lean::nat_dec_lt(x_6, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
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
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
x_14 = lean::array_fget(x_5, x_6);
lean::inc(x_3);
lean::inc(x_1);
x_15 = l_PersistentArray_mfoldlAux___main___rarg(x_1, lean::box(0), x_3, x_14, x_7);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_6, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__1___rarg___boxed), 7, 6);
lean::closure_set(x_18, 0, x_1);
lean::closure_set(x_18, 1, lean::box(0));
lean::closure_set(x_18, 2, x_3);
lean::closure_set(x_18, 3, x_4);
lean::closure_set(x_18, 4, x_5);
lean::closure_set(x_18, 5, x_17);
x_19 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_15, x_18);
return x_19;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_5);
x_9 = lean::nat_dec_lt(x_6, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
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
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
x_14 = lean::array_fget(x_5, x_6);
lean::inc(x_3);
x_15 = lean::apply_2(x_3, x_7, x_14);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_6, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__2___rarg___boxed), 7, 6);
lean::closure_set(x_18, 0, x_1);
lean::closure_set(x_18, 1, lean::box(0));
lean::closure_set(x_18, 2, x_3);
lean::closure_set(x_18, 3, x_4);
lean::closure_set(x_18, 4, x_5);
lean::closure_set(x_18, 5, x_17);
x_19 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_15, x_18);
return x_19;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__2___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_PersistentArray_mfoldlFromAux___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_1, x_6);
lean::inc(x_4);
x_8 = l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__1___rarg(x_2, lean::box(0), x_3, x_4, x_4, x_7, x_5);
lean::dec(x_7);
return x_8;
}
}
obj* l_PersistentArray_mfoldlFromAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, usize x_5, usize x_6, obj* x_7) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; usize x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; usize x_14; usize x_15; usize x_16; usize x_17; usize x_18; usize x_19; obj* x_20; obj* x_21; obj* x_22; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_9 = x_5 >> x_6;
x_10 = lean::usize_to_nat(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
x_12 = l_PersistentArray_getAux___main___rarg___closed__1;
x_13 = lean::array_get(x_12, x_8, x_10);
x_14 = 1;
x_15 = x_14 << x_6;
x_16 = x_15 - x_14;
x_17 = x_5 & x_16;
x_18 = 5;
x_19 = x_6 - x_18;
lean::inc(x_3);
lean::inc(x_1);
x_20 = l_PersistentArray_mfoldlFromAux___main___rarg(x_1, lean::box(0), x_3, x_13, x_17, x_19, x_7);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldlFromAux___main___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_21, 0, x_10);
lean::closure_set(x_21, 1, x_1);
lean::closure_set(x_21, 2, x_3);
lean::closure_set(x_21, 3, x_8);
x_22 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_20, x_21);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = lean::cnstr_get(x_4, 0);
lean::inc(x_23);
lean::dec(x_4);
x_24 = lean::usize_to_nat(x_5);
lean::inc(x_23);
x_25 = l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__2___rarg(x_1, lean::box(0), x_3, x_23, x_23, x_24, x_7);
lean::dec(x_24);
return x_25;
}
}
}
obj* l_PersistentArray_mfoldlFromAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldlFromAux___main___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
return x_8;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
return x_8;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterateAux___main___at_PersistentArray_mfoldlFromAux___main___spec__2(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mfoldlFromAux___main___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_PersistentArray_mfoldlFromAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_PersistentArray_mfoldlFromAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
usize x_8; usize x_9; obj* x_10; 
x_8 = lean::unbox_size_t(x_5);
lean::dec(x_5);
x_9 = lean::unbox_size_t(x_6);
lean::dec(x_6);
x_10 = l_PersistentArray_mfoldlFromAux___main___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
obj* l_PersistentArray_mfoldlFromAux___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfoldlFromAux___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mfoldlFromAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, usize x_5, usize x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_PersistentArray_mfoldlFromAux___main___rarg(x_1, lean::box(0), x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
obj* l_PersistentArray_mfoldlFromAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldlFromAux___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_PersistentArray_mfoldlFromAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
usize x_8; usize x_9; obj* x_10; 
x_8 = lean::unbox_size_t(x_5);
lean::dec(x_5);
x_9 = lean::unbox_size_t(x_6);
lean::dec(x_6);
x_10 = l_PersistentArray_mfoldlFromAux___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
obj* l_PersistentArray_mfoldlFromAux___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfoldlFromAux(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_5);
x_9 = lean::nat_dec_lt(x_6, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
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
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
x_14 = lean::array_fget(x_5, x_6);
lean::inc(x_4);
x_15 = lean::apply_2(x_4, x_7, x_14);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_6, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__1___rarg___boxed), 7, 6);
lean::closure_set(x_18, 0, x_1);
lean::closure_set(x_18, 1, lean::box(0));
lean::closure_set(x_18, 2, x_3);
lean::closure_set(x_18, 3, x_4);
lean::closure_set(x_18, 4, x_5);
lean::closure_set(x_18, 5, x_17);
x_19 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_15, x_18);
return x_19;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_5);
x_9 = lean::nat_dec_lt(x_6, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
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
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
x_14 = lean::array_fget(x_5, x_6);
lean::inc(x_4);
x_15 = lean::apply_2(x_4, x_7, x_14);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_6, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__2___rarg___boxed), 7, 6);
lean::closure_set(x_18, 0, x_1);
lean::closure_set(x_18, 1, lean::box(0));
lean::closure_set(x_18, 2, x_3);
lean::closure_set(x_18, 3, x_4);
lean::closure_set(x_18, 4, x_5);
lean::closure_set(x_18, 5, x_17);
x_19 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_15, x_18);
return x_19;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__2___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_PersistentArray_mfoldlFrom___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__1___rarg(x_2, lean::box(0), x_1, x_3, x_5, x_6, x_4);
return x_7;
}
}
obj* l_PersistentArray_mfoldlFrom___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::cnstr_get(x_3, 3);
lean::inc(x_7);
x_8 = lean::nat_dec_le(x_7, x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; usize x_11; usize x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
x_11 = lean::usize_of_nat(x_6);
x_12 = lean::cnstr_get_usize(x_3, 4);
lean::inc(x_4);
lean::inc(x_1);
x_13 = l_PersistentArray_mfoldlFromAux___main___rarg(x_1, lean::box(0), x_4, x_10, x_11, x_12, x_5);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldlFrom___rarg___lambda__1), 4, 3);
lean::closure_set(x_14, 0, x_3);
lean::closure_set(x_14, 1, x_1);
lean::closure_set(x_14, 2, x_4);
x_15 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
else
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::cnstr_get(x_3, 1);
lean::inc(x_16);
x_17 = lean::nat_sub(x_6, x_7);
lean::dec(x_7);
x_18 = l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__2___rarg(x_1, lean::box(0), x_3, x_4, x_16, x_17, x_5);
lean::dec(x_17);
return x_18;
}
}
}
obj* l_PersistentArray_mfoldlFrom(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldlFrom___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
return x_8;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
return x_8;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterateAux___main___at_PersistentArray_mfoldlFrom___spec__2(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mfoldlFrom___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_PersistentArray_mfoldlFrom___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
return x_7;
}
}
obj* l_PersistentArray_mfoldlFrom___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfoldlFrom(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_mforAux___main___at_PersistentArray_mforAux___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_4);
x_7 = lean::nat_dec_lt(x_5, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_3);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_10 = lean::box(0);
x_11 = lean::apply_2(x_9, lean::box(0), x_10);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::array_fget(x_4, x_5);
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_13, 4);
lean::inc(x_14);
lean::dec(x_13);
lean::inc(x_3);
lean::inc(x_1);
x_15 = l_PersistentArray_mforAux___main___rarg(x_1, lean::box(0), x_3, x_12);
lean::dec(x_12);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_5, x_16);
x_18 = l_Array_mforAux___main___at_PersistentArray_mforAux___main___spec__1___rarg(x_1, lean::box(0), x_3, x_4, x_17);
lean::dec(x_17);
x_19 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_15, x_18);
return x_19;
}
}
}
obj* l_Array_mforAux___main___at_PersistentArray_mforAux___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mforAux___main___at_PersistentArray_mforAux___main___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_PersistentArray_mforAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_4, 0);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_mforAux___main___at_PersistentArray_mforAux___main___spec__1___rarg(x_1, lean::box(0), x_3, x_5, x_6);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_4, 0);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_Array_mforAux___main___rarg(x_1, lean::box(0), lean::box(0), x_3, x_8, x_9);
return x_10;
}
}
}
obj* l_PersistentArray_mforAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mforAux___main___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_Array_mforAux___main___at_PersistentArray_mforAux___main___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_mforAux___main___at_PersistentArray_mforAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_Array_mforAux___main___at_PersistentArray_mforAux___main___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mforAux___main___at_PersistentArray_mforAux___main___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mforAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentArray_mforAux___main___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_PersistentArray_mforAux___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mforAux___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mforAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentArray_mforAux___main___rarg(x_1, lean::box(0), x_3, x_4);
return x_5;
}
}
obj* l_PersistentArray_mforAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mforAux___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_PersistentArray_mforAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentArray_mforAux___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_PersistentArray_mforAux___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mforAux(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mfor___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_5, 4);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::inc(x_1);
x_8 = l_PersistentArray_mforAux___main___rarg(x_1, lean::box(0), x_4, x_7);
x_9 = lean::cnstr_get(x_3, 1);
x_10 = lean::mk_nat_obj(0u);
x_11 = l_Array_mforAux___main___rarg(x_1, lean::box(0), lean::box(0), x_4, x_9, x_10);
x_12 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_11);
return x_12;
}
}
obj* l_PersistentArray_mfor(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfor___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_PersistentArray_mfor___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentArray_mfor___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_PersistentArray_mfor___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfor(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__3___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::array_fget(x_3, x_4);
lean::inc(x_1);
x_9 = l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldl___spec__2___rarg(x_1, x_8, x_5);
lean::dec(x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_foldl___spec__3___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__4___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
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
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_foldl___spec__4___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldl___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterateAux___main___at_PersistentArray_foldl___spec__3___rarg(x_1, x_4, x_4, x_5, x_3);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_2, 0);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_miterateAux___main___at_PersistentArray_foldl___spec__4___rarg(x_1, x_7, x_7, x_8, x_3);
return x_9;
}
}
}
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldl___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldl___spec__2___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__5___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
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
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__5(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_foldl___spec__5___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_PersistentArray_mfoldl___at_PersistentArray_foldl___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_1);
x_5 = l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldl___spec__2___rarg(x_1, x_4, x_3);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_miterateAux___main___at_PersistentArray_foldl___spec__5___rarg(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
obj* l_PersistentArray_mfoldl___at_PersistentArray_foldl___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldl___at_PersistentArray_foldl___spec__1___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_PersistentArray_foldl___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentArray_mfoldl___at_PersistentArray_foldl___spec__1___rarg(x_2, x_1, x_3);
return x_4;
}
}
obj* l_PersistentArray_foldl(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_foldl___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__3___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_PersistentArray_foldl___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__4___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_PersistentArray_foldl___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldl___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldl___spec__2___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldl___spec__5___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_PersistentArray_foldl___spec__5___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_PersistentArray_mfoldl___at_PersistentArray_foldl___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentArray_mfoldl___at_PersistentArray_foldl___spec__1___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_PersistentArray_foldl___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentArray_foldl___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__3___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
x_8 = l_PersistentArray_mfindAux___main___at_PersistentArray_find___spec__2___rarg(x_1, x_7);
lean::dec(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; 
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
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindAux___main___at_PersistentArray_find___spec__3___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__4___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_9; obj* x_10; 
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
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindAux___main___at_PersistentArray_find___spec__4___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_PersistentArray_mfindAux___main___at_PersistentArray_find___spec__2___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_mfindAux___main___at_PersistentArray_find___spec__3___rarg(x_1, x_3, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_mfindAux___main___at_PersistentArray_find___spec__4___rarg(x_1, x_6, x_7);
return x_8;
}
}
}
obj* l_PersistentArray_mfindAux___main___at_PersistentArray_find___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfindAux___main___at_PersistentArray_find___spec__2___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__5___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_9; obj* x_10; 
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
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__5(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindAux___main___at_PersistentArray_find___spec__5___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_PersistentArray_mfind___at_PersistentArray_find___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_1);
x_4 = l_PersistentArray_mfindAux___main___at_PersistentArray_find___spec__2___rarg(x_1, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_mfindAux___main___at_PersistentArray_find___spec__5___rarg(x_1, x_5, x_6);
return x_7;
}
else
{
lean::dec(x_1);
return x_4;
}
}
}
obj* l_PersistentArray_mfind___at_PersistentArray_find___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfind___at_PersistentArray_find___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_PersistentArray_find___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfind___at_PersistentArray_find___spec__1___rarg(x_2, x_1);
return x_3;
}
}
obj* l_PersistentArray_find(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_find___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__3___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mfindAux___main___at_PersistentArray_find___spec__3___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__4___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mfindAux___main___at_PersistentArray_find___spec__4___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_PersistentArray_mfindAux___main___at_PersistentArray_find___spec__2___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfindAux___main___at_PersistentArray_find___spec__2___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_mfindAux___main___at_PersistentArray_find___spec__5___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mfindAux___main___at_PersistentArray_find___spec__5___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_PersistentArray_mfind___at_PersistentArray_find___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfind___at_PersistentArray_find___spec__1___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_find___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_find___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_lt(x_5, x_3);
if (x_6 == 0)
{
obj* x_7; 
lean::dec(x_3);
lean::dec(x_1);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_3, x_8);
lean::dec(x_3);
x_10 = lean::array_fget(x_2, x_9);
lean::inc(x_1);
x_11 = lean::apply_1(x_1, x_10);
if (lean::obj_tag(x_11) == 0)
{
x_3 = x_9;
x_4 = lean::box(0);
goto _start;
}
else
{
lean::dec(x_9);
lean::dec(x_1);
return x_11;
}
}
}
}
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__2___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__4___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_lt(x_5, x_3);
if (x_6 == 0)
{
obj* x_7; 
lean::dec(x_3);
lean::dec(x_1);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_3, x_8);
lean::dec(x_3);
x_10 = lean::array_fget(x_2, x_9);
lean::inc(x_1);
x_11 = l_PersistentArray_mfindRevAux___main___at_PersistentArray_findRev___spec__3___rarg(x_1, x_10);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
x_3 = x_9;
x_4 = lean::box(0);
goto _start;
}
else
{
lean::dec(x_9);
lean::dec(x_1);
return x_11;
}
}
}
}
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__4___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__5___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_lt(x_5, x_3);
if (x_6 == 0)
{
obj* x_7; 
lean::dec(x_3);
lean::dec(x_1);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_3, x_8);
lean::dec(x_3);
x_10 = lean::array_fget(x_2, x_9);
lean::inc(x_1);
x_11 = lean::apply_1(x_1, x_10);
if (lean::obj_tag(x_11) == 0)
{
x_3 = x_9;
x_4 = lean::box(0);
goto _start;
}
else
{
lean::dec(x_9);
lean::dec(x_1);
return x_11;
}
}
}
}
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__5(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__5___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_PersistentArray_mfindRevAux___main___at_PersistentArray_findRev___spec__3___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::array_get_size(x_3);
x_5 = l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__4___rarg(x_1, x_3, x_4, lean::box(0));
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean::array_get_size(x_6);
x_8 = l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__5___rarg(x_1, x_6, x_7, lean::box(0));
return x_8;
}
}
}
obj* l_PersistentArray_mfindRevAux___main___at_PersistentArray_findRev___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfindRevAux___main___at_PersistentArray_findRev___spec__3___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_PersistentArray_mfindRev___at_PersistentArray_findRev___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_2, 1);
x_4 = lean::array_get_size(x_3);
lean::inc(x_1);
x_5 = l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__2___rarg(x_1, x_3, x_4, lean::box(0));
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_2, 0);
x_7 = l_PersistentArray_mfindRevAux___main___at_PersistentArray_findRev___spec__3___rarg(x_1, x_6);
return x_7;
}
else
{
lean::dec(x_1);
return x_5;
}
}
}
obj* l_PersistentArray_mfindRev___at_PersistentArray_findRev___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfindRev___at_PersistentArray_findRev___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_PersistentArray_findRev___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfindRev___at_PersistentArray_findRev___spec__1___rarg(x_2, x_1);
return x_3;
}
}
obj* l_PersistentArray_findRev(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_findRev___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__2___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__4___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__4___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__5___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_mfindRevAux___main___at_PersistentArray_findRev___spec__5___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_PersistentArray_mfindRevAux___main___at_PersistentArray_findRev___spec__3___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfindRevAux___main___at_PersistentArray_findRev___spec__3___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mfindRev___at_PersistentArray_findRev___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfindRev___at_PersistentArray_findRev___spec__1___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_findRev___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_findRev___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__4___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::array_fget(x_3, x_4);
lean::inc(x_1);
x_9 = l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldlFrom___spec__3___rarg(x_1, x_8, x_5);
lean::dec(x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__4___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__5___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
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
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__5(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__5___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldlFrom___spec__3___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__4___rarg(x_1, x_4, x_4, x_5, x_3);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_2, 0);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__5___rarg(x_1, x_7, x_7, x_8, x_3);
return x_9;
}
}
}
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldlFrom___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldlFrom___spec__3___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__6___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::array_fget(x_3, x_4);
lean::inc(x_1);
x_9 = l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldlFrom___spec__3___rarg(x_1, x_8, x_5);
lean::dec(x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__6(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__6___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__7___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
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
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__7(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__7___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_PersistentArray_mfoldlFromAux___main___at_PersistentArray_foldlFrom___spec__2___rarg(obj* x_1, obj* x_2, usize x_3, usize x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; usize x_7; obj* x_8; obj* x_9; obj* x_10; usize x_11; usize x_12; usize x_13; usize x_14; usize x_15; usize x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_6 = lean::cnstr_get(x_2, 0);
x_7 = x_3 >> x_4;
x_8 = lean::usize_to_nat(x_7);
x_9 = l_PersistentArray_getAux___main___rarg___closed__1;
x_10 = lean::array_get(x_9, x_6, x_8);
x_11 = 1;
x_12 = x_11 << x_4;
x_13 = x_12 - x_11;
x_14 = x_3 & x_13;
x_15 = 5;
x_16 = x_4 - x_15;
lean::inc(x_1);
x_17 = l_PersistentArray_mfoldlFromAux___main___at_PersistentArray_foldlFrom___spec__2___rarg(x_1, x_10, x_14, x_16, x_5);
lean::dec(x_10);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_8, x_18);
lean::dec(x_8);
x_20 = l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__6___rarg(x_1, x_6, x_6, x_19, x_17);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_2, 0);
x_22 = lean::usize_to_nat(x_3);
x_23 = l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__7___rarg(x_1, x_21, x_21, x_22, x_5);
return x_23;
}
}
}
obj* l_PersistentArray_mfoldlFromAux___main___at_PersistentArray_foldlFrom___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldlFromAux___main___at_PersistentArray_foldlFrom___spec__2___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__8___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::array_fget(x_3, x_4);
lean::inc(x_2);
x_9 = lean::apply_2(x_2, x_5, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__8(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__8___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__9___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::array_fget(x_3, x_4);
lean::inc(x_2);
x_9 = lean::apply_2(x_2, x_5, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__9(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__9___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_PersistentArray_mfoldlFrom___at_PersistentArray_foldlFrom___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::cnstr_get(x_1, 3);
x_6 = lean::nat_dec_le(x_5, x_4);
if (x_6 == 0)
{
obj* x_7; usize x_8; usize x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::usize_of_nat(x_4);
x_9 = lean::cnstr_get_usize(x_1, 4);
lean::inc(x_2);
x_10 = l_PersistentArray_mfoldlFromAux___main___at_PersistentArray_foldlFrom___spec__2___rarg(x_2, x_7, x_8, x_9, x_3);
x_11 = lean::cnstr_get(x_1, 1);
x_12 = lean::mk_nat_obj(0u);
x_13 = l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__8___rarg(x_1, x_2, x_11, x_12, x_10);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_1, 1);
x_15 = lean::nat_sub(x_4, x_5);
x_16 = l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__9___rarg(x_1, x_2, x_14, x_15, x_3);
return x_16;
}
}
}
obj* l_PersistentArray_mfoldlFrom___at_PersistentArray_foldlFrom___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldlFrom___at_PersistentArray_foldlFrom___spec__1___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_PersistentArray_foldlFrom___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentArray_mfoldlFrom___at_PersistentArray_foldlFrom___spec__1___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_PersistentArray_foldlFrom(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_foldlFrom___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__4___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__5___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__5___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldlFrom___spec__3___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentArray_mfoldlAux___main___at_PersistentArray_foldlFrom___spec__3___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__6___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__6___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__7___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__7___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_PersistentArray_mfoldlFromAux___main___at_PersistentArray_foldlFrom___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
usize x_6; usize x_7; obj* x_8; 
x_6 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_7 = lean::unbox_size_t(x_4);
lean::dec(x_4);
x_8 = l_PersistentArray_mfoldlFromAux___main___at_PersistentArray_foldlFrom___spec__2___rarg(x_1, x_2, x_6, x_7, x_5);
lean::dec(x_2);
return x_8;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__8___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__8___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__9___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_PersistentArray_foldlFrom___spec__9___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l_PersistentArray_mfoldlFrom___at_PersistentArray_foldlFrom___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentArray_mfoldlFrom___at_PersistentArray_foldlFrom___spec__1___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_PersistentArray_foldlFrom___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentArray_foldlFrom___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__3___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = l_PersistentArray_mfoldlAux___main___at_PersistentArray_toList___spec__2___rarg(x_7, x_4);
lean::dec(x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_3, x_9);
lean::dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__3(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_toList___spec__3___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__4___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_3, x_9);
lean::dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__4(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_toList___spec__4___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_toList___spec__2___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_miterateAux___main___at_PersistentArray_toList___spec__3___rarg(x_3, x_3, x_4, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_miterateAux___main___at_PersistentArray_toList___spec__4___rarg(x_6, x_6, x_7, x_2);
return x_8;
}
}
}
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_toList___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldlAux___main___at_PersistentArray_toList___spec__2___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__5___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_3, x_9);
lean::dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__5(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_toList___spec__5___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_PersistentArray_mfoldl___at_PersistentArray_toList___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = l_PersistentArray_mfoldlAux___main___at_PersistentArray_toList___spec__2___rarg(x_3, x_2);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_miterateAux___main___at_PersistentArray_toList___spec__5___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
obj* l_PersistentArray_mfoldl___at_PersistentArray_toList___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mfoldl___at_PersistentArray_toList___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_PersistentArray_toList___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box(0);
x_3 = l_PersistentArray_mfoldl___at_PersistentArray_toList___spec__1___rarg(x_1, x_2);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
}
obj* l_PersistentArray_toList(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_toList___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__3___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_PersistentArray_toList___spec__3___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__4___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_PersistentArray_toList___spec__4___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_PersistentArray_mfoldlAux___main___at_PersistentArray_toList___spec__2___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfoldlAux___main___at_PersistentArray_toList___spec__2___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_toList___spec__5___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_PersistentArray_toList___spec__5___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_PersistentArray_mfoldl___at_PersistentArray_toList___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mfoldl___at_PersistentArray_toList___spec__1___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_PersistentArray_toList___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentArray_toList___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_1, x_7);
x_9 = x_6;
x_10 = lean::array_fset(x_3, x_1, x_9);
x_11 = l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1___rarg(x_4, lean::box(0), x_5, x_8, x_10);
return x_11;
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_5);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_4);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_10 = l_Array_empty___closed__1;
x_11 = x_5;
x_12 = lean::apply_2(x_9, lean::box(0), x_11);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::array_fget(x_5, x_4);
x_14 = lean::box(0);
lean::inc(x_13);
x_15 = x_14;
x_16 = lean::array_fset(x_5, x_4, x_15);
x_17 = lean::cnstr_get(x_1, 1);
lean::inc(x_17);
lean::inc(x_13);
lean::inc(x_3);
lean::inc(x_1);
x_18 = l_PersistentArray_mmapAux___main___rarg(x_1, lean::box(0), x_3, x_13);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_19, 0, x_4);
lean::closure_set(x_19, 1, x_13);
lean::closure_set(x_19, 2, x_16);
lean::closure_set(x_19, 3, x_1);
lean::closure_set(x_19, 4, x_3);
x_20 = lean::apply_4(x_17, lean::box(0), lean::box(0), x_18, x_19);
return x_20;
}
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1___rarg), 5, 0);
return x_3;
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_1, x_7);
x_9 = x_6;
x_10 = lean::array_fset(x_3, x_1, x_9);
x_11 = l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2___rarg(x_4, lean::box(0), x_5, x_8, x_10);
return x_11;
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_5);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_4);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_10 = l_Array_empty___closed__1;
x_11 = x_5;
x_12 = lean::apply_2(x_9, lean::box(0), x_11);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::array_fget(x_5, x_4);
x_14 = lean::box(0);
lean::inc(x_13);
x_15 = x_14;
x_16 = lean::array_fset(x_5, x_4, x_15);
x_17 = lean::cnstr_get(x_1, 1);
lean::inc(x_17);
lean::inc(x_3);
lean::inc(x_13);
x_18 = lean::apply_1(x_3, x_13);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_19, 0, x_4);
lean::closure_set(x_19, 1, x_13);
lean::closure_set(x_19, 2, x_16);
lean::closure_set(x_19, 3, x_1);
lean::closure_set(x_19, 4, x_3);
x_20 = lean::apply_4(x_17, lean::box(0), lean::box(0), x_18, x_19);
return x_20;
}
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2___rarg), 5, 0);
return x_3;
}
}
obj* l_PersistentArray_mmapAux___main___rarg___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_PersistentArray_mmapAux___main___rarg___lambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_PersistentArray_mmapAux___main___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mmapAux___main___rarg___lambda__1), 1, 0);
return x_1;
}
}
obj* _init_l_PersistentArray_mmapAux___main___rarg___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mmapAux___main___rarg___lambda__2), 1, 0);
return x_1;
}
}
obj* l_PersistentArray_mmapAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1___rarg(x_1, lean::box(0), x_3, x_9, x_5);
x_11 = l_PersistentArray_mmapAux___main___rarg___closed__1;
x_12 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_11, x_10);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_4, 0);
lean::inc(x_13);
lean::dec(x_4);
x_14 = lean::cnstr_get(x_1, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
lean::dec(x_14);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
x_17 = lean::mk_nat_obj(0u);
x_18 = l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2___rarg(x_1, lean::box(0), x_3, x_17, x_13);
x_19 = l_PersistentArray_mmapAux___main___rarg___closed__2;
x_20 = lean::apply_4(x_16, lean::box(0), lean::box(0), x_19, x_18);
return x_20;
}
}
}
obj* l_PersistentArray_mmapAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mmapAux___main___rarg), 4, 0);
return x_3;
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
return x_7;
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
return x_7;
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_ummapAux___main___at_PersistentArray_mmapAux___main___spec__2(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mmapAux___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mmapAux___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mmapAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentArray_mmapAux___main___rarg(x_1, lean::box(0), x_3, x_4);
return x_5;
}
}
obj* l_PersistentArray_mmapAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mmapAux___rarg), 4, 0);
return x_3;
}
}
obj* l_PersistentArray_mmapAux___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mmapAux(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_1, x_7);
x_9 = x_6;
x_10 = lean::array_fset(x_3, x_1, x_9);
x_11 = l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1___rarg(x_4, lean::box(0), x_5, x_8, x_10);
return x_11;
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_5);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_4);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_10 = l_Array_empty___closed__1;
x_11 = x_5;
x_12 = lean::apply_2(x_9, lean::box(0), x_11);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::array_fget(x_5, x_4);
x_14 = lean::box(0);
lean::inc(x_13);
x_15 = x_14;
x_16 = lean::array_fset(x_5, x_4, x_15);
x_17 = lean::cnstr_get(x_1, 1);
lean::inc(x_17);
lean::inc(x_3);
lean::inc(x_13);
x_18 = lean::apply_1(x_3, x_13);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_19, 0, x_4);
lean::closure_set(x_19, 1, x_13);
lean::closure_set(x_19, 2, x_16);
lean::closure_set(x_19, 3, x_1);
lean::closure_set(x_19, 4, x_3);
x_20 = lean::apply_4(x_17, lean::box(0), lean::box(0), x_18, x_19);
return x_20;
}
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1___rarg), 5, 0);
return x_3;
}
}
obj* l_PersistentArray_mmap___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; usize x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::cnstr_get(x_2, 2);
x_8 = lean::cnstr_get_usize(x_2, 4);
x_9 = lean::cnstr_get(x_2, 3);
lean::inc(x_9);
lean::inc(x_7);
x_10 = lean::alloc_cnstr(0, 4, sizeof(size_t)*1);
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_4);
lean::cnstr_set(x_10, 2, x_7);
lean::cnstr_set(x_10, 3, x_9);
lean::cnstr_set_usize(x_10, 4, x_8);
x_11 = lean::apply_2(x_6, lean::box(0), x_10);
return x_11;
}
}
obj* l_PersistentArray_mmap___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_7 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_8 = l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1___rarg(x_2, lean::box(0), x_3, x_7, x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mmap___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_9, 0, x_2);
lean::closure_set(x_9, 1, x_1);
lean::closure_set(x_9, 2, x_5);
x_10 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_PersistentArray_mmap___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::inc(x_3);
lean::inc(x_1);
x_7 = l_PersistentArray_mmapAux___main___rarg(x_1, lean::box(0), x_3, x_6);
lean::inc(x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mmap___rarg___lambda__2), 5, 4);
lean::closure_set(x_8, 0, x_4);
lean::closure_set(x_8, 1, x_1);
lean::closure_set(x_8, 2, x_3);
lean::closure_set(x_8, 3, x_5);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_PersistentArray_mmap(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mmap___rarg), 4, 0);
return x_3;
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
return x_7;
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_ummapAux___main___at_PersistentArray_mmap___spec__1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_PersistentArray_mmap___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentArray_mmap___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_PersistentArray_mmap___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mmap(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_map___spec__3___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_8 = lean::array_fget(x_3, x_2);
x_9 = lean::box(0);
lean::inc(x_8);
x_10 = x_9;
x_11 = lean::array_fset(x_3, x_2, x_10);
lean::inc(x_8);
lean::inc(x_1);
x_12 = l_PersistentArray_mmapAux___main___at_PersistentArray_map___spec__2___rarg(x_1, x_8);
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
obj* l_Array_ummapAux___main___at_PersistentArray_map___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_PersistentArray_map___spec__3___rarg), 3, 0);
return x_3;
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_map___spec__4___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
obj* l_Array_ummapAux___main___at_PersistentArray_map___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_PersistentArray_map___spec__4___rarg), 3, 0);
return x_3;
}
}
obj* l_PersistentArray_mmapAux___main___at_PersistentArray_map___spec__2___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_ummapAux___main___at_PersistentArray_map___spec__3___rarg(x_1, x_5, x_4);
lean::cnstr_set(x_2, 0, x_6);
return x_2;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_ummapAux___main___at_PersistentArray_map___spec__3___rarg(x_1, x_8, x_7);
x_10 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_2);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_2, 0);
x_13 = lean::mk_nat_obj(0u);
x_14 = l_Array_ummapAux___main___at_PersistentArray_map___spec__4___rarg(x_1, x_13, x_12);
lean::cnstr_set(x_2, 0, x_14);
return x_2;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
lean::dec(x_2);
x_16 = lean::mk_nat_obj(0u);
x_17 = l_Array_ummapAux___main___at_PersistentArray_map___spec__4___rarg(x_1, x_16, x_15);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
}
}
}
obj* l_PersistentArray_mmapAux___main___at_PersistentArray_map___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mmapAux___main___at_PersistentArray_map___spec__2___rarg), 2, 0);
return x_3;
}
}
obj* l_Array_ummapAux___main___at_PersistentArray_map___spec__5___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
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
obj* l_Array_ummapAux___main___at_PersistentArray_map___spec__5(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_ummapAux___main___at_PersistentArray_map___spec__5___rarg), 3, 0);
return x_3;
}
}
obj* l_PersistentArray_mmap___at_PersistentArray_map___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_1);
x_6 = l_PersistentArray_mmapAux___main___at_PersistentArray_map___spec__2___rarg(x_1, x_4);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_Array_ummapAux___main___at_PersistentArray_map___spec__5___rarg(x_1, x_7, x_5);
lean::cnstr_set(x_2, 1, x_8);
lean::cnstr_set(x_2, 0, x_6);
return x_2;
}
else
{
obj* x_9; obj* x_10; obj* x_11; usize x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_9 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 1);
x_11 = lean::cnstr_get(x_2, 2);
x_12 = lean::cnstr_get_usize(x_2, 4);
x_13 = lean::cnstr_get(x_2, 3);
lean::inc(x_13);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_2);
lean::inc(x_1);
x_14 = l_PersistentArray_mmapAux___main___at_PersistentArray_map___spec__2___rarg(x_1, x_9);
x_15 = lean::mk_nat_obj(0u);
x_16 = l_Array_ummapAux___main___at_PersistentArray_map___spec__5___rarg(x_1, x_15, x_10);
x_17 = lean::alloc_cnstr(0, 4, sizeof(size_t)*1);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set(x_17, 2, x_11);
lean::cnstr_set(x_17, 3, x_13);
lean::cnstr_set_usize(x_17, 4, x_12);
return x_17;
}
}
}
obj* l_PersistentArray_mmap___at_PersistentArray_map___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_mmap___at_PersistentArray_map___spec__1___rarg), 2, 0);
return x_3;
}
}
obj* l_PersistentArray_map___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentArray_mmap___at_PersistentArray_map___spec__1___rarg(x_1, x_2);
return x_3;
}
}
obj* l_PersistentArray_map(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_map___rarg), 2, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_collectStats___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::array_fget(x_3, x_4);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_1, x_9);
x_11 = l_PersistentArray_collectStats___main___rarg(x_8, x_5, x_10);
lean::dec(x_10);
lean::dec(x_8);
x_12 = lean::nat_add(x_4, x_9);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_11;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_collectStats___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentArray_collectStats___main___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_PersistentArray_collectStats___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_6, x_8);
lean::dec(x_6);
x_10 = l_Nat_max(x_3, x_7);
lean::dec(x_7);
lean::cnstr_set(x_2, 1, x_10);
lean::cnstr_set(x_2, 0, x_9);
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Array_miterateAux___main___at_PersistentArray_collectStats___main___spec__1___rarg(x_3, x_5, x_5, x_11, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_13 = lean::cnstr_get(x_1, 0);
x_14 = lean::cnstr_get(x_2, 0);
x_15 = lean::cnstr_get(x_2, 1);
x_16 = lean::cnstr_get(x_2, 2);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_2);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_add(x_14, x_17);
lean::dec(x_14);
x_19 = l_Nat_max(x_3, x_15);
lean::dec(x_15);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
lean::cnstr_set(x_20, 2, x_16);
x_21 = lean::mk_nat_obj(0u);
x_22 = l_Array_miterateAux___main___at_PersistentArray_collectStats___main___spec__1___rarg(x_3, x_13, x_13, x_21, x_20);
return x_22;
}
}
else
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_2);
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_24 = lean::cnstr_get(x_2, 0);
x_25 = lean::cnstr_get(x_2, 1);
x_26 = lean::mk_nat_obj(1u);
x_27 = lean::nat_add(x_24, x_26);
lean::dec(x_24);
x_28 = l_Nat_max(x_3, x_25);
lean::dec(x_25);
lean::cnstr_set(x_2, 1, x_28);
lean::cnstr_set(x_2, 0, x_27);
return x_2;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_29 = lean::cnstr_get(x_2, 0);
x_30 = lean::cnstr_get(x_2, 1);
x_31 = lean::cnstr_get(x_2, 2);
lean::inc(x_31);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_2);
x_32 = lean::mk_nat_obj(1u);
x_33 = lean::nat_add(x_29, x_32);
lean::dec(x_29);
x_34 = l_Nat_max(x_3, x_30);
lean::dec(x_30);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
lean::cnstr_set(x_35, 2, x_31);
return x_35;
}
}
}
}
obj* l_PersistentArray_collectStats___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_collectStats___main___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_PersistentArray_collectStats___main___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_PersistentArray_collectStats___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_PersistentArray_collectStats___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentArray_collectStats___main___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_PersistentArray_collectStats___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentArray_collectStats___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_PersistentArray_collectStats(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_collectStats___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_PersistentArray_collectStats___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentArray_collectStats___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_PersistentArray_stats___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::array_get_size(x_3);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_5);
lean::cnstr_set(x_6, 2, x_4);
x_7 = l_PersistentArray_collectStats___main___rarg(x_2, x_6, x_5);
return x_7;
}
}
obj* l_PersistentArray_stats(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_stats___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_PersistentArray_stats___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentArray_stats___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_PersistentArray_Stats_toString___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("{nodes := ");
return x_1;
}
}
obj* _init_l_PersistentArray_Stats_toString___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(", depth := ");
return x_1;
}
}
obj* _init_l_PersistentArray_Stats_toString___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(", tail size := ");
return x_1;
}
}
obj* _init_l_PersistentArray_Stats_toString___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("}");
return x_1;
}
}
obj* l_PersistentArray_Stats_toString(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Nat_repr(x_2);
x_4 = l_PersistentArray_Stats_toString___closed__1;
x_5 = lean::string_append(x_4, x_3);
lean::dec(x_3);
x_6 = l_PersistentArray_Stats_toString___closed__2;
x_7 = lean::string_append(x_5, x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_9 = l_Nat_repr(x_8);
x_10 = lean::string_append(x_7, x_9);
lean::dec(x_9);
x_11 = l_PersistentArray_Stats_toString___closed__3;
x_12 = lean::string_append(x_10, x_11);
x_13 = lean::cnstr_get(x_1, 2);
lean::inc(x_13);
lean::dec(x_1);
x_14 = l_Nat_repr(x_13);
x_15 = lean::string_append(x_12, x_14);
lean::dec(x_14);
x_16 = l_PersistentArray_Stats_toString___closed__4;
x_17 = lean::string_append(x_15, x_16);
return x_17;
}
}
obj* _init_l_PersistentArray_HasToString___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentArray_Stats_toString), 1, 0);
return x_1;
}
}
obj* _init_l_PersistentArray_HasToString() {
_start:
{
obj* x_1; 
x_1 = l_PersistentArray_HasToString___closed__1;
return x_1;
}
}
obj* l_List_toPersistentArrayAux___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_PersistentArray_push___rarg(x_2, x_3);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
}
}
obj* l_List_toPersistentArrayAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toPersistentArrayAux___main___rarg), 2, 0);
return x_2;
}
}
obj* l_List_toPersistentArrayAux___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_toPersistentArrayAux___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_toPersistentArrayAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toPersistentArrayAux___rarg), 2, 0);
return x_2;
}
}
obj* l_List_toPersistentArray___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_PersistentArray_empty___closed__3;
x_3 = l_List_toPersistentArrayAux___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_List_toPersistentArray(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toPersistentArray___rarg), 1, 0);
return x_2;
}
}
obj* initialize_init_data_array_default(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_persistentarray_basic(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_array_default(w);
if (lean::io_result_is_error(w)) return w;
l_PersistentArrayNode_Inhabited___closed__1 = _init_l_PersistentArrayNode_Inhabited___closed__1();
lean::mark_persistent(l_PersistentArrayNode_Inhabited___closed__1);
l_PersistentArray_initShift = _init_l_PersistentArray_initShift();
l_PersistentArray_branching = _init_l_PersistentArray_branching();
l_PersistentArray_empty___closed__1 = _init_l_PersistentArray_empty___closed__1();
lean::mark_persistent(l_PersistentArray_empty___closed__1);
l_PersistentArray_empty___closed__2 = _init_l_PersistentArray_empty___closed__2();
lean::mark_persistent(l_PersistentArray_empty___closed__2);
l_PersistentArray_empty___closed__3 = _init_l_PersistentArray_empty___closed__3();
lean::mark_persistent(l_PersistentArray_empty___closed__3);
l_PersistentArray_getAux___main___rarg___closed__1 = _init_l_PersistentArray_getAux___main___rarg___closed__1();
lean::mark_persistent(l_PersistentArray_getAux___main___rarg___closed__1);
l_PersistentArray_tooBig___closed__1 = _init_l_PersistentArray_tooBig___closed__1();
lean::mark_persistent(l_PersistentArray_tooBig___closed__1);
l_PersistentArray_tooBig = _init_l_PersistentArray_tooBig();
lean::mark_persistent(l_PersistentArray_tooBig);
l_PersistentArray_popLeaf___main___rarg___closed__1 = _init_l_PersistentArray_popLeaf___main___rarg___closed__1();
lean::mark_persistent(l_PersistentArray_popLeaf___main___rarg___closed__1);
l_PersistentArray_mmapAux___main___rarg___closed__1 = _init_l_PersistentArray_mmapAux___main___rarg___closed__1();
lean::mark_persistent(l_PersistentArray_mmapAux___main___rarg___closed__1);
l_PersistentArray_mmapAux___main___rarg___closed__2 = _init_l_PersistentArray_mmapAux___main___rarg___closed__2();
lean::mark_persistent(l_PersistentArray_mmapAux___main___rarg___closed__2);
l_PersistentArray_Stats_toString___closed__1 = _init_l_PersistentArray_Stats_toString___closed__1();
lean::mark_persistent(l_PersistentArray_Stats_toString___closed__1);
l_PersistentArray_Stats_toString___closed__2 = _init_l_PersistentArray_Stats_toString___closed__2();
lean::mark_persistent(l_PersistentArray_Stats_toString___closed__2);
l_PersistentArray_Stats_toString___closed__3 = _init_l_PersistentArray_Stats_toString___closed__3();
lean::mark_persistent(l_PersistentArray_Stats_toString___closed__3);
l_PersistentArray_Stats_toString___closed__4 = _init_l_PersistentArray_Stats_toString___closed__4();
lean::mark_persistent(l_PersistentArray_Stats_toString___closed__4);
l_PersistentArray_HasToString___closed__1 = _init_l_PersistentArray_HasToString___closed__1();
lean::mark_persistent(l_PersistentArray_HasToString___closed__1);
l_PersistentArray_HasToString = _init_l_PersistentArray_HasToString();
lean::mark_persistent(l_PersistentArray_HasToString);
return w;
}
