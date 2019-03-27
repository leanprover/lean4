// Lean compiler output
// Module: init.data.hashmap.basic
// Imports: init.data.array.basic init.data.list.basic init.data.option.basic init.data.hashable
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
obj* l_HashmapImp_findAux___rarg(obj*, obj*, obj*);
obj* l_HashmapImp_fold(obj*, obj*, obj*);
obj* l_HashmapImp_replaceAux___main___boxed(obj*, obj*);
obj* l_HashmapImp_replaceAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Hashmap_fold___rarg(obj*, obj*, obj*);
uint8 l_Hashmap_empty___rarg(obj*);
obj* l_DHashmap_empty___boxed(obj*, obj*, obj*, obj*);
obj* l_DHashmap_find(obj*, obj*);
obj* l_DHashmap_contains___rarg___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Hashmap_erase___rarg(obj*, obj*, obj*, obj*);
obj* l_DHashmap_insert(obj*, obj*);
obj* l_Hashmap_empty___boxed(obj*, obj*, obj*, obj*);
obj* l_HashmapImp_insert(obj*, obj*);
uint8 l_Option_isSome___main___rarg(obj*);
obj* l_HashmapImp_foldBuckets___boxed(obj*, obj*, obj*);
obj* l_HashmapImp_reinsertAux(obj*, obj*);
uint8 l_HashmapImp_containsAux___rarg(obj*, obj*, obj*);
obj* l_Array_iterateAux___main___at_HashmapImp_foldBuckets___spec__2(obj*, obj*, obj*);
obj* l_Hashmap_find___rarg(obj*, obj*, obj*, obj*);
obj* l_Hashmap_size___boxed(obj*, obj*, obj*, obj*);
obj* l_DHashmap_find___boxed(obj*, obj*);
uint8 l_Hashmap_contains___rarg(obj*, obj*, obj*, obj*);
obj* l_HashmapImp_find___rarg(obj*, obj*, obj*, obj*);
obj* l_HashmapImp_reinsertAux___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_iterateAux___main___at_HashmapImp_foldBuckets___spec__2___boxed(obj*, obj*, obj*);
obj* l_Hashmap_size(obj*, obj*, obj*, obj*);
obj* l_HashmapImp_containsAux(obj*, obj*);
obj* l_mkHashmapImp(obj*, obj*);
obj* l_Hashmap_erase___boxed(obj*, obj*);
obj* l_HashmapImp_erase(obj*, obj*);
obj* l_DHashmap_contains(obj*, obj*);
obj* l_DHashmap_insert___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_HashmapImp_find(obj*, obj*);
obj* l_HashmapImp_mkIdx___boxed(obj*, obj*, obj*);
obj* l_bucketArray_updt___rarg(obj*, usize, obj*, obj*);
obj* l_HashmapImp_replaceAux___boxed(obj*, obj*);
obj* l_List_foldl___main___at_HashmapImp_foldBuckets___spec__1___boxed(obj*, obj*, obj*);
obj* l_HashmapImp_findAux___main___rarg(obj*, obj*, obj*);
obj* l_Array_iterateAux___main___at_HashmapImp_foldBuckets___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_HashmapImp_fold___rarg(obj*, obj*, obj*);
obj* l_HashmapImp_erase___boxed(obj*, obj*);
obj* l_HashmapImp_containsAux___boxed(obj*, obj*);
obj* l_DHashmap_fold(obj*, obj*, obj*, obj*, obj*);
obj* l_Hashmap_fold___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_bucketArray_updt(obj*, obj*);
obj* l_mkHashmap___boxed(obj*, obj*, obj*, obj*);
obj* l_DHashmap_empty___rarg___boxed(obj*);
obj* l_DHashmap_erase(obj*, obj*);
obj* l_DHashmap_contains___boxed(obj*, obj*);
obj* l_Hashmap_insert___boxed(obj*, obj*);
obj* l_HashmapImp_findAux___main(obj*, obj*);
obj* l_HashmapImp_find___boxed(obj*, obj*);
obj* l_mkHashmapImp___rarg(obj*);
obj* l_Hashmap_size___rarg(obj*);
obj* l_HashmapImp_insert___boxed(obj*, obj*);
obj* l_HashmapImp_replaceAux___rarg(obj*, obj*, obj*, obj*);
obj* l_HashmapImp_findAux(obj*, obj*);
obj* l_HashmapImp_insert___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_DHashmap_size(obj*, obj*, obj*, obj*);
obj* l_HashmapImp_erase___rarg(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_HashmapImp_foldBuckets___spec__1(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_mkHashmapImp___boxed(obj*, obj*);
uint8 l_DHashmap_contains___rarg(obj*, obj*, obj*, obj*);
obj* l_HashmapImp_replaceAux___main(obj*, obj*);
obj* l_HashmapImp_reinsertAux___boxed(obj*, obj*);
obj* l_mkHashmap___rarg(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_DHashmap_insert___boxed(obj*, obj*);
obj* l_Hashmap_find(obj*, obj*);
uint8 l_DHashmap_empty___rarg(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_DHashmap_size___rarg(obj*);
obj* l_HashmapImp_foldBuckets___rarg(obj*, obj*, obj*);
obj* l_Hashmap_empty(obj*, obj*, obj*, obj*);
obj* l_HashmapImp_containsAux___rarg___boxed(obj*, obj*, obj*);
obj* l_Hashmap_empty___rarg___boxed(obj*);
obj* l_Hashmap_fold(obj*, obj*, obj*, obj*, obj*);
obj* l_Hashmap_contains(obj*, obj*);
obj* l_Hashmap_size___rarg___boxed(obj*);
obj* l_HashmapImp_findAux___boxed(obj*, obj*);
obj* l_bucketArray_updt___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_mkDHashmap(obj*, obj*, obj*, obj*);
obj* l_mkDHashmap___rarg(obj*);
obj* l_Hashmap_insert(obj*, obj*);
obj* l_HashmapImp_eraseAux___rarg(obj*, obj*, obj*);
obj* l_Hashmap_find___boxed(obj*, obj*);
obj* l_Hashmap_contains___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_HashmapImp_eraseAux___main(obj*, obj*);
obj* l_DHashmap_size___rarg___boxed(obj*);
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_Hashmap_contains___boxed(obj*, obj*);
obj* l_HashmapImp_eraseAux(obj*, obj*);
obj* l_DHashmap_size___boxed(obj*, obj*, obj*, obj*);
obj* l_HashmapImp_eraseAux___boxed(obj*, obj*);
obj* l_Hashmap_erase(obj*, obj*);
usize l_HashmapImp_mkIdx(obj*, obj*, usize);
obj* l_DHashmap_erase___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_DHashmap_find___rarg(obj*, obj*, obj*, obj*);
obj* l_mkHashmapImp___rarg___closed__1;
obj* l_Array_iterateAux___main___at_HashmapImp_foldBuckets___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_HashmapImp_foldBuckets___spec__1___rarg(obj*, obj*, obj*);
obj* l_Hashmap_insert___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_HashmapImp_foldBuckets(obj*, obj*, obj*);
obj* l_DHashmap_empty(obj*, obj*, obj*, obj*);
obj* l_DHashmap_fold___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_DHashmap_fold___rarg(obj*, obj*, obj*);
obj* l_bucketArray_updt___boxed(obj*, obj*);
obj* l_DHashmap_erase___rarg(obj*, obj*, obj*, obj*);
obj* l_HashmapImp_fold___boxed(obj*, obj*, obj*);
obj* l_mkHashmap(obj*, obj*, obj*, obj*);
obj* l_HashmapImp_eraseAux___main___boxed(obj*, obj*);
obj* l_mkDHashmap___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_HashmapImp_replaceAux(obj*, obj*);
obj* l_HashmapImp_eraseAux___main___rarg(obj*, obj*, obj*);
obj* l_HashmapImp_findAux___main___boxed(obj*, obj*);
obj* l_bucketArray_updt___rarg(obj* x_0, usize x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::array_updt(x_0, x_1, x_2);
return x_4;
}
}
obj* l_bucketArray_updt(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_bucketArray_updt___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_bucketArray_updt___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; obj* x_5; 
x_4 = lean::unbox_size_t(x_1);
x_5 = l_bucketArray_updt___rarg(x_0, x_4, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_bucketArray_updt___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_bucketArray_updt(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_mkHashmapImp___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(8ul);
x_2 = lean::mk_array(x_1, x_0);
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_mkHashmapImp___rarg(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::nat_dec_eq(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::box(0);
x_4 = lean::mk_array(x_0, x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
else
{
obj* x_7; 
lean::dec(x_0);
x_7 = l_mkHashmapImp___rarg___closed__1;
return x_7;
}
}
}
obj* l_mkHashmapImp(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_mkHashmapImp___rarg), 1, 0);
return x_2;
}
}
obj* l_mkHashmapImp___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashmapImp(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
usize l_HashmapImp_mkIdx(obj* x_0, obj* x_1, usize x_2) {
_start:
{
usize x_3; 
x_3 = lean::usize_modn(x_2, x_0);
return x_3;
}
}
obj* l_HashmapImp_mkIdx___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_2);
x_4 = l_HashmapImp_mkIdx(x_0, x_1, x_3);
x_5 = lean::box_size_t(x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_HashmapImp_reinsertAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; usize x_8; usize x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::inc(x_1);
x_5 = lean::array_sz(x_1);
lean::inc(x_2);
x_7 = lean::apply_1(x_0, x_2);
x_8 = lean::unbox_size_t(x_7);
x_9 = lean::usize_modn(x_8, x_5);
lean::dec(x_5);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_3);
x_12 = lean::array_idx(x_1, x_9);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::array_updt(x_1, x_9, x_13);
lean::dec(x_13);
lean::dec(x_1);
return x_14;
}
}
obj* l_HashmapImp_reinsertAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashmapImp_reinsertAux___rarg), 4, 0);
return x_2;
}
}
obj* l_HashmapImp_reinsertAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashmapImp_reinsertAux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_foldl___main___at_HashmapImp_foldBuckets___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
lean::inc(x_0);
x_15 = lean::apply_3(x_0, x_1, x_9, x_11);
x_1 = x_15;
x_2 = x_6;
goto _start;
}
}
}
obj* l_List_foldl___main___at_HashmapImp_foldBuckets___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_HashmapImp_foldBuckets___spec__1___rarg), 3, 0);
return x_3;
}
}
obj* l_Array_iterateAux___main___at_HashmapImp_foldBuckets___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; uint8 x_7; 
lean::inc(x_2);
x_6 = lean::array_sz(x_2);
x_7 = lean::nat_dec_lt(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_17; 
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_3, x_12);
x_14 = lean::array_index(x_2, x_3);
lean::dec(x_3);
lean::inc(x_1);
x_17 = l_List_foldl___main___at_HashmapImp_foldBuckets___spec__1___rarg(x_1, x_4, x_14);
x_3 = x_13;
x_4 = x_17;
goto _start;
}
}
}
obj* l_Array_iterateAux___main___at_HashmapImp_foldBuckets___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_iterateAux___main___at_HashmapImp_foldBuckets___spec__2___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_HashmapImp_foldBuckets___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = lean::mk_nat_obj(0ul);
lean::inc(x_0);
x_5 = l_Array_iterateAux___main___at_HashmapImp_foldBuckets___spec__2___rarg(x_0, x_2, x_0, x_3, x_1);
lean::dec(x_0);
return x_5;
}
}
obj* l_HashmapImp_foldBuckets(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashmapImp_foldBuckets___rarg), 3, 0);
return x_3;
}
}
obj* l_List_foldl___main___at_HashmapImp_foldBuckets___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldl___main___at_HashmapImp_foldBuckets___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_iterateAux___main___at_HashmapImp_foldBuckets___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_iterateAux___main___at_HashmapImp_foldBuckets___spec__2___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_Array_iterateAux___main___at_HashmapImp_foldBuckets___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_iterateAux___main___at_HashmapImp_foldBuckets___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_HashmapImp_foldBuckets___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashmapImp_foldBuckets(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_HashmapImp_findAux___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
lean::dec(x_6);
lean::inc(x_1);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_11, x_1);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
lean::dec(x_13);
x_2 = x_8;
goto _start;
}
else
{
obj* x_25; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_13);
return x_25;
}
}
}
}
obj* l_HashmapImp_findAux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashmapImp_findAux___main___rarg), 3, 0);
return x_2;
}
}
obj* l_HashmapImp_findAux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashmapImp_findAux___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashmapImp_findAux___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashmapImp_findAux___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_HashmapImp_findAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashmapImp_findAux___rarg), 3, 0);
return x_2;
}
}
obj* l_HashmapImp_findAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashmapImp_findAux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_HashmapImp_containsAux___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_HashmapImp_findAux___main___rarg(x_0, x_1, x_2);
x_4 = l_Option_isSome___main___rarg(x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_HashmapImp_containsAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashmapImp_containsAux___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_HashmapImp_containsAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_HashmapImp_containsAux___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_HashmapImp_containsAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashmapImp_containsAux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashmapImp_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_8; obj* x_10; usize x_11; usize x_12; obj* x_14; obj* x_16; 
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::dec(x_2);
lean::inc(x_4);
x_8 = lean::array_sz(x_4);
lean::inc(x_3);
x_10 = lean::apply_1(x_1, x_3);
x_11 = lean::unbox_size_t(x_10);
x_12 = lean::usize_modn(x_11, x_8);
lean::dec(x_8);
x_14 = lean::array_idx(x_4, x_12);
lean::dec(x_4);
x_16 = l_HashmapImp_findAux___main___rarg(x_0, x_3, x_14);
return x_16;
}
}
obj* l_HashmapImp_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashmapImp_find___rarg), 4, 0);
return x_2;
}
}
obj* l_HashmapImp_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashmapImp_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashmapImp_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::mk_nat_obj(0ul);
lean::inc(x_3);
x_8 = l_Array_iterateAux___main___at_HashmapImp_foldBuckets___spec__2___rarg(x_3, x_2, x_3, x_6, x_1);
lean::dec(x_3);
return x_8;
}
}
obj* l_HashmapImp_fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashmapImp_fold___rarg), 3, 0);
return x_3;
}
}
obj* l_HashmapImp_fold___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashmapImp_fold(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_HashmapImp_replaceAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_16; uint8 x_17; 
x_7 = lean::cnstr_get(x_3, 0);
x_9 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_11 = x_3;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_3);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
lean::inc(x_1);
lean::inc(x_0);
x_16 = lean::apply_2(x_0, x_12, x_1);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; 
x_18 = l_HashmapImp_replaceAux___main___rarg(x_0, x_1, x_2, x_9);
if (lean::is_scalar(x_11)) {
 x_19 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_19 = x_11;
}
lean::cnstr_set(x_19, 0, x_7);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_21 = x_7;
} else {
 lean::dec(x_7);
 x_21 = lean::box(0);
}
if (lean::is_scalar(x_21)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_21;
}
lean::cnstr_set(x_22, 0, x_1);
lean::cnstr_set(x_22, 1, x_2);
if (lean::is_scalar(x_11)) {
 x_23 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_23 = x_11;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_9);
return x_23;
}
}
}
}
obj* l_HashmapImp_replaceAux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashmapImp_replaceAux___main___rarg), 4, 0);
return x_2;
}
}
obj* l_HashmapImp_replaceAux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashmapImp_replaceAux___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashmapImp_replaceAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashmapImp_replaceAux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_HashmapImp_replaceAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashmapImp_replaceAux___rarg), 4, 0);
return x_2;
}
}
obj* l_HashmapImp_replaceAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashmapImp_replaceAux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashmapImp_eraseAux___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_14; uint8 x_15; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_9 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::inc(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_10, x_1);
x_15 = lean::unbox(x_14);
if (x_15 == 0)
{
obj* x_16; obj* x_17; 
x_16 = l_HashmapImp_eraseAux___main___rarg(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_9;
}
lean::cnstr_set(x_17, 0, x_5);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
else
{
lean::dec(x_9);
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
return x_7;
}
}
}
}
obj* l_HashmapImp_eraseAux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashmapImp_eraseAux___main___rarg), 3, 0);
return x_2;
}
}
obj* l_HashmapImp_eraseAux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashmapImp_eraseAux___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashmapImp_eraseAux___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashmapImp_eraseAux___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_HashmapImp_eraseAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashmapImp_eraseAux___rarg), 3, 0);
return x_2;
}
}
obj* l_HashmapImp_eraseAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashmapImp_eraseAux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashmapImp_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_14; usize x_15; usize x_16; obj* x_17; uint8 x_21; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_9 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
lean::inc(x_7);
x_11 = lean::array_sz(x_7);
lean::inc(x_3);
lean::inc(x_1);
x_14 = lean::apply_1(x_1, x_3);
x_15 = lean::unbox_size_t(x_14);
x_16 = lean::usize_modn(x_15, x_11);
x_17 = lean::array_idx(x_7, x_16);
lean::inc(x_17);
lean::inc(x_3);
lean::inc(x_0);
x_21 = l_HashmapImp_containsAux___rarg(x_0, x_3, x_17);
if (x_21 == 0)
{
obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; uint8 x_31; 
lean::dec(x_0);
x_23 = lean::mk_nat_obj(1ul);
x_24 = lean::nat_add(x_5, x_23);
lean::dec(x_5);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_3);
lean::cnstr_set(x_26, 1, x_4);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_17);
x_28 = lean::array_updt(x_7, x_16, x_27);
lean::dec(x_27);
lean::dec(x_7);
x_31 = lean::nat_dec_le(x_24, x_11);
if (x_31 == 0)
{
obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_40; obj* x_42; 
x_32 = lean::mk_nat_obj(2ul);
x_33 = lean::nat_mul(x_11, x_32);
lean::dec(x_11);
x_35 = lean::box(0);
x_36 = lean::mk_array(x_33, x_35);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_HashmapImp_reinsertAux___rarg), 4, 1);
lean::closure_set(x_37, 0, x_1);
x_38 = lean::mk_nat_obj(0ul);
lean::inc(x_28);
x_40 = l_Array_iterateAux___main___at_HashmapImp_foldBuckets___spec__2___rarg(x_28, x_37, x_28, x_38, x_36);
lean::dec(x_28);
if (lean::is_scalar(x_9)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_9;
}
lean::cnstr_set(x_42, 0, x_24);
lean::cnstr_set(x_42, 1, x_40);
return x_42;
}
else
{
obj* x_45; 
lean::dec(x_11);
lean::dec(x_1);
if (lean::is_scalar(x_9)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_9;
}
lean::cnstr_set(x_45, 0, x_24);
lean::cnstr_set(x_45, 1, x_28);
return x_45;
}
}
else
{
obj* x_48; obj* x_49; obj* x_52; 
lean::dec(x_11);
lean::dec(x_1);
x_48 = l_HashmapImp_replaceAux___main___rarg(x_0, x_3, x_4, x_17);
x_49 = lean::array_updt(x_7, x_16, x_48);
lean::dec(x_48);
lean::dec(x_7);
if (lean::is_scalar(x_9)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_9;
}
lean::cnstr_set(x_52, 0, x_5);
lean::cnstr_set(x_52, 1, x_49);
return x_52;
}
}
}
obj* l_HashmapImp_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashmapImp_insert___rarg), 5, 0);
return x_2;
}
}
obj* l_HashmapImp_insert___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashmapImp_insert(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashmapImp_erase___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; usize x_12; usize x_13; obj* x_15; uint8 x_19; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::inc(x_6);
x_9 = lean::array_sz(x_6);
lean::inc(x_3);
x_11 = lean::apply_1(x_1, x_3);
x_12 = lean::unbox_size_t(x_11);
x_13 = lean::usize_modn(x_12, x_9);
lean::dec(x_9);
x_15 = lean::array_idx(x_6, x_13);
lean::inc(x_15);
lean::inc(x_3);
lean::inc(x_0);
x_19 = l_HashmapImp_containsAux___rarg(x_0, x_3, x_15);
if (x_19 == 0)
{
lean::dec(x_6);
lean::dec(x_15);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_33; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_25 = x_2;
} else {
 lean::dec(x_2);
 x_25 = lean::box(0);
}
x_26 = lean::mk_nat_obj(1ul);
x_27 = lean::nat_sub(x_4, x_26);
lean::dec(x_4);
x_29 = l_HashmapImp_eraseAux___main___rarg(x_0, x_3, x_15);
x_30 = lean::array_updt(x_6, x_13, x_29);
lean::dec(x_29);
lean::dec(x_6);
if (lean::is_scalar(x_25)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_25;
}
lean::cnstr_set(x_33, 0, x_27);
lean::cnstr_set(x_33, 1, x_30);
return x_33;
}
}
}
obj* l_HashmapImp_erase(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashmapImp_erase___rarg), 4, 0);
return x_2;
}
}
obj* l_HashmapImp_erase___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashmapImp_erase(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_mkDHashmap___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mkHashmapImp___rarg(x_0);
return x_1;
}
}
obj* l_mkDHashmap(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_mkDHashmap___rarg), 1, 0);
return x_4;
}
}
obj* l_mkDHashmap___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_mkDHashmap(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_DHashmap_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashmapImp_insert___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_DHashmap_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DHashmap_insert___rarg), 5, 0);
return x_2;
}
}
obj* l_DHashmap_insert___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_DHashmap_insert(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_DHashmap_erase___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashmapImp_erase___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_DHashmap_erase(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DHashmap_erase___rarg), 4, 0);
return x_2;
}
}
obj* l_DHashmap_erase___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_DHashmap_erase(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_DHashmap_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashmapImp_find___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_DHashmap_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DHashmap_find___rarg), 4, 0);
return x_2;
}
}
obj* l_DHashmap_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_DHashmap_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_DHashmap_contains___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = l_HashmapImp_find___rarg(x_0, x_1, x_2, x_3);
x_5 = l_Option_isSome___main___rarg(x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_DHashmap_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DHashmap_contains___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_DHashmap_contains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_DHashmap_contains___rarg(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_DHashmap_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_DHashmap_contains(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_DHashmap_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashmapImp_fold___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_DHashmap_fold(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_DHashmap_fold___rarg), 3, 0);
return x_5;
}
}
obj* l_DHashmap_fold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_DHashmap_fold(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_DHashmap_size___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_DHashmap_size(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DHashmap_size___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_DHashmap_size___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_DHashmap_size___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_DHashmap_size___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_DHashmap_size(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
uint8 l_DHashmap_empty___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = l_DHashmap_size___rarg(x_0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_DHashmap_empty(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_DHashmap_empty___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_DHashmap_empty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_DHashmap_empty___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_DHashmap_empty___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_DHashmap_empty(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_mkHashmap___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mkHashmapImp___rarg(x_0);
return x_1;
}
}
obj* l_mkHashmap(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_mkHashmap___rarg), 1, 0);
return x_4;
}
}
obj* l_mkHashmap___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_mkHashmap(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Hashmap_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashmapImp_insert___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Hashmap_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Hashmap_insert___rarg), 5, 0);
return x_2;
}
}
obj* l_Hashmap_insert___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Hashmap_insert(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Hashmap_erase___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashmapImp_erase___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Hashmap_erase(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Hashmap_erase___rarg), 4, 0);
return x_2;
}
}
obj* l_Hashmap_erase___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Hashmap_erase(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Hashmap_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashmapImp_find___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Hashmap_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Hashmap_find___rarg), 4, 0);
return x_2;
}
}
obj* l_Hashmap_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Hashmap_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Hashmap_contains___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = l_HashmapImp_find___rarg(x_0, x_1, x_2, x_3);
x_5 = l_Option_isSome___main___rarg(x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Hashmap_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Hashmap_contains___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Hashmap_contains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Hashmap_contains___rarg(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Hashmap_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Hashmap_contains(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Hashmap_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashmapImp_fold___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Hashmap_fold(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Hashmap_fold___rarg), 3, 0);
return x_5;
}
}
obj* l_Hashmap_fold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Hashmap_fold(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_Hashmap_size___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_DHashmap_size___rarg(x_0);
return x_1;
}
}
obj* l_Hashmap_size(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Hashmap_size___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_Hashmap_size___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Hashmap_size___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Hashmap_size___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Hashmap_size(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
uint8 l_Hashmap_empty___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = l_DHashmap_size___rarg(x_0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Hashmap_empty(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Hashmap_empty___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_Hashmap_empty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Hashmap_empty___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Hashmap_empty___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Hashmap_empty(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* initialize_init_data_array_basic(obj*);
obj* initialize_init_data_list_basic(obj*);
obj* initialize_init_data_option_basic(obj*);
obj* initialize_init_data_hashable(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_hashmap_basic(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_array_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_list_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_hashable(w);
 l_mkHashmapImp___rarg___closed__1 = _init_l_mkHashmapImp___rarg___closed__1();
lean::mark_persistent(l_mkHashmapImp___rarg___closed__1);
return w;
}
