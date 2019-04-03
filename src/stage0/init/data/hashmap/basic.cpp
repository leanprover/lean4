// Lean compiler output
// Module: init.data.hashmap.basic
// Imports: init.data.array.basic init.data.assoclist init.data.option.basic init.data.hashable
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
obj* l_HashMap_size(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_fold___rarg(obj*, obj*, obj*);
uint8 l_HashMap_contains___rarg(obj*, obj*, obj*, obj*);
obj* l_HashMap_size___rarg___boxed(obj*);
obj* l_HashMapImp_fold(obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_HashMap_find___rarg(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_find___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_mkHashMap(obj*, obj*, obj*, obj*);
obj* l_HashMap_contains___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMap_find___boxed(obj*, obj*);
obj* l_HashMapImp_erase___boxed(obj*, obj*);
obj* l_HashMapImp_foldBuckets(obj*, obj*, obj*);
usize l_HashMapImp_mkIdx(obj*, obj*, usize);
uint8 l_HashMapImp_contains___rarg(obj*, obj*, obj*, obj*);
obj* l_HashMap_Inhabited___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMap_HasEmptyc___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMap_size___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMap_erase___rarg(obj*, obj*, obj*, obj*);
obj* l_HashMap_insert___boxed(obj*, obj*);
obj* l_HashMapBucket_update___rarg(obj*, usize, obj*, obj*);
obj* l_HashMapImp_contains___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_contains___boxed(obj*, obj*);
obj* l_HashMap_size___rarg(obj*);
obj* l_HashMap_empty___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMap_insert___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_AssocList_erase___main___rarg(obj*, obj*, obj*);
obj* l_HashMap_empty___rarg___boxed(obj*);
obj* l_HashMap_contains(obj*, obj*);
obj* l_mkHashMapImp(obj*, obj*);
obj* l_AssocList_find___main___rarg(obj*, obj*, obj*);
obj* l_HashMapImp_reinsertAux___rarg(obj*, obj*, obj*, obj*);
obj* l_HashMap_fold(obj*, obj*, obj*, obj*, obj*);
obj* l_HashMapImp_erase(obj*, obj*);
uint8 l_AssocList_contains___main___rarg(obj*, obj*, obj*);
obj* l_HashMap_insert(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_HashMapBucket_update___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_foldBuckets___boxed(obj*, obj*, obj*);
obj* l_HashMapImp_erase___rarg(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_reinsertAux___boxed(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_HashMapImp_find___rarg(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_insert___rarg(obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_HashMap_find(obj*, obj*);
obj* l_Array_mkArray___rarg(obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_mkHashMapImp___boxed(obj*, obj*);
obj* l_mkHashMap___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMapBucket_update___boxed(obj*, obj*);
obj* l_AssocList_replace___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__1(obj*, obj*, obj*);
obj* l_HashMapImp_find___boxed(obj*, obj*);
obj* l_mkHashMapImp___rarg___closed__1;
obj* l_HashMapImp_reinsertAux(obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__1___boxed(obj*, obj*, obj*);
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_mkHashMap___rarg(obj*);
obj* l_HashMapImp_foldBuckets___rarg(obj*, obj*, obj*);
obj* l_HashMap_empty(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_contains(obj*, obj*);
obj* l_HashMapBucket_update(obj*, obj*);
obj* l_mkHashMapImp___rarg(obj*);
obj* l_HashMapImp_insert(obj*, obj*);
obj* l_HashMap_erase(obj*, obj*);
obj* l_HashMap_fold___rarg(obj*, obj*, obj*);
obj* l_HashMapImp_fold___boxed(obj*, obj*, obj*);
obj* l_HashMap_erase___boxed(obj*, obj*);
obj* l_HashMap_Inhabited(obj*, obj*, obj*, obj*);
obj* l_HashMap_contains___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_HashMapImp_mkIdx___boxed(obj*, obj*, obj*);
obj* l_HashMapImp_find(obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_HashMap_find___rarg___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
uint8 l_HashMap_empty___rarg(obj*);
obj* l_HashMap_fold___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_HashMapImp_insert___boxed(obj*, obj*);
obj* l_HashMap_HasEmptyc(obj*, obj*, obj*, obj*);
obj* l_AssocList_foldl___main___rarg(obj*, obj*, obj*);
obj* l_HashMapBucket_update___rarg(obj* x_0, usize x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::array_updt(x_0, x_1, x_2);
return x_4;
}
}
obj* l_HashMapBucket_update(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapBucket_update___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_HashMapBucket_update___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; obj* x_5; 
x_4 = lean::unbox_size_t(x_1);
x_5 = l_HashMapBucket_update___rarg(x_0, x_4, x_2, x_3);
lean::dec(x_3);
return x_5;
}
}
obj* l_HashMapBucket_update___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMapBucket_update(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_mkHashMapImp___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(8ul);
x_2 = l_Array_mkArray___rarg(x_1, x_0);
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_mkHashMapImp___rarg(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = lean::nat_dec_eq(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::box(0);
x_4 = l_Array_mkArray___rarg(x_0, x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
else
{
obj* x_7; 
lean::dec(x_0);
x_7 = l_mkHashMapImp___rarg___closed__1;
return x_7;
}
}
}
obj* l_mkHashMapImp(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_mkHashMapImp___rarg), 1, 0);
return x_2;
}
}
obj* l_mkHashMapImp___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashMapImp(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
usize l_HashMapImp_mkIdx(obj* x_0, obj* x_1, usize x_2) {
_start:
{
usize x_3; 
x_3 = lean::usize_modn(x_2, x_0);
return x_3;
}
}
obj* l_HashMapImp_mkIdx___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_2);
x_4 = l_HashMapImp_mkIdx(x_0, x_1, x_3);
x_5 = lean::box_size_t(x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_HashMapImp_reinsertAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; usize x_7; usize x_8; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::array_get_size(x_1);
lean::inc(x_2);
x_6 = lean::apply_1(x_0, x_2);
x_7 = lean::unbox_size_t(x_6);
x_8 = lean::usize_modn(x_7, x_4);
lean::dec(x_4);
x_10 = lean::array_idx(x_1, x_8);
x_11 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_3);
lean::cnstr_set(x_11, 2, x_10);
x_12 = lean::array_updt(x_1, x_8, x_11);
return x_12;
}
}
obj* l_HashMapImp_reinsertAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_reinsertAux___rarg), 4, 0);
return x_2;
}
}
obj* l_HashMapImp_reinsertAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMapImp_reinsertAux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
x_12 = lean::array_index(x_2, x_3);
lean::inc(x_1);
x_14 = l_AssocList_foldl___main___rarg(x_1, x_4, x_12);
x_15 = lean::mk_nat_obj(1ul);
x_16 = lean::nat_add(x_3, x_15);
lean::dec(x_3);
x_3 = x_16;
x_4 = x_14;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_HashMapImp_foldBuckets___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = lean::mk_nat_obj(0ul);
lean::inc(x_0);
x_5 = l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__1___rarg(x_0, x_2, x_0, x_3, x_1);
lean::dec(x_0);
return x_5;
}
}
obj* l_HashMapImp_foldBuckets(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_foldBuckets___rarg), 3, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_HashMapImp_foldBuckets___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashMapImp_foldBuckets(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_HashMapImp_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; usize x_8; usize x_9; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::array_get_size(x_4);
lean::inc(x_3);
x_7 = lean::apply_1(x_1, x_3);
x_8 = lean::unbox_size_t(x_7);
x_9 = lean::usize_modn(x_8, x_5);
lean::dec(x_5);
x_11 = lean::array_idx(x_4, x_9);
x_12 = l_AssocList_find___main___rarg(x_0, x_3, x_11);
return x_12;
}
}
obj* l_HashMapImp_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_find___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_HashMapImp_find___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashMapImp_find___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_HashMapImp_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMapImp_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_HashMapImp_contains___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; usize x_8; usize x_9; obj* x_11; uint8 x_12; 
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::array_get_size(x_4);
lean::inc(x_3);
x_7 = lean::apply_1(x_1, x_3);
x_8 = lean::unbox_size_t(x_7);
x_9 = lean::usize_modn(x_8, x_5);
lean::dec(x_5);
x_11 = lean::array_idx(x_4, x_9);
x_12 = l_AssocList_contains___main___rarg(x_0, x_3, x_11);
return x_12;
}
}
obj* l_HashMapImp_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_contains___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_HashMapImp_contains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_HashMapImp_contains___rarg(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_HashMapImp_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMapImp_contains(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashMapImp_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::mk_nat_obj(0ul);
lean::inc(x_3);
x_8 = l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__1___rarg(x_3, x_2, x_3, x_6, x_1);
lean::dec(x_3);
return x_8;
}
}
obj* l_HashMapImp_fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_fold___rarg), 3, 0);
return x_3;
}
}
obj* l_HashMapImp_fold___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashMapImp_fold(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_HashMapImp_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_13; usize x_14; usize x_15; obj* x_16; uint8 x_20; 
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
x_10 = lean::array_get_size(x_7);
lean::inc(x_3);
lean::inc(x_1);
x_13 = lean::apply_1(x_1, x_3);
x_14 = lean::unbox_size_t(x_13);
x_15 = lean::usize_modn(x_14, x_10);
x_16 = lean::array_idx(x_7, x_15);
lean::inc(x_16);
lean::inc(x_3);
lean::inc(x_0);
x_20 = l_AssocList_contains___main___rarg(x_0, x_3, x_16);
if (x_20 == 0)
{
obj* x_22; obj* x_23; obj* x_25; obj* x_26; uint8 x_27; 
lean::dec(x_0);
x_22 = lean::mk_nat_obj(1ul);
x_23 = lean::nat_add(x_5, x_22);
lean::dec(x_5);
x_25 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_25, 0, x_3);
lean::cnstr_set(x_25, 1, x_4);
lean::cnstr_set(x_25, 2, x_16);
x_26 = lean::array_updt(x_7, x_15, x_25);
x_27 = lean::nat_dec_le(x_23, x_10);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_38; 
x_28 = lean::mk_nat_obj(2ul);
x_29 = lean::nat_mul(x_10, x_28);
lean::dec(x_10);
x_31 = lean::box(0);
x_32 = l_Array_mkArray___rarg(x_29, x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_reinsertAux___rarg), 4, 1);
lean::closure_set(x_33, 0, x_1);
x_34 = lean::mk_nat_obj(0ul);
lean::inc(x_26);
x_36 = l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__1___rarg(x_26, x_33, x_26, x_34, x_32);
lean::dec(x_26);
if (lean::is_scalar(x_9)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_9;
}
lean::cnstr_set(x_38, 0, x_23);
lean::cnstr_set(x_38, 1, x_36);
return x_38;
}
else
{
obj* x_41; 
lean::dec(x_10);
lean::dec(x_1);
if (lean::is_scalar(x_9)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_9;
}
lean::cnstr_set(x_41, 0, x_23);
lean::cnstr_set(x_41, 1, x_26);
return x_41;
}
}
else
{
obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_10);
lean::dec(x_1);
x_44 = l_AssocList_replace___main___rarg(x_0, x_3, x_4, x_16);
x_45 = lean::array_updt(x_7, x_15, x_44);
if (lean::is_scalar(x_9)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_9;
}
lean::cnstr_set(x_46, 0, x_5);
lean::cnstr_set(x_46, 1, x_45);
return x_46;
}
}
}
obj* l_HashMapImp_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_insert___rarg), 5, 0);
return x_2;
}
}
obj* l_HashMapImp_insert___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMapImp_insert(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashMapImp_erase___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; usize x_11; usize x_12; obj* x_14; uint8 x_18; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
x_8 = lean::array_get_size(x_6);
lean::inc(x_3);
x_10 = lean::apply_1(x_1, x_3);
x_11 = lean::unbox_size_t(x_10);
x_12 = lean::usize_modn(x_11, x_8);
lean::dec(x_8);
x_14 = lean::array_idx(x_6, x_12);
lean::inc(x_14);
lean::inc(x_3);
lean::inc(x_0);
x_18 = l_AssocList_contains___main___rarg(x_0, x_3, x_14);
if (x_18 == 0)
{
lean::dec(x_6);
lean::dec(x_14);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_24 = x_2;
} else {
 lean::dec(x_2);
 x_24 = lean::box(0);
}
x_25 = lean::mk_nat_obj(1ul);
x_26 = lean::nat_sub(x_4, x_25);
lean::dec(x_4);
x_28 = l_AssocList_erase___main___rarg(x_0, x_3, x_14);
x_29 = lean::array_updt(x_6, x_12, x_28);
if (lean::is_scalar(x_24)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_24;
}
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
}
obj* l_HashMapImp_erase(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_erase___rarg), 4, 0);
return x_2;
}
}
obj* l_HashMapImp_erase___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMapImp_erase(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_mkHashMap___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mkHashMapImp___rarg(x_0);
return x_1;
}
}
obj* l_mkHashMap(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_mkHashMap___rarg), 1, 0);
return x_4;
}
}
obj* l_mkHashMap___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_mkHashMap(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_HashMap_Inhabited(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(8ul);
x_5 = l_mkHashMapImp___rarg(x_4);
return x_5;
}
}
obj* l_HashMap_Inhabited___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashMap_Inhabited(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_HashMap_HasEmptyc(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(8ul);
x_5 = l_mkHashMapImp___rarg(x_4);
return x_5;
}
}
obj* l_HashMap_HasEmptyc___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashMap_HasEmptyc(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_HashMap_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMapImp_insert___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_HashMap_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_insert___rarg), 5, 0);
return x_2;
}
}
obj* l_HashMap_insert___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMap_insert(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashMap_erase___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashMapImp_erase___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_HashMap_erase(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_erase___rarg), 4, 0);
return x_2;
}
}
obj* l_HashMap_erase___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMap_erase(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashMap_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashMapImp_find___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_HashMap_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_find___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_HashMap_find___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashMap_find___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_HashMap_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMap_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_HashMap_contains___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_HashMapImp_contains___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_HashMap_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_contains___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_HashMap_contains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_HashMap_contains___rarg(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_HashMap_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMap_contains(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashMap_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_HashMapImp_fold___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_HashMap_fold(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_fold___rarg), 3, 0);
return x_5;
}
}
obj* l_HashMap_fold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMap_fold(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_HashMap_size___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_HashMap_size(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_size___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_HashMap_size___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_HashMap_size___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_HashMap_size___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashMap_size(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
uint8 l_HashMap_empty___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::nat_dec_eq(x_1, x_2);
return x_3;
}
}
obj* l_HashMap_empty(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_empty___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_HashMap_empty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_HashMap_empty___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_HashMap_empty___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashMap_empty(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* initialize_init_data_array_basic(obj*);
obj* initialize_init_data_assoclist(obj*);
obj* initialize_init_data_option_basic(obj*);
obj* initialize_init_data_hashable(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_hashmap_basic(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_array_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_assoclist(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_hashable(w);
 l_mkHashMapImp___rarg___closed__1 = _init_l_mkHashMapImp___rarg___closed__1();
lean::mark_persistent(l_mkHashMapImp___rarg___closed__1);
return w;
}
