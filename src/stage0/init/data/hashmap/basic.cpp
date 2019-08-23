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
extern "C" {
obj* l_Array_miterateAux___main___at_HashMapImp_mfoldBuckets___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_HashMap_size(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMapImp_mfold___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMapImp_fold___spec__2(obj*, obj*, obj*);
obj* l_HashMapImp_fold___rarg(obj*, obj*, obj*);
obj* l_HashMapImp_mfoldBuckets(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMapImp_fold___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_HashMap_mfold___rarg(obj*, obj*, obj*, obj*);
uint8 l_HashMap_contains___rarg(obj*, obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___at_HashMapImp_moveEntries___main___spec__1___rarg(obj*, obj*, obj*);
obj* l_HashMap_size___rarg___boxed(obj*);
obj* l_HashMapImp_fold(obj*, obj*, obj*);
obj* lean_nat_sub(obj*, obj*);
obj* l_HashMap_find___rarg(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_find___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_expand(obj*, obj*);
obj* l_AssocList_mfoldl___main___at_HashMapImp_fold___spec__1___rarg(obj*, obj*, obj*);
obj* l_mkHashMap(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMapImp_mfoldBuckets___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_HashMapImp_mfold___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___at_HashMap_fold___spec__1(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMap_fold___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_mkHashMapImp___rarg___closed__2;
obj* l_HashMap_contains___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_HashMap_numBuckets___rarg___boxed(obj*);
obj* l_Array_miterateAux___main___at_HashMapImp_mfold___spec__1(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_foldBuckets(obj*, obj*, obj*);
usize l_HashMapImp_mkIdx(obj*, obj*, usize);
obj* l_Array_miterateAux___main___at_HashMapImp_mfoldBuckets___spec__1___boxed(obj*, obj*, obj*, obj*);
uint8 l_HashMapImp_contains___rarg(obj*, obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___at_HashMapImp_foldBuckets___spec__1___rarg(obj*, obj*, obj*);
obj* l_HashMap_Inhabited___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMap_HasEmptyc___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_uget(obj*, obj*, usize, obj*);
obj* l_HashMapImp_mfoldBuckets___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMap_size___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_uset(obj*, obj*, usize, obj*, obj*);
obj* l_HashMap_erase___rarg(obj*, obj*, obj*, obj*);
obj* l_HashMapBucket_update___rarg(obj*, usize, obj*, obj*);
obj* l_HashMap_numBuckets___rarg(obj*);
obj* l_HashMapImp_contains___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_mfold(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_HashMap_size___rarg(obj*);
obj* l_HashMap_empty___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMap_insert___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_AssocList_erase___main___rarg(obj*, obj*, obj*);
obj* l_HashMapImp_moveEntries___rarg(obj*, obj*, obj*, obj*);
obj* l_HashMap_empty___rarg___boxed(obj*);
obj* l_HashMap_contains(obj*, obj*);
obj* l_HashMapImp_moveEntries___main(obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___rarg(obj*, obj*, obj*, obj*);
obj* l_mkHashMapImp(obj*, obj*);
obj* l_HashMapImp_foldBuckets___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMap_mfold___spec__1(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMapImp_fold___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_AssocList_find___main___rarg(obj*, obj*, obj*);
obj* l_HashMapImp_reinsertAux___rarg(obj*, obj*, obj*, obj*);
obj* l_HashMap_fold(obj*, obj*, obj*, obj*, obj*);
obj* l_HashMapImp_erase(obj*, obj*);
uint8 l_AssocList_contains___main___rarg(obj*, obj*, obj*);
obj* l_HashMap_insert(obj*, obj*);
uint8 lean_nat_dec_lt(obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMap_fold___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___at_HashMapImp_fold___spec__1(obj*, obj*, obj*);
obj* l_HashMapBucket_update___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMap_mfold___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_fget(obj*, obj*, obj*);
obj* l_HashMapImp_erase___rarg(obj*, obj*, obj*, obj*);
obj* lean_nat_add(obj*, obj*);
obj* l_HashMapImp_find___rarg(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_insert___rarg(obj*, obj*, obj*, obj*, obj*);
uint8 lean_nat_dec_eq(obj*, obj*);
obj* l_HashMap_find(obj*, obj*);
obj* l_HashMap_numBuckets___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__2(obj*, obj*, obj*);
obj* l_mkHashMap___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMap_mfold___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_AssocList_replace___main___rarg(obj*, obj*, obj*, obj*);
obj* l_mkHashMapImp___rarg___closed__1;
obj* l_Array_miterateAux___main___at_HashMapImp_mfold___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_HashMapImp_reinsertAux(obj*, obj*);
obj* l_HashMapImp_moveEntries___main___rarg(obj*, obj*, obj*, obj*);
obj* l_HashMap_mfold(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMap_mfold___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_HashMap_numBuckets(obj*, obj*, obj*, obj*);
usize lean_usize_modn(usize, obj*);
obj* l_Array_miterateAux___main___at_HashMap_fold___spec__2(obj*, obj*, obj*);
obj* l_HashMap_mfold___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_mkHashMap___rarg(obj*);
obj* l_HashMapImp_foldBuckets___rarg(obj*, obj*, obj*);
obj* l_HashMapImp_moveEntries(obj*, obj*);
obj* l_HashMap_empty(obj*, obj*, obj*, obj*);
obj* l_HashMap_Inhabited___closed__1;
obj* l_Array_size(obj*, obj*);
obj* l_HashMapImp_contains(obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMapImp_mfold___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_HashMapImp_mfoldBuckets___spec__1(obj*, obj*, obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_fold___rarg___boxed(obj*, obj*, obj*);
obj* l_HashMapBucket_update(obj*, obj*);
obj* l_mkHashMapImp___rarg(obj*);
obj* l_HashMapImp_insert(obj*, obj*);
obj* l_HashMap_erase(obj*, obj*);
obj* l_HashMap_fold___rarg(obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___at_HashMap_fold___spec__1___rarg(obj*, obj*, obj*);
obj* l_HashMap_Inhabited(obj*, obj*, obj*, obj*);
obj* l_AssocList_mfoldl___main___at_HashMapImp_foldBuckets___spec__1(obj*, obj*, obj*);
uint8 lean_nat_dec_le(obj*, obj*);
obj* l_AssocList_mfoldl___main___at_HashMapImp_moveEntries___main___spec__1(obj*, obj*);
obj* l_HashMapImp_mkIdx___boxed(obj*, obj*, obj*);
obj* l_HashMapImp_find(obj*, obj*);
obj* l_HashMap_find___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_HashMap_fold___rarg___boxed(obj*, obj*, obj*);
obj* lean_nat_mul(obj*, obj*);
uint8 l_HashMap_empty___rarg(obj*);
obj* l_HashMap_fold___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_HashMapImp_mfoldBuckets___rarg(obj*, obj*, obj*, obj*);
obj* l_HashMap_HasEmptyc(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_expand___rarg(obj*, obj*, obj*);
obj* l_HashMapBucket_update___rarg(obj* x_1, usize x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean_array_uset(x_1, x_2, x_3);
return x_5;
}
}
obj* l_HashMapBucket_update(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapBucket_update___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_HashMapBucket_update___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; obj* x_6; 
x_5 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_6 = l_HashMapBucket_update___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* _init_l_mkHashMapImp___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(8u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
obj* _init_l_mkHashMapImp___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(0u);
x_2 = l_mkHashMapImp___rarg___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_mkHashMapImp___rarg(obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::box(0);
x_5 = lean_mk_array(x_1, x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
else
{
obj* x_7; 
lean::dec(x_1);
x_7 = l_mkHashMapImp___rarg___closed__2;
return x_7;
}
}
}
obj* l_mkHashMapImp(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_mkHashMapImp___rarg), 1, 0);
return x_3;
}
}
usize l_HashMapImp_mkIdx(obj* x_1, obj* x_2, usize x_3) {
_start:
{
usize x_4; 
x_4 = lean_usize_modn(x_3, x_1);
return x_4;
}
}
obj* l_HashMapImp_mkIdx___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; usize x_5; obj* x_6; 
x_4 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_5 = l_HashMapImp_mkIdx(x_1, x_2, x_4);
lean::dec(x_1);
x_6 = lean::box_size_t(x_5);
return x_6;
}
}
obj* l_HashMapImp_reinsertAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; usize x_7; usize x_8; obj* x_9; usize x_10; obj* x_11; obj* x_12; usize x_13; obj* x_14; 
x_5 = lean_array_get_size(x_2);
lean::inc(x_3);
x_6 = lean::apply_1(x_1, x_3);
x_7 = lean::unbox_size_t(x_6);
lean::dec(x_6);
x_8 = lean_usize_modn(x_7, x_5);
lean::dec(x_5);
x_9 = lean::box_size_t(x_8);
x_10 = lean::unbox_size_t(x_9);
x_11 = lean_array_uget(x_2, x_10);
x_12 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_12, 0, x_3);
lean::cnstr_set(x_12, 1, x_4);
lean::cnstr_set(x_12, 2, x_11);
x_13 = lean::unbox_size_t(x_9);
lean::dec(x_9);
x_14 = lean_array_uset(x_2, x_13, x_12);
return x_14;
}
}
obj* l_HashMapImp_reinsertAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_reinsertAux___rarg), 4, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_mfoldBuckets___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
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
x_13 = lean_array_fget(x_4, x_5);
lean::inc(x_3);
lean::inc(x_1);
x_14 = l_AssocList_mfoldl___main___rarg(x_1, x_3, x_6, x_13);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean_nat_add(x_5, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_HashMapImp_mfoldBuckets___spec__1___rarg___boxed), 6, 5);
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
obj* l_Array_miterateAux___main___at_HashMapImp_mfoldBuckets___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_HashMapImp_mfoldBuckets___spec__1___rarg___boxed), 6, 0);
return x_5;
}
}
obj* l_HashMapImp_mfoldBuckets___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_6 = l_Array_miterateAux___main___at_HashMapImp_mfoldBuckets___spec__1___rarg(x_1, x_2, x_4, x_2, x_5, x_3);
return x_6;
}
}
obj* l_HashMapImp_mfoldBuckets(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_mfoldBuckets___rarg), 4, 0);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_mfoldBuckets___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_HashMapImp_mfoldBuckets___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_mfoldBuckets___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_HashMapImp_mfoldBuckets___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_HashMapImp_mfoldBuckets___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMapImp_mfoldBuckets(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_AssocList_mfoldl___main___at_HashMapImp_foldBuckets___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
lean::dec(x_3);
lean::inc(x_1);
x_7 = lean::apply_3(x_1, x_2, x_4, x_5);
x_2 = x_7;
x_3 = x_6;
goto _start;
}
}
}
obj* l_AssocList_mfoldl___main___at_HashMapImp_foldBuckets___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_mfoldl___main___at_HashMapImp_foldBuckets___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
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
x_8 = lean_array_fget(x_3, x_4);
lean::inc(x_2);
x_9 = l_AssocList_mfoldl___main___at_HashMapImp_foldBuckets___spec__1___rarg(x_2, x_5, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__2___rarg___boxed), 5, 0);
return x_4;
}
}
obj* l_HashMapImp_foldBuckets___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__2___rarg(x_1, x_3, x_1, x_4, x_2);
return x_5;
}
}
obj* l_HashMapImp_foldBuckets(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_foldBuckets___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_HashMapImp_foldBuckets___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l_HashMapImp_foldBuckets___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashMapImp_foldBuckets___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_mfold___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
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
x_13 = lean_array_fget(x_4, x_5);
lean::inc(x_2);
lean::inc(x_1);
x_14 = l_AssocList_mfoldl___main___rarg(x_1, x_2, x_6, x_13);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean_nat_add(x_5, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_HashMapImp_mfold___spec__1___rarg___boxed), 6, 5);
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
obj* l_Array_miterateAux___main___at_HashMapImp_mfold___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_HashMapImp_mfold___spec__1___rarg___boxed), 6, 0);
return x_5;
}
}
obj* l_HashMapImp_mfold___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_miterateAux___main___at_HashMapImp_mfold___spec__1___rarg(x_1, x_2, x_4, x_5, x_6, x_3);
return x_7;
}
}
obj* l_HashMapImp_mfold(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_mfold___rarg), 4, 0);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_mfold___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_HashMapImp_mfold___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_mfold___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_HashMapImp_mfold___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_HashMapImp_mfold___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMapImp_mfold(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_AssocList_mfoldl___main___at_HashMapImp_fold___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
lean::dec(x_3);
lean::inc(x_1);
x_7 = lean::apply_3(x_1, x_2, x_4, x_5);
x_2 = x_7;
x_3 = x_6;
goto _start;
}
}
}
obj* l_AssocList_mfoldl___main___at_HashMapImp_fold___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_mfoldl___main___at_HashMapImp_fold___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_fold___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
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
x_8 = lean_array_fget(x_3, x_4);
lean::inc(x_1);
x_9 = l_AssocList_mfoldl___main___at_HashMapImp_fold___spec__1___rarg(x_1, x_5, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_fold___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_HashMapImp_fold___spec__2___rarg___boxed), 5, 0);
return x_4;
}
}
obj* l_HashMapImp_fold___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_3, 1);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterateAux___main___at_HashMapImp_fold___spec__2___rarg(x_1, x_3, x_4, x_5, x_2);
return x_6;
}
}
obj* l_HashMapImp_fold(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_fold___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_HashMapImp_fold___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_HashMapImp_fold___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_HashMapImp_fold___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashMapImp_fold___rarg(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_HashMapImp_find___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; usize x_8; usize x_9; obj* x_10; usize x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean_array_get_size(x_5);
lean::inc(x_4);
x_7 = lean::apply_1(x_2, x_4);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean::dec(x_6);
x_10 = lean::box_size_t(x_9);
x_11 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_12 = lean_array_uget(x_5, x_11);
x_13 = l_AssocList_find___main___rarg(x_1, x_4, x_12);
return x_13;
}
}
obj* l_HashMapImp_find(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_find___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_HashMapImp_find___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMapImp_find___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
uint8 l_HashMapImp_contains___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; usize x_8; usize x_9; obj* x_10; usize x_11; obj* x_12; uint8 x_13; 
x_5 = lean::cnstr_get(x_3, 1);
x_6 = lean_array_get_size(x_5);
lean::inc(x_4);
x_7 = lean::apply_1(x_2, x_4);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean::dec(x_6);
x_10 = lean::box_size_t(x_9);
x_11 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_12 = lean_array_uget(x_5, x_11);
x_13 = l_AssocList_contains___main___rarg(x_1, x_4, x_12);
return x_13;
}
}
obj* l_HashMapImp_contains(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_contains___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_HashMapImp_contains___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_HashMapImp_contains___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_AssocList_mfoldl___main___at_HashMapImp_moveEntries___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; usize x_9; usize x_10; obj* x_11; usize x_12; obj* x_13; usize x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean::inc(x_1);
lean::inc(x_5);
x_8 = lean::apply_1(x_1, x_5);
x_9 = lean::unbox_size_t(x_8);
lean::dec(x_8);
x_10 = lean_usize_modn(x_9, x_7);
lean::dec(x_7);
x_11 = lean::box_size_t(x_10);
x_12 = lean::unbox_size_t(x_11);
x_13 = lean_array_uget(x_2, x_12);
lean::cnstr_set(x_3, 2, x_13);
x_14 = lean::unbox_size_t(x_11);
lean::dec(x_11);
x_15 = lean_array_uset(x_2, x_14, x_3);
x_2 = x_15;
x_3 = x_6;
goto _start;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; usize x_22; usize x_23; obj* x_24; usize x_25; obj* x_26; obj* x_27; usize x_28; obj* x_29; 
x_17 = lean::cnstr_get(x_3, 0);
x_18 = lean::cnstr_get(x_3, 1);
x_19 = lean::cnstr_get(x_3, 2);
lean::inc(x_19);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_3);
x_20 = lean_array_get_size(x_2);
lean::inc(x_1);
lean::inc(x_17);
x_21 = lean::apply_1(x_1, x_17);
x_22 = lean::unbox_size_t(x_21);
lean::dec(x_21);
x_23 = lean_usize_modn(x_22, x_20);
lean::dec(x_20);
x_24 = lean::box_size_t(x_23);
x_25 = lean::unbox_size_t(x_24);
x_26 = lean_array_uget(x_2, x_25);
x_27 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_27, 0, x_17);
lean::cnstr_set(x_27, 1, x_18);
lean::cnstr_set(x_27, 2, x_26);
x_28 = lean::unbox_size_t(x_24);
lean::dec(x_24);
x_29 = lean_array_uset(x_2, x_28, x_27);
x_2 = x_29;
x_3 = x_19;
goto _start;
}
}
}
}
obj* l_AssocList_mfoldl___main___at_HashMapImp_moveEntries___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_mfoldl___main___at_HashMapImp_moveEntries___main___spec__1___rarg), 3, 0);
return x_3;
}
}
obj* l_HashMapImp_moveEntries___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean::box(0);
x_9 = lean_array_fset(x_3, x_2, x_8);
lean::inc(x_1);
x_10 = l_AssocList_mfoldl___main___at_HashMapImp_moveEntries___main___spec__1___rarg(x_1, x_4, x_7);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean_nat_add(x_2, x_11);
lean::dec(x_2);
x_2 = x_12;
x_3 = x_9;
x_4 = x_10;
goto _start;
}
}
}
obj* l_HashMapImp_moveEntries___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_moveEntries___main___rarg), 4, 0);
return x_3;
}
}
obj* l_HashMapImp_moveEntries___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMapImp_moveEntries___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_HashMapImp_moveEntries(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_moveEntries___rarg), 4, 0);
return x_3;
}
}
obj* l_HashMapImp_expand___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean_array_get_size(x_3);
x_5 = lean::mk_nat_obj(2u);
x_6 = lean_nat_mul(x_4, x_5);
lean::dec(x_4);
x_7 = lean::box(0);
x_8 = lean_mk_array(x_6, x_7);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_HashMapImp_moveEntries___main___rarg(x_1, x_9, x_3, x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_HashMapImp_expand(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_expand___rarg), 3, 0);
return x_3;
}
}
obj* l_HashMapImp_insert___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; usize x_11; usize x_12; obj* x_13; usize x_14; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
x_9 = lean_array_get_size(x_8);
lean::inc(x_2);
lean::inc(x_4);
x_10 = lean::apply_1(x_2, x_4);
x_11 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_12 = lean_usize_modn(x_11, x_9);
x_13 = lean::box_size_t(x_12);
x_14 = lean::unbox_size_t(x_13);
x_15 = lean_array_uget(x_8, x_14);
lean::inc(x_15);
lean::inc(x_4);
lean::inc(x_1);
x_16 = l_AssocList_contains___main___rarg(x_1, x_4, x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_19; usize x_20; obj* x_21; uint8 x_22; 
lean::dec(x_1);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean_nat_add(x_7, x_17);
lean::dec(x_7);
x_19 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_19, 0, x_4);
lean::cnstr_set(x_19, 1, x_5);
lean::cnstr_set(x_19, 2, x_15);
x_20 = lean::unbox_size_t(x_13);
lean::dec(x_13);
x_21 = lean_array_uset(x_8, x_20, x_19);
x_22 = lean_nat_dec_le(x_18, x_9);
lean::dec(x_9);
if (x_22 == 0)
{
obj* x_23; 
lean::free_heap_obj(x_3);
x_23 = l_HashMapImp_expand___rarg(x_2, x_18, x_21);
return x_23;
}
else
{
lean::dec(x_2);
lean::cnstr_set(x_3, 1, x_21);
lean::cnstr_set(x_3, 0, x_18);
return x_3;
}
}
else
{
obj* x_24; usize x_25; obj* x_26; 
lean::dec(x_9);
lean::dec(x_2);
x_24 = l_AssocList_replace___main___rarg(x_1, x_4, x_5, x_15);
x_25 = lean::unbox_size_t(x_13);
lean::dec(x_13);
x_26 = lean_array_uset(x_8, x_25, x_24);
lean::cnstr_set(x_3, 1, x_26);
return x_3;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; usize x_31; usize x_32; obj* x_33; usize x_34; obj* x_35; uint8 x_36; 
x_27 = lean::cnstr_get(x_3, 0);
x_28 = lean::cnstr_get(x_3, 1);
lean::inc(x_28);
lean::inc(x_27);
lean::dec(x_3);
x_29 = lean_array_get_size(x_28);
lean::inc(x_2);
lean::inc(x_4);
x_30 = lean::apply_1(x_2, x_4);
x_31 = lean::unbox_size_t(x_30);
lean::dec(x_30);
x_32 = lean_usize_modn(x_31, x_29);
x_33 = lean::box_size_t(x_32);
x_34 = lean::unbox_size_t(x_33);
x_35 = lean_array_uget(x_28, x_34);
lean::inc(x_35);
lean::inc(x_4);
lean::inc(x_1);
x_36 = l_AssocList_contains___main___rarg(x_1, x_4, x_35);
if (x_36 == 0)
{
obj* x_37; obj* x_38; obj* x_39; usize x_40; obj* x_41; uint8 x_42; 
lean::dec(x_1);
x_37 = lean::mk_nat_obj(1u);
x_38 = lean_nat_add(x_27, x_37);
lean::dec(x_27);
x_39 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_39, 0, x_4);
lean::cnstr_set(x_39, 1, x_5);
lean::cnstr_set(x_39, 2, x_35);
x_40 = lean::unbox_size_t(x_33);
lean::dec(x_33);
x_41 = lean_array_uset(x_28, x_40, x_39);
x_42 = lean_nat_dec_le(x_38, x_29);
lean::dec(x_29);
if (x_42 == 0)
{
obj* x_43; 
x_43 = l_HashMapImp_expand___rarg(x_2, x_38, x_41);
return x_43;
}
else
{
obj* x_44; 
lean::dec(x_2);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_38);
lean::cnstr_set(x_44, 1, x_41);
return x_44;
}
}
else
{
obj* x_45; usize x_46; obj* x_47; obj* x_48; 
lean::dec(x_29);
lean::dec(x_2);
x_45 = l_AssocList_replace___main___rarg(x_1, x_4, x_5, x_35);
x_46 = lean::unbox_size_t(x_33);
lean::dec(x_33);
x_47 = lean_array_uset(x_28, x_46, x_45);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_27);
lean::cnstr_set(x_48, 1, x_47);
return x_48;
}
}
}
}
obj* l_HashMapImp_insert(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_insert___rarg), 5, 0);
return x_3;
}
}
obj* l_HashMapImp_erase___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; usize x_9; usize x_10; obj* x_11; usize x_12; obj* x_13; uint8 x_14; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_7 = lean_array_get_size(x_6);
lean::inc(x_4);
x_8 = lean::apply_1(x_2, x_4);
x_9 = lean::unbox_size_t(x_8);
lean::dec(x_8);
x_10 = lean_usize_modn(x_9, x_7);
lean::dec(x_7);
x_11 = lean::box_size_t(x_10);
x_12 = lean::unbox_size_t(x_11);
x_13 = lean_array_uget(x_6, x_12);
lean::inc(x_13);
lean::inc(x_4);
lean::inc(x_1);
x_14 = l_AssocList_contains___main___rarg(x_1, x_4, x_13);
if (x_14 == 0)
{
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
return x_3;
}
else
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_3);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; usize x_21; obj* x_22; 
x_16 = lean::cnstr_get(x_3, 1);
lean::dec(x_16);
x_17 = lean::cnstr_get(x_3, 0);
lean::dec(x_17);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean_nat_sub(x_5, x_18);
lean::dec(x_5);
x_20 = l_AssocList_erase___main___rarg(x_1, x_4, x_13);
x_21 = lean::unbox_size_t(x_11);
lean::dec(x_11);
x_22 = lean_array_uset(x_6, x_21, x_20);
lean::cnstr_set(x_3, 1, x_22);
lean::cnstr_set(x_3, 0, x_19);
return x_3;
}
else
{
obj* x_23; obj* x_24; obj* x_25; usize x_26; obj* x_27; obj* x_28; 
lean::dec(x_3);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean_nat_sub(x_5, x_23);
lean::dec(x_5);
x_25 = l_AssocList_erase___main___rarg(x_1, x_4, x_13);
x_26 = lean::unbox_size_t(x_11);
lean::dec(x_11);
x_27 = lean_array_uset(x_6, x_26, x_25);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_24);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
}
}
}
obj* l_HashMapImp_erase(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMapImp_erase___rarg), 4, 0);
return x_3;
}
}
obj* l_mkHashMap___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* l_mkHashMap(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_mkHashMap___rarg), 1, 0);
return x_5;
}
}
obj* l_mkHashMap___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_mkHashMap(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* _init_l_HashMap_Inhabited___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
obj* l_HashMap_Inhabited(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMap_Inhabited___closed__1;
return x_5;
}
}
obj* l_HashMap_Inhabited___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMap_Inhabited(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_HashMap_HasEmptyc(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMap_Inhabited___closed__1;
return x_5;
}
}
obj* l_HashMap_HasEmptyc___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMap_HasEmptyc(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_HashMap_insert___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_HashMapImp_insert___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_HashMap_insert(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_insert___rarg), 5, 0);
return x_3;
}
}
obj* l_HashMap_erase___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMapImp_erase___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_HashMap_erase(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_erase___rarg), 4, 0);
return x_3;
}
}
obj* l_HashMap_find___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMapImp_find___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_HashMap_find(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_find___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_HashMap_find___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMap_find___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
uint8 l_HashMap_contains___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = l_HashMapImp_contains___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_HashMap_contains(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_contains___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_HashMap_contains___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_HashMap_contains___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_HashMap_mfold___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
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
x_13 = lean_array_fget(x_4, x_5);
lean::inc(x_2);
lean::inc(x_1);
x_14 = l_AssocList_mfoldl___main___rarg(x_1, x_2, x_6, x_13);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean_nat_add(x_5, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_HashMap_mfold___spec__1___rarg___boxed), 6, 5);
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
obj* l_Array_miterateAux___main___at_HashMap_mfold___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_HashMap_mfold___spec__1___rarg___boxed), 6, 0);
return x_5;
}
}
obj* l_HashMap_mfold___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = lean::mk_nat_obj(0u);
x_7 = l_Array_miterateAux___main___at_HashMap_mfold___spec__1___rarg(x_1, x_2, x_4, x_5, x_6, x_3);
return x_7;
}
}
obj* l_HashMap_mfold(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_mfold___rarg), 4, 0);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_HashMap_mfold___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_HashMap_mfold___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
return x_7;
}
}
obj* l_Array_miterateAux___main___at_HashMap_mfold___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_HashMap_mfold___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_HashMap_mfold___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_HashMap_mfold(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_3);
return x_7;
}
}
obj* l_AssocList_mfoldl___main___at_HashMap_fold___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
lean::dec(x_3);
lean::inc(x_1);
x_7 = lean::apply_3(x_1, x_2, x_4, x_5);
x_2 = x_7;
x_3 = x_6;
goto _start;
}
}
}
obj* l_AssocList_mfoldl___main___at_HashMap_fold___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_AssocList_mfoldl___main___at_HashMap_fold___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_HashMap_fold___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
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
x_8 = lean_array_fget(x_3, x_4);
lean::inc(x_1);
x_9 = l_AssocList_mfoldl___main___at_HashMap_fold___spec__1___rarg(x_1, x_5, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_HashMap_fold___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_HashMap_fold___spec__2___rarg___boxed), 5, 0);
return x_4;
}
}
obj* l_HashMap_fold___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_3, 1);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterateAux___main___at_HashMap_fold___spec__2___rarg(x_1, x_3, x_4, x_5, x_2);
return x_6;
}
}
obj* l_HashMap_fold(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_fold___rarg___boxed), 3, 0);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_HashMap_fold___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_HashMap_fold___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_HashMap_fold___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_HashMap_fold___rarg(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_HashMap_fold___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_HashMap_fold(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_3);
return x_6;
}
}
obj* l_HashMap_size___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* l_HashMap_size(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_size___rarg___boxed), 1, 0);
return x_5;
}
}
obj* l_HashMap_size___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMap_size___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashMap_size___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMap_size(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
uint8 l_HashMap_empty___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
obj* l_HashMap_empty(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_empty___rarg___boxed), 1, 0);
return x_5;
}
}
obj* l_HashMap_empty___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_HashMap_empty___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_HashMap_empty___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMap_empty(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_HashMap_numBuckets___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
obj* l_HashMap_numBuckets(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_HashMap_numBuckets___rarg___boxed), 1, 0);
return x_5;
}
}
obj* l_HashMap_numBuckets___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMap_numBuckets___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_HashMap_numBuckets___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_HashMap_numBuckets(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
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
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_array_basic(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_assoclist(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_hashable(w);
if (lean::io_result_is_error(w)) return w;
l_mkHashMapImp___rarg___closed__1 = _init_l_mkHashMapImp___rarg___closed__1();
lean::mark_persistent(l_mkHashMapImp___rarg___closed__1);
l_mkHashMapImp___rarg___closed__2 = _init_l_mkHashMapImp___rarg___closed__2();
lean::mark_persistent(l_mkHashMapImp___rarg___closed__2);
l_HashMap_Inhabited___closed__1 = _init_l_HashMap_Inhabited___closed__1();
lean::mark_persistent(l_HashMap_Inhabited___closed__1);
return w;
}
}
