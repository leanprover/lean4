// Lean compiler output
// Module: init.lean.smap
// Imports: init.data.hashmap.default init.data.rbmap.default
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
obj* l_Lean_SMap_find___boxed(obj*, obj*);
obj* l_Lean_SMap_numBuckets___rarg(obj*);
obj* l_Lean_SMap_find(obj*, obj*);
obj* l_Lean_SMap_contains___main___boxed(obj*, obj*);
obj* l_Lean_SMap_empty___rarg(obj*, obj*, obj*);
obj* l_Lean_SMap_insert___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___rarg(obj*, obj*, obj*, obj*);
uint8 l_HashMapImp_contains___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_contains(obj*, obj*);
obj* l_Lean_SMap_insert___boxed(obj*, obj*);
obj* l_Lean_SMap_HasEmptyc___boxed(obj*, obj*);
obj* l_Lean_SMap_find___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(obj*, obj*);
obj* l_Lean_SMap_Inhabited(obj*, obj*);
obj* l_HashMap_numBuckets___rarg(obj*);
obj* l_RBNode_depth___main___rarg(obj*, obj*);
obj* l_Lean_SMap_stageSizes(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_foldStage2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_empty___boxed(obj*, obj*);
obj* l_Lean_SMap_find___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_Inhabited___rarg(obj*, obj*, obj*);
obj* l_Lean_SMap_switch___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_insert___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_insert(obj*, obj*);
obj* l_Lean_SMap_insert___main(obj*, obj*);
obj* l_Lean_SMap_find_x_27___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_HasEmptyc(obj*, obj*);
obj* l_Lean_SMap_size(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_size___rarg___boxed(obj*);
obj* l_Lean_SMap_contains___main(obj*, obj*);
obj* l_Lean_SMap_contains___boxed(obj*, obj*);
obj* l_Lean_SMap_find_x_27___main___boxed(obj*, obj*);
obj* l_Lean_SMap_Inhabited___boxed(obj*, obj*);
obj* l_Lean_SMap_maxDepth___boxed(obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_SMap_contains___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_find_x_27___boxed(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
extern obj* l_RBMap_maxDepth___rarg___closed__1;
obj* l_Lean_SMap_find_x_27___main(obj*, obj*);
obj* l_HashMapImp_find___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_maxDepth___rarg(obj*);
obj* l_HashMapImp_insert___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_maxDepth(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_fold___main___rarg(obj*, obj*, obj*);
obj* l_Lean_SMap_switch(obj*, obj*);
obj* l_Lean_SMap_find_x_27(obj*, obj*);
obj* l_Lean_SMap_contains___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_size___rarg(obj*);
obj* l_Lean_SMap_numBuckets___rarg___boxed(obj*);
obj* l_RBNode_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_empty(obj*, obj*);
obj* l_Lean_SMap_find___main___boxed(obj*, obj*);
obj* l_Lean_SMap_insert___main___boxed(obj*, obj*);
uint8 l_Lean_SMap_contains___rarg(obj*, obj*, obj*, obj*, obj*);
extern obj* l_HashMap_Inhabited___closed__1;
obj* l_Lean_SMap_numBuckets___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_find___main(obj*, obj*);
obj* l_Lean_SMap_stageSizes___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_HasEmptyc___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_SMap_Inhabited___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_SMap_HasEmptyc___rarg(obj*, obj*, obj*);
obj* l_Lean_SMap_stageSizes___rarg(obj*);
obj* l_Lean_SMap_foldStage2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_maxDepth___rarg___boxed(obj*);
obj* l_Lean_SMap_switch___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_find_x_27___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_contains___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_foldStage2___rarg(obj*, obj*, obj*);
obj* l_Lean_SMap_switch___boxed(obj*, obj*);
obj* l_Lean_SMap_numBuckets(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_empty___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_SMap_size___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_Inhabited___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::box(0);
x_4 = 1;
x_5 = l_HashMap_Inhabited___closed__1;
x_6 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
lean::cnstr_set_scalar(x_6, sizeof(void*)*2, x_4);
x_7 = x_6;
return x_7;
}
}
obj* l_Lean_SMap_Inhabited(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_Inhabited___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_SMap_Inhabited___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SMap_Inhabited___rarg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_SMap_Inhabited___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_Inhabited(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_empty___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::box(0);
x_4 = 1;
x_5 = l_HashMap_Inhabited___closed__1;
x_6 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
lean::cnstr_set_scalar(x_6, sizeof(void*)*2, x_4);
x_7 = x_6;
return x_7;
}
}
obj* l_Lean_SMap_empty(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_empty___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_SMap_empty___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SMap_empty___rarg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_SMap_empty___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_empty(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_HasEmptyc___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SMap_empty___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_SMap_HasEmptyc(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_HasEmptyc___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_SMap_HasEmptyc___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_SMap_HasEmptyc___rarg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_SMap_HasEmptyc___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_HasEmptyc(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_insert___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*2);
if (x_6 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_3, 0);
x_11 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_13 = x_3;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_3);
 x_13 = lean::box(0);
}
x_14 = l_RBNode_insert___rarg(x_0, x_11, x_4, x_5);
if (lean::is_scalar(x_13)) {
 x_15 = lean::alloc_cnstr(0, 2, 1);
} else {
 x_15 = x_13;
}
lean::cnstr_set(x_15, 0, x_9);
lean::cnstr_set(x_15, 1, x_14);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_6);
x_16 = x_15;
return x_16;
}
else
{
obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_3, 0);
x_20 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_22 = x_3;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_3);
 x_22 = lean::box(0);
}
x_23 = l_HashMapImp_insert___rarg(x_1, x_2, x_18, x_4, x_5);
if (lean::is_scalar(x_22)) {
 x_24 = lean::alloc_cnstr(0, 2, 1);
} else {
 x_24 = x_22;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_20);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_6);
x_25 = x_24;
return x_25;
}
}
}
obj* l_Lean_SMap_insert___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_insert___main___rarg), 6, 0);
return x_2;
}
}
obj* l_Lean_SMap_insert___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_insert___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_SMap_insert___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Lean_SMap_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_insert___rarg), 6, 0);
return x_2;
}
}
obj* l_Lean_SMap_insert___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_insert(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_find___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*2);
if (x_5 == 0)
{
obj* x_6; obj* x_8; obj* x_12; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
lean::inc(x_4);
x_12 = l_RBNode_find___main___rarg(x_0, lean::box(0), x_8, x_4);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; 
x_13 = l_HashMapImp_find___rarg(x_1, x_2, x_6, x_4);
lean::dec(x_6);
return x_13;
}
else
{
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_2);
return x_12;
}
}
else
{
obj* x_20; obj* x_23; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_3, 0);
lean::inc(x_20);
lean::dec(x_3);
x_23 = l_HashMapImp_find___rarg(x_1, x_2, x_20, x_4);
lean::dec(x_20);
return x_23;
}
}
}
obj* l_Lean_SMap_find___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_find___main___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_SMap_find___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_find___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_SMap_find___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Lean_SMap_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_find___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_SMap_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Lean_SMap_contains___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*2);
if (x_5 == 0)
{
obj* x_6; obj* x_8; uint8 x_12; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
lean::inc(x_4);
x_12 = l_HashMapImp_contains___rarg(x_1, x_2, x_6, x_4);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_14; 
x_14 = l_RBNode_find___main___rarg(x_0, lean::box(0), x_8, x_4);
if (lean::obj_tag(x_14) == 0)
{
uint8 x_15; 
x_15 = 0;
return x_15;
}
else
{
uint8 x_17; 
lean::dec(x_14);
x_17 = 1;
return x_17;
}
}
else
{
uint8 x_21; 
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
x_21 = 1;
return x_21;
}
}
else
{
obj* x_23; uint8 x_26; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_3, 0);
lean::inc(x_23);
lean::dec(x_3);
x_26 = l_HashMapImp_contains___rarg(x_1, x_2, x_23, x_4);
lean::dec(x_23);
return x_26;
}
}
}
obj* l_Lean_SMap_contains___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_contains___main___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_SMap_contains___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_Lean_SMap_contains___main___rarg(x_0, x_1, x_2, x_3, x_4);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_Lean_SMap_contains___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_contains___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Lean_SMap_contains___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = l_Lean_SMap_contains___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Lean_SMap_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_contains___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_SMap_contains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_Lean_SMap_contains___rarg(x_0, x_1, x_2, x_3, x_4);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_Lean_SMap_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_contains(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_find_x_27___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*2);
if (x_5 == 0)
{
obj* x_6; obj* x_8; obj* x_12; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
lean::inc(x_4);
x_12 = l_HashMapImp_find___rarg(x_1, x_2, x_6, x_4);
lean::dec(x_6);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; 
x_14 = l_RBNode_find___main___rarg(x_0, lean::box(0), x_8, x_4);
return x_14;
}
else
{
lean::dec(x_8);
lean::dec(x_4);
lean::dec(x_0);
return x_12;
}
}
else
{
obj* x_19; obj* x_22; 
lean::dec(x_0);
x_19 = lean::cnstr_get(x_3, 0);
lean::inc(x_19);
lean::dec(x_3);
x_22 = l_HashMapImp_find___rarg(x_1, x_2, x_19, x_4);
lean::dec(x_19);
return x_22;
}
}
}
obj* l_Lean_SMap_find_x_27___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_find_x_27___main___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_SMap_find_x_27___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_find_x_27___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_find_x_27___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_SMap_find_x_27___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Lean_SMap_find_x_27(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_find_x_27___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_SMap_find_x_27___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_find_x_27(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_switch___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*2);
if (x_4 == 0)
{
return x_3;
}
else
{
obj* x_5; obj* x_7; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_9 = x_3;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_3);
 x_9 = lean::box(0);
}
x_10 = 0;
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(0, 2, 1);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_5);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_10);
x_12 = x_11;
return x_12;
}
}
}
obj* l_Lean_SMap_switch(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_switch___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Lean_SMap_switch___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_SMap_switch___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_SMap_switch___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_switch(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_foldStage2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
lean::dec(x_2);
x_6 = l_RBNode_fold___main___rarg(x_0, x_1, x_3);
return x_6;
}
}
obj* l_Lean_SMap_foldStage2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_foldStage2___rarg), 3, 0);
return x_6;
}
}
obj* l_Lean_SMap_foldStage2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_SMap_foldStage2(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_SMap_size___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_3, x_2);
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::nat_add(x_5, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_SMap_size(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_size___rarg___boxed), 1, 0);
return x_5;
}
}
obj* l_Lean_SMap_size___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_SMap_size___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_SMap_size___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_SMap_size(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_SMap_stageSizes___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_12; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::mk_nat_obj(0ul);
x_7 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_6, x_3);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_9);
lean::cnstr_set(x_12, 1, x_7);
return x_12;
}
}
obj* l_Lean_SMap_stageSizes(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_stageSizes___rarg), 1, 0);
return x_5;
}
}
obj* l_Lean_SMap_stageSizes___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_SMap_stageSizes(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_SMap_maxDepth___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::cnstr_get(x_0, 1);
x_2 = l_RBMap_maxDepth___rarg___closed__1;
x_3 = l_RBNode_depth___main___rarg(x_2, x_1);
return x_3;
}
}
obj* l_Lean_SMap_maxDepth(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_maxDepth___rarg___boxed), 1, 0);
return x_5;
}
}
obj* l_Lean_SMap_maxDepth___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_SMap_maxDepth___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_SMap_maxDepth___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_SMap_maxDepth(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_SMap_numBuckets___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = l_HashMap_numBuckets___rarg(x_1);
return x_2;
}
}
obj* l_Lean_SMap_numBuckets(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_numBuckets___rarg___boxed), 1, 0);
return x_5;
}
}
obj* l_Lean_SMap_numBuckets___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_SMap_numBuckets___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_SMap_numBuckets___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_SMap_numBuckets(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* initialize_init_data_hashmap_default(obj*);
obj* initialize_init_data_rbmap_default(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_smap(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_hashmap_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_rbmap_default(w);
if (io_result_is_error(w)) return w;
return w;
}
