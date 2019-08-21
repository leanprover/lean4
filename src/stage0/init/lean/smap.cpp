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
obj* l_Lean_SMap_numBuckets___rarg(obj*);
obj* l_Lean_SMap_find(obj*, obj*);
obj* l_Lean_SMap_empty___rarg(obj*, obj*, obj*);
obj* l_Lean_SMap_insert___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___rarg(obj*, obj*, obj*, obj*);
uint8 l_HashMapImp_contains___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_contains(obj*, obj*);
obj* l_Lean_SMap_find___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(obj*, obj*);
obj* l_Lean_SMap_Inhabited(obj*, obj*);
obj* l_HashMap_numBuckets___rarg(obj*);
obj* l_RBNode_depth___main___rarg(obj*, obj*);
obj* l_Lean_SMap_stageSizes(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_foldStage2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_Inhabited___rarg(obj*, obj*, obj*);
obj* l_Lean_SMap_switch___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_insert(obj*, obj*);
obj* l_Lean_SMap_find_x27___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_HasEmptyc(obj*, obj*);
obj* l_Lean_SMap_size(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_size___rarg___boxed(obj*);
obj* l_Lean_SMap_maxDepth___boxed(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
extern obj* l_RBMap_maxDepth___rarg___closed__1;
obj* l_HashMapImp_find___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_maxDepth___rarg(obj*);
obj* l_HashMapImp_insert___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_maxDepth(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_fold___main___rarg(obj*, obj*, obj*);
obj* l_Lean_SMap_switch(obj*, obj*);
obj* l_Lean_SMap_find_x27(obj*, obj*);
obj* l_Lean_SMap_contains___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_size___rarg(obj*);
obj* l_Lean_SMap_numBuckets___rarg___boxed(obj*);
obj* l_RBNode_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_empty(obj*, obj*);
uint8 l_Lean_SMap_contains___rarg(obj*, obj*, obj*, obj*, obj*);
extern obj* l_HashMap_Inhabited___closed__1;
obj* l_Lean_SMap_numBuckets___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_stageSizes___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_HasEmptyc___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_SMap_Inhabited___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_SMap_stageSizes___rarg___boxed(obj*);
obj* l_Lean_SMap_HasEmptyc___rarg(obj*, obj*, obj*);
obj* l_Lean_SMap_stageSizes___rarg(obj*);
obj* l_Lean_SMap_foldStage2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_maxDepth___rarg___boxed(obj*);
obj* l_Lean_SMap_switch___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_foldStage2___rarg(obj*, obj*, obj*);
obj* l_Lean_SMap_numBuckets(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_empty___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_SMap_size___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_SMap_Inhabited___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
x_5 = 1;
x_6 = l_HashMap_Inhabited___closed__1;
x_7 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set_uint8(x_7, sizeof(void*)*2, x_5);
return x_7;
}
}
obj* l_Lean_SMap_Inhabited(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_Inhabited___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Lean_SMap_Inhabited___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_SMap_Inhabited___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_SMap_empty___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
x_5 = 1;
x_6 = l_HashMap_Inhabited___closed__1;
x_7 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set_uint8(x_7, sizeof(void*)*2, x_5);
return x_7;
}
}
obj* l_Lean_SMap_empty(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_empty___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Lean_SMap_empty___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_SMap_empty___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_SMap_HasEmptyc___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_SMap_empty___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_SMap_HasEmptyc(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_HasEmptyc___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Lean_SMap_HasEmptyc___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_SMap_HasEmptyc___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_SMap_insert___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = lean::cnstr_get_uint8(x_4, sizeof(void*)*2);
if (x_7 == 0)
{
uint8 x_8; 
lean::dec(x_3);
lean::dec(x_2);
x_8 = !lean::is_exclusive(x_4);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_4, 1);
x_10 = l_RBNode_insert___rarg(x_1, x_9, x_5, x_6);
lean::cnstr_set(x_4, 1, x_10);
return x_4;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_4, 0);
x_12 = lean::cnstr_get(x_4, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_4);
x_13 = l_RBNode_insert___rarg(x_1, x_12, x_5, x_6);
x_14 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set_uint8(x_14, sizeof(void*)*2, x_7);
return x_14;
}
}
else
{
uint8 x_15; 
lean::dec(x_1);
x_15 = !lean::is_exclusive(x_4);
if (x_15 == 0)
{
obj* x_16; obj* x_17; 
x_16 = lean::cnstr_get(x_4, 0);
x_17 = l_HashMapImp_insert___rarg(x_2, x_3, x_16, x_5, x_6);
lean::cnstr_set(x_4, 0, x_17);
return x_4;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_18 = lean::cnstr_get(x_4, 0);
x_19 = lean::cnstr_get(x_4, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_4);
x_20 = l_HashMapImp_insert___rarg(x_2, x_3, x_18, x_5, x_6);
x_21 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_19);
lean::cnstr_set_uint8(x_21, sizeof(void*)*2, x_7);
return x_21;
}
}
}
}
obj* l_Lean_SMap_insert(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_insert___rarg), 6, 0);
return x_3;
}
}
obj* l_Lean_SMap_find___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = lean::cnstr_get_uint8(x_4, sizeof(void*)*2);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_4, 1);
lean::inc(x_8);
lean::dec(x_4);
lean::inc(x_5);
x_9 = l_RBNode_find___main___rarg(x_1, lean::box(0), x_8, x_5);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; 
x_10 = l_HashMapImp_find___rarg(x_2, x_3, x_7, x_5);
lean::dec(x_7);
return x_10;
}
else
{
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_9;
}
}
else
{
obj* x_11; obj* x_12; 
lean::dec(x_1);
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
lean::dec(x_4);
x_12 = l_HashMapImp_find___rarg(x_2, x_3, x_11, x_5);
lean::dec(x_11);
return x_12;
}
}
}
obj* l_Lean_SMap_find(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_find___rarg), 5, 0);
return x_3;
}
}
uint8 l_Lean_SMap_contains___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = lean::cnstr_get_uint8(x_4, sizeof(void*)*2);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_4, 1);
lean::inc(x_8);
lean::dec(x_4);
lean::inc(x_5);
x_9 = l_HashMapImp_contains___rarg(x_2, x_3, x_7, x_5);
lean::dec(x_7);
if (x_9 == 0)
{
obj* x_10; 
x_10 = l_RBNode_find___main___rarg(x_1, lean::box(0), x_8, x_5);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8 x_12; 
lean::dec(x_10);
x_12 = 1;
return x_12;
}
}
else
{
uint8 x_13; 
lean::dec(x_8);
lean::dec(x_5);
lean::dec(x_1);
x_13 = 1;
return x_13;
}
}
else
{
obj* x_14; uint8 x_15; 
lean::dec(x_1);
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
lean::dec(x_4);
x_15 = l_HashMapImp_contains___rarg(x_2, x_3, x_14, x_5);
lean::dec(x_14);
return x_15;
}
}
}
obj* l_Lean_SMap_contains(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_contains___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Lean_SMap_contains___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = l_Lean_SMap_contains___rarg(x_1, x_2, x_3, x_4, x_5);
x_7 = lean::box(x_6);
return x_7;
}
}
obj* l_Lean_SMap_find_x27___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = lean::cnstr_get_uint8(x_4, sizeof(void*)*2);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_4, 1);
lean::inc(x_8);
lean::dec(x_4);
lean::inc(x_5);
x_9 = l_HashMapImp_find___rarg(x_2, x_3, x_7, x_5);
lean::dec(x_7);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; 
x_10 = l_RBNode_find___main___rarg(x_1, lean::box(0), x_8, x_5);
return x_10;
}
else
{
lean::dec(x_8);
lean::dec(x_5);
lean::dec(x_1);
return x_9;
}
}
else
{
obj* x_11; obj* x_12; 
lean::dec(x_1);
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
lean::dec(x_4);
x_12 = l_HashMapImp_find___rarg(x_2, x_3, x_11, x_5);
lean::dec(x_11);
return x_12;
}
}
}
obj* l_Lean_SMap_find_x27(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_find_x27___rarg), 5, 0);
return x_3;
}
}
obj* l_Lean_SMap_switch___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::cnstr_get_uint8(x_4, sizeof(void*)*2);
if (x_5 == 0)
{
return x_4;
}
else
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_4);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = 0;
lean::cnstr_set_uint8(x_4, sizeof(void*)*2, x_7);
return x_4;
}
else
{
obj* x_8; obj* x_9; uint8 x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_4);
x_10 = 0;
x_11 = lean::alloc_cnstr(0, 2, 1);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_9);
lean::cnstr_set_uint8(x_11, sizeof(void*)*2, x_10);
return x_11;
}
}
}
}
obj* l_Lean_SMap_switch(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_switch___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_Lean_SMap_switch___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_SMap_switch___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_SMap_foldStage2___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_5 = l_RBNode_fold___main___rarg(x_1, x_2, x_4);
return x_5;
}
}
obj* l_Lean_SMap_foldStage2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_foldStage2___rarg), 3, 0);
return x_7;
}
}
obj* l_Lean_SMap_foldStage2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_SMap_foldStage2(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_SMap_size___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_4, x_3);
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean::nat_add(x_6, x_5);
lean::dec(x_5);
return x_7;
}
}
obj* l_Lean_SMap_size(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_size___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_Lean_SMap_size___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_size___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_size___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_SMap_size(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_SMap_stageSizes___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_4, x_3);
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
obj* l_Lean_SMap_stageSizes(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_stageSizes___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_Lean_SMap_stageSizes___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_stageSizes___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_stageSizes___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_SMap_stageSizes(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_SMap_maxDepth___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 1);
x_3 = l_RBMap_maxDepth___rarg___closed__1;
x_4 = l_RBNode_depth___main___rarg(x_3, x_2);
return x_4;
}
}
obj* l_Lean_SMap_maxDepth(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_maxDepth___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_Lean_SMap_maxDepth___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_maxDepth___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_maxDepth___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_SMap_maxDepth(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_SMap_numBuckets___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = l_HashMap_numBuckets___rarg(x_2);
return x_3;
}
}
obj* l_Lean_SMap_numBuckets(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_SMap_numBuckets___rarg___boxed), 1, 0);
return x_6;
}
}
obj* l_Lean_SMap_numBuckets___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_SMap_numBuckets___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_SMap_numBuckets___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_SMap_numBuckets(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
return x_6;
}
}
obj* initialize_init_data_hashmap_default(obj*);
obj* initialize_init_data_rbmap_default(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_smap(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_hashmap_default(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_rbmap_default(w);
if (lean::io_result_is_error(w)) return w;
return w;
}
