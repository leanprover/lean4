// Lean compiler output
// Module: init.lean.smap
// Imports: init.data.hashmap.default init.data.rbmap.default
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
lean_object* l_Lean_SMap_numBuckets___rarg(lean_object*);
lean_object* l_Lean_SMap_find(lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_contains(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_SMap_Inhabited(lean_object*, lean_object*);
lean_object* l_HashMap_numBuckets___rarg(lean_object*);
lean_object* l_RBNode_depth___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_SMap_stageSizes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_foldStage2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_Inhabited___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_HasEmptyc(lean_object*, lean_object*);
lean_object* l_Lean_SMap_size(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_size___rarg___boxed(lean_object*);
lean_object* l_Lean_SMap_maxDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_RBMap_maxDepth___rarg___closed__1;
lean_object* l_HashMapImp_find___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_maxDepth___rarg(lean_object*);
lean_object* l_HashMapImp_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_maxDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x27(lean_object*, lean_object*);
lean_object* l_Lean_SMap_contains___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_size___rarg(lean_object*);
lean_object* l_Lean_SMap_numBuckets___rarg___boxed(lean_object*);
lean_object* l_RBNode_find___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty(lean_object*, lean_object*);
uint8_t l_Lean_SMap_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_HashMap_Inhabited___closed__1;
lean_object* l_Lean_SMap_numBuckets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_stageSizes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_HasEmptyc___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_Inhabited___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_stageSizes___rarg___boxed(lean_object*);
lean_object* l_Lean_SMap_HasEmptyc___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_stageSizes___rarg(lean_object*);
lean_object* l_Lean_SMap_foldStage2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_maxDepth___rarg___boxed(lean_object*);
lean_object* l_Lean_SMap_switch___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_foldStage2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_numBuckets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_Inhabited___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = 1;
x_6 = l_HashMap_Inhabited___closed__1;
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_5);
return x_7;
}
}
lean_object* l_Lean_SMap_Inhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_Inhabited___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_Inhabited___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_Inhabited___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_SMap_empty___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = 1;
x_6 = l_HashMap_Inhabited___closed__1;
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_5);
return x_7;
}
}
lean_object* l_Lean_SMap_empty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_empty___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_empty___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_empty___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_SMap_HasEmptyc___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_empty___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_SMap_HasEmptyc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_HasEmptyc___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_HasEmptyc___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_HasEmptyc___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_SMap_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 1);
x_10 = l_RBNode_insert___rarg(x_1, x_9, x_5, x_6);
lean_ctor_set(x_4, 1, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = l_RBNode_insert___rarg(x_1, x_12, x_5, x_6);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_7);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = l_HashMapImp_insert___rarg(x_2, x_3, x_16, x_5, x_6);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = l_HashMapImp_insert___rarg(x_2, x_3, x_18, x_5, x_6);
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_7);
return x_21;
}
}
}
}
lean_object* l_Lean_SMap_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_insert___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_find___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_5);
x_9 = l_RBNode_find___main___rarg(x_1, lean_box(0), x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = l_HashMapImp_find___rarg(x_2, x_3, x_7, x_5);
lean_dec(x_7);
return x_10;
}
else
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = l_HashMapImp_find___rarg(x_2, x_3, x_11, x_5);
lean_dec(x_11);
return x_12;
}
}
}
lean_object* l_Lean_SMap_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_find___rarg), 5, 0);
return x_3;
}
}
uint8_t l_Lean_SMap_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_5);
x_9 = l_HashMapImp_contains___rarg(x_2, x_3, x_7, x_5);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_RBNode_find___main___rarg(x_1, lean_box(0), x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_13 = 1;
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = l_HashMapImp_contains___rarg(x_2, x_3, x_14, x_5);
lean_dec(x_14);
return x_15;
}
}
}
lean_object* l_Lean_SMap_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_contains___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_SMap_contains___rarg(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_SMap_find_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_5);
x_9 = l_HashMapImp_find___rarg(x_2, x_3, x_7, x_5);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = l_RBNode_find___main___rarg(x_1, lean_box(0), x_8, x_5);
return x_10;
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = l_HashMapImp_find___rarg(x_2, x_3, x_11, x_5);
lean_dec(x_11);
return x_12;
}
}
}
lean_object* l_Lean_SMap_find_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_find_x27___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_switch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
if (x_5 == 0)
{
return x_4;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = 0;
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_10);
return x_11;
}
}
}
}
lean_object* l_Lean_SMap_switch(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_SMap_switch___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Lean_SMap_switch___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SMap_switch___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_SMap_foldStage2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_RBNode_fold___main___rarg(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_SMap_foldStage2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_SMap_foldStage2___rarg), 3, 0);
return x_7;
}
}
lean_object* l_Lean_SMap_foldStage2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_SMap_foldStage2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_SMap_size___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_4, x_3);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_nat_add(x_6, x_5);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_SMap_size(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_SMap_size___rarg___boxed), 1, 0);
return x_6;
}
}
lean_object* l_Lean_SMap_size___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_size___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SMap_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_SMap_size(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_SMap_stageSizes___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_4, x_3);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
lean_object* l_Lean_SMap_stageSizes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_SMap_stageSizes___rarg___boxed), 1, 0);
return x_6;
}
}
lean_object* l_Lean_SMap_stageSizes___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_stageSizes___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SMap_stageSizes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_SMap_stageSizes(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_SMap_maxDepth___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_RBMap_maxDepth___rarg___closed__1;
x_4 = l_RBNode_depth___main___rarg(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_SMap_maxDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_SMap_maxDepth___rarg___boxed), 1, 0);
return x_6;
}
}
lean_object* l_Lean_SMap_maxDepth___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_maxDepth___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SMap_maxDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_SMap_maxDepth(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_SMap_numBuckets___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_HashMap_numBuckets___rarg(x_2);
return x_3;
}
}
lean_object* l_Lean_SMap_numBuckets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_SMap_numBuckets___rarg___boxed), 1, 0);
return x_6;
}
}
lean_object* l_Lean_SMap_numBuckets___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_SMap_numBuckets___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_SMap_numBuckets___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_SMap_numBuckets(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_init_data_hashmap_default(lean_object*);
lean_object* initialize_init_data_rbmap_default(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_smap(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_hashmap_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_rbmap_default(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
