// Lean compiler output
// Module: Init.Data.RBTree.Basic
// Imports: Init.Data.RBMap.Basic
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
lean_object* l_RBTree_min___boxed(lean_object*, lean_object*);
lean_object* l_RBTree_HasEmptyc___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_any___main___at_RBTree_any___spec__1(lean_object*);
lean_object* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_findCore___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___rarg(lean_object*, lean_object*);
lean_object* l_rbtreeOf(lean_object*);
lean_object* l_List_foldl___main___at_RBTree_fromList___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_max___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_all___main___at_RBTree_subset___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_ofList___main(lean_object*);
lean_object* l_RBNode_fold___main___at_RBTree_fold___spec__1(lean_object*, lean_object*);
lean_object* l_RBTree_seteq___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_toList(lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_any___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBTree_isEmpty___rarg___boxed(lean_object*);
uint8_t l_RBTree_all___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_RBTree_min___rarg(lean_object*);
lean_object* l_RBTree_all___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___at_RBTree_mfor___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_erase___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_depth___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBTree_fromList___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_min___main___rarg(lean_object*);
lean_object* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_max___main___rarg(lean_object*);
lean_object* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_empty(lean_object*, lean_object*);
lean_object* l_RBTree_toList___rarg(lean_object*);
lean_object* l_RBTree_HasRepr___boxed(lean_object*, lean_object*);
lean_object* l_RBTree_HasRepr___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_depth___main___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_revFold___main___at_RBTree_toList___spec__1(lean_object*);
lean_object* l_RBTree_erase(lean_object*);
uint8_t l_RBTree_any___rarg(lean_object*, lean_object*);
lean_object* l_RBTree_empty___boxed(lean_object*, lean_object*);
lean_object* l_RBTree_HasRepr___rarg___closed__1;
lean_object* l_RBTree_depth___boxed(lean_object*, lean_object*);
lean_object* l_RBTree_depth___rarg(lean_object*, lean_object*);
lean_object* l_RBTree_find(lean_object*);
lean_object* l_RBTree_find___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_RBTree_contains___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_max___rarg___boxed(lean_object*);
lean_object* l_RBTree_revFold___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkRBTree(lean_object*, lean_object*);
lean_object* l_RBTree_min(lean_object*, lean_object*);
lean_object* l_RBTree_min___rarg___closed__1;
uint8_t l_RBNode_any___main___at_RBTree_any___spec__1___rarg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_RBTree_min___rarg___boxed(lean_object*);
lean_object* l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBTree_contains___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_RBTree_seteq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_fromList(lean_object*);
lean_object* l_RBTree_erase___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_seteq(lean_object*);
lean_object* l_RBTree_HasEmptyc(lean_object*, lean_object*);
lean_object* l_RBTree_revFold___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_isEmpty(lean_object*, lean_object*);
lean_object* l_RBTree_mfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_revFold___main___at_RBTree_revFold___spec__1(lean_object*, lean_object*);
lean_object* l_RBTree_mfor___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_HasRepr(lean_object*, lean_object*);
uint8_t l_RBNode_all___main___at_RBTree_all___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_RBTree_revFold(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_subset(lean_object*);
lean_object* l_RBTree_any___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_any(lean_object*, lean_object*);
lean_object* l_RBNode_all___main___at_RBTree_all___spec__1(lean_object*);
lean_object* l_RBNode_any___main___at_RBTree_any___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBTree_subset___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_mfold(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_insert___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_mfor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_fold___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_fold(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_all___main___at_RBTree_all___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBTree_contains(lean_object*);
lean_object* l_RBTree_HasRepr___rarg(lean_object*, lean_object*);
uint8_t l_RBTree_subset___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_mkRBTree___boxed(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_RBTree_fromList___spec__1(lean_object*);
lean_object* l_rbtreeOf___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___at_RBTree_mfold___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_all___rarg___boxed(lean_object*, lean_object*);
uint8_t l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_ofList___main___rarg(lean_object*, lean_object*);
lean_object* l_RBTree_isEmpty___boxed(lean_object*, lean_object*);
lean_object* l_RBTree_max___rarg(lean_object*);
lean_object* l_RBTree_mfold___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_insert(lean_object*);
lean_object* l_RBNode_all___main___at_RBTree_subset___spec__1(lean_object*);
uint8_t l_RBTree_isEmpty___rarg(lean_object*);
lean_object* l_RBTree_ofList(lean_object*);
lean_object* l_RBTree_depth(lean_object*, lean_object*);
lean_object* l_RBTree_fold___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_toList___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_ofList___rarg(lean_object*, lean_object*);
lean_object* l_RBTree_mfor___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBTree_all(lean_object*, lean_object*);
lean_object* l_RBTree_toList___rarg___boxed(lean_object*);
lean_object* l_RBTree_max(lean_object*, lean_object*);
lean_object* l_mkRBTree(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
lean_object* l_mkRBTree___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_mkRBTree(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBTree_HasEmptyc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
lean_object* l_RBTree_HasEmptyc___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBTree_HasEmptyc(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBTree_empty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
lean_object* l_RBTree_empty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBTree_empty(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBTree_depth___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_depth___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_RBTree_depth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBTree_depth___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_RBTree_depth___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBTree_depth___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBTree_depth___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBTree_depth(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
x_7 = l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg(x_1, x_2, x_4);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_7, x_5);
x_2 = x_8;
x_3 = x_6;
goto _start;
}
}
}
lean_object* l_RBNode_fold___main___at_RBTree_fold___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_RBTree_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_RBTree_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBTree_fold___rarg), 3, 0);
return x_4;
}
}
lean_object* l_RBTree_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBTree_fold(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
x_7 = l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg(x_1, x_2, x_6);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_7, x_5);
x_2 = x_8;
x_3 = x_4;
goto _start;
}
}
}
lean_object* l_RBNode_revFold___main___at_RBTree_revFold___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_RBTree_revFold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_RBTree_revFold(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBTree_revFold___rarg), 3, 0);
return x_4;
}
}
lean_object* l_RBTree_revFold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBTree_revFold(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_7 = lean_apply_2(x_1, x_6, x_2);
x_8 = lean_alloc_closure((void*)(l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__1), 4, 3);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_4);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(x_1, x_2, x_3, x_8);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__2), 6, 5);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_10);
lean_closure_set(x_13, 4, x_11);
x_14 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
}
lean_object* l_RBNode_mfold___main___at_RBTree_mfold___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg), 4, 0);
return x_4;
}
}
lean_object* l_RBTree_mfold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_RBTree_mfold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_RBTree_mfold___rarg), 4, 0);
return x_5;
}
}
lean_object* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_mfold___main___at_RBTree_mfold___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBTree_mfold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBTree_mfold(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_3);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_12);
x_14 = lean_alloc_closure((void*)(l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__1), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_4);
x_15 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
lean_object* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_2(x_6, lean_box(0), x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(x_1, x_2, x_3, x_8);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_9);
lean_closure_set(x_13, 3, x_10);
lean_closure_set(x_13, 4, x_11);
x_14 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
}
lean_object* l_RBNode_mfold___main___at_RBTree_mfor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg), 4, 0);
return x_4;
}
}
lean_object* l_RBTree_mfor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_RBTree_mfor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_RBTree_mfor___rarg), 3, 0);
return x_5;
}
}
lean_object* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBTree_mfor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBTree_mfor(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
uint8_t l_RBTree_isEmpty___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
lean_object* l_RBTree_isEmpty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBTree_isEmpty___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_RBTree_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_RBTree_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_RBTree_isEmpty___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBTree_isEmpty(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 3);
x_6 = l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(x_1, x_5);
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_3;
goto _start;
}
}
}
lean_object* l_RBNode_revFold___main___at_RBTree_toList___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_RBTree_toList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_RBTree_toList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBTree_toList___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBTree_toList___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBTree_toList___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_RBTree_toList___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBTree_toList(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l_RBTree_min___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_RBTree_min___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBNode_min___main___rarg(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_RBTree_min___rarg___closed__1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
lean_object* l_RBTree_min(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBTree_min___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_RBTree_min___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBTree_min___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_RBTree_min___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBTree_min(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBTree_max___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBNode_max___main___rarg(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_RBTree_min___rarg___closed__1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
lean_object* l_RBTree_max(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBTree_max___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_RBTree_max___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBTree_max___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_RBTree_max___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBTree_max(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l_RBTree_HasRepr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rbtreeOf ");
return x_1;
}
}
lean_object* l_RBTree_HasRepr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_RBTree_toList___rarg(x_2);
x_4 = l_List_repr___rarg(x_1, x_3);
x_5 = l_RBTree_HasRepr___rarg___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_RBTree_HasRepr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBTree_HasRepr___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_RBTree_HasRepr___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBTree_HasRepr___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBTree_HasRepr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBTree_HasRepr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBTree_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_RBNode_insert___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_RBTree_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBTree_insert___rarg), 3, 0);
return x_2;
}
}
lean_object* l_RBTree_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_erase___rarg(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_RBTree_erase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBTree_erase___rarg), 3, 0);
return x_2;
}
}
lean_object* l_RBTree_ofList___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = l_RBTree_ofList___main___rarg(x_1, x_5);
x_7 = lean_box(0);
x_8 = l_RBNode_insert___rarg(x_1, x_6, x_4, x_7);
return x_8;
}
}
}
lean_object* l_RBTree_ofList___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBTree_ofList___main___rarg), 2, 0);
return x_2;
}
}
lean_object* l_RBTree_ofList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBTree_ofList___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_RBTree_ofList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBTree_ofList___rarg), 2, 0);
return x_2;
}
}
lean_object* l_RBTree_find___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_findCore___main___rarg(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
lean_object* l_RBTree_find(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBTree_find___rarg), 3, 0);
return x_2;
}
}
uint8_t l_RBTree_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_findCore___main___rarg(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
}
}
lean_object* l_RBTree_contains(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBTree_contains___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBTree_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_RBTree_contains___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_List_foldl___main___at_RBTree_fromList___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_box(0);
lean_inc(x_1);
x_7 = l_RBNode_insert___rarg(x_1, x_2, x_4, x_6);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
}
}
lean_object* l_List_foldl___main___at_RBTree_fromList___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___main___at_RBTree_fromList___spec__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_RBTree_fromList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_foldl___main___at_RBTree_fromList___spec__1___rarg(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_RBTree_fromList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBTree_fromList___rarg), 2, 0);
return x_2;
}
}
uint8_t l_RBNode_all___main___at_RBTree_all___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
lean_inc(x_1);
x_10 = l_RBNode_all___main___at_RBTree_all___spec__1___rarg(x_1, x_4);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_1);
x_11 = 0;
return x_11;
}
else
{
x_2 = x_6;
goto _start;
}
}
}
}
}
lean_object* l_RBNode_all___main___at_RBTree_all___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_all___main___at_RBTree_all___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
uint8_t l_RBTree_all___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_RBNode_all___main___at_RBTree_all___spec__1___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_RBTree_all(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBTree_all___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_RBNode_all___main___at_RBTree_all___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_RBNode_all___main___at_RBTree_all___spec__1___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_RBTree_all___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_RBTree_all___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_RBTree_all___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBTree_all(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_RBNode_any___main___at_RBTree_any___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_5);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_inc(x_1);
x_9 = l_RBNode_any___main___at_RBTree_any___spec__1___rarg(x_1, x_4);
if (x_9 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_1);
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
}
}
lean_object* l_RBNode_any___main___at_RBTree_any___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_any___main___at_RBTree_any___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
uint8_t l_RBTree_any___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_RBNode_any___main___at_RBTree_any___spec__1___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_RBTree_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBTree_any___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_RBNode_any___main___at_RBTree_any___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_RBNode_any___main___at_RBTree_any___spec__1___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_RBTree_any___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_RBTree_any___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_RBTree_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBTree_any(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = 1;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_RBNode_findCore___main___rarg(x_1, x_2, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(x_1, x_2, x_5);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_11 = 0;
return x_11;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
}
lean_object* l_RBNode_all___main___at_RBTree_subset___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_all___main___at_RBTree_subset___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
uint8_t l_RBTree_subset___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_RBTree_subset(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBTree_subset___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBNode_all___main___at_RBTree_subset___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_RBTree_subset___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_RBTree_subset___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_RBTree_seteq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_inc(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(x_1, x_3, x_2);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(x_1, x_2, x_3);
return x_6;
}
}
}
lean_object* l_RBTree_seteq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBTree_seteq___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_RBTree_seteq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_RBTree_seteq___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_rbtreeOf___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBTree_fromList___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_rbtreeOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_rbtreeOf___rarg), 2, 0);
return x_2;
}
}
lean_object* initialize_Init_Data_RBMap_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_RBTree_Basic(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_RBMap_Basic(w);
if (lean_io_result_is_error(w)) return w;
l_RBTree_min___rarg___closed__1 = _init_l_RBTree_min___rarg___closed__1();
lean_mark_persistent(l_RBTree_min___rarg___closed__1);
l_RBTree_HasRepr___rarg___closed__1 = _init_l_RBTree_HasRepr___rarg___closed__1();
lean_mark_persistent(l_RBTree_HasRepr___rarg___closed__1);
return w;
}
#ifdef __cplusplus
}
#endif
