// Lean compiler output
// Module: Lean.Data.PrefixTree
// Imports: Init Std.Data.RBMap
#include <lean/lean.h>
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
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_loop(lean_object*, lean_object*);
static lean_object* l_Lean_PrefixTree_empty___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f_loop(lean_object*, lean_object*);
lean_object* l_Std_RBNode_singleton___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_fold(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_PrefixTreeNode_foldMatchingM_fold___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_PrefixTreeNode_foldMatchingM_fold___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedPrefixTreeNode___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_insertEmpty___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_PrefixTreeNode_foldMatchingM_fold___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find___at_Lean_PrefixTree_forMatchingM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_fold___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find___at_Lean_PrefixTree_forMatchingM___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find___at_Lean_PrefixTree_forM___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_insertEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_PrefixTreeNode_foldMatchingM_fold___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find___at_Lean_PrefixTree_forM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_instInhabitedPrefixTreeNode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTreeNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedPrefixTreeNode___closed__1;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_empty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instInhabitedPrefixTreeNode___closed__1;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_insertEmpty___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_PrefixTreeNode_insert_insertEmpty___rarg(x_1, x_7);
x_9 = lean_box(0);
x_10 = l_Std_RBNode_singleton___rarg(x_6, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_insertEmpty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrefixTreeNode_insert_insertEmpty___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_1);
x_15 = l_Std_RBNode_find___rarg(x_1, lean_box(0), x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_PrefixTreeNode_insert_insertEmpty___rarg(x_2, x_14);
x_17 = l_Std_RBNode_insert___rarg(x_1, x_12, x_13, x_16);
lean_ctor_set(x_3, 1, x_17);
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_1);
x_19 = l_Lean_PrefixTreeNode_insert_loop___rarg(x_1, x_2, x_18, x_14);
x_20 = l_Std_RBNode_insert___rarg(x_1, x_12, x_13, x_19);
lean_ctor_set(x_3, 1, x_20);
return x_3;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_1);
x_25 = l_Std_RBNode_find___rarg(x_1, lean_box(0), x_22, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_Lean_PrefixTreeNode_insert_insertEmpty___rarg(x_2, x_24);
x_27 = l_Std_RBNode_insert___rarg(x_1, x_22, x_23, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
lean_inc(x_1);
x_30 = l_Lean_PrefixTreeNode_insert_loop___rarg(x_1, x_2, x_29, x_24);
x_31 = l_Std_RBNode_insert___rarg(x_1, x_22, x_23, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrefixTreeNode_insert_loop___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrefixTreeNode_insert_loop___rarg(x_2, x_4, x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrefixTreeNode_insert___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_1);
x_8 = l_Std_RBNode_find___rarg(x_1, lean_box(0), x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_2 = x_10;
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f_loop(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrefixTreeNode_find_x3f_loop___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTreeNode_find_x3f_loop___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrefixTreeNode_find_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_PrefixTreeNode_foldMatchingM_fold___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_foldM___at_Lean_PrefixTreeNode_foldMatchingM_fold___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_PrefixTreeNode_foldMatchingM_fold___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_PrefixTreeNode_foldMatchingM_fold___rarg(x_1, x_2, x_3, x_6);
x_8 = lean_alloc_closure((void*)(l_Std_RBNode_foldM___at_Lean_PrefixTreeNode_foldMatchingM_fold___spec__1___rarg___lambda__1), 4, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_4);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_PrefixTreeNode_foldMatchingM_fold___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Std_RBNode_foldM___at_Lean_PrefixTreeNode_foldMatchingM_fold___spec__1___rarg(x_1, x_2, x_3, x_8);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_RBNode_foldM___at_Lean_PrefixTreeNode_foldMatchingM_fold___spec__1___rarg___lambda__2), 6, 5);
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
LEAN_EXPORT lean_object* l_Std_RBNode_foldM___at_Lean_PrefixTreeNode_foldMatchingM_fold___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_RBNode_foldM___at_Lean_PrefixTreeNode_foldMatchingM_fold___spec__1___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Std_RBNode_foldM___at_Lean_PrefixTreeNode_foldMatchingM_fold___spec__1___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_6);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_4);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_2, x_13, x_4);
x_16 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_15, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrefixTreeNode_foldMatchingM_fold___rarg), 4, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lean_PrefixTreeNode_foldMatchingM_fold___rarg(x_1, x_4, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
lean_inc(x_2);
x_12 = l_Std_RBNode_find___rarg(x_2, lean_box(0), x_11, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_3);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_5 = x_10;
x_6 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrefixTreeNode_foldMatchingM_find___rarg), 7, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l_Lean_PrefixTreeNode_foldMatchingM_find___rarg(x_1, x_3, x_5, x_6, x_4, x_2, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_PrefixTreeNode_foldMatchingM___rarg), 6, 0);
return x_5;
}
}
static lean_object* _init_l_Lean_PrefixTree_empty___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrefixTreeNode_empty(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTree_empty___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_empty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTree_empty(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTree_empty___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPrefixTree___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instInhabitedPrefixTree(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTree_empty___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionPrefixTree___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instEmptyCollectionPrefixTree(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PrefixTreeNode_insert_loop___rarg(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrefixTree_insert___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTreeNode_find_x3f_loop___rarg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrefixTree_find_x3f___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
x_8 = l_Lean_PrefixTreeNode_foldMatchingM_find___rarg(x_3, x_1, x_6, x_7, x_5, x_4, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldMatchingM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrefixTree_foldMatchingM___rarg), 7, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
lean_inc(x_5);
x_8 = l_Lean_PrefixTreeNode_foldMatchingM_find___rarg(x_3, x_1, x_5, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrefixTree_foldM___rarg), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find___at_Lean_PrefixTree_forMatchingM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lean_PrefixTreeNode_foldMatchingM_fold___rarg(x_1, x_4, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
lean_inc(x_2);
x_12 = l_Std_RBNode_find___rarg(x_2, lean_box(0), x_11, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_3);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_5 = x_10;
x_6 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find___at_Lean_PrefixTree_forMatchingM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrefixTreeNode_foldMatchingM_find___at_Lean_PrefixTree_forMatchingM___spec__1___rarg), 7, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_box(0);
x_8 = l_Lean_PrefixTreeNode_foldMatchingM_find___at_Lean_PrefixTree_forMatchingM___spec__1___rarg(x_2, x_1, x_7, x_6, x_4, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___rarg), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forMatchingM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrefixTree_forMatchingM___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find___at_Lean_PrefixTree_forM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lean_PrefixTreeNode_foldMatchingM_fold___rarg(x_1, x_4, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
lean_inc(x_2);
x_12 = l_Std_RBNode_find___rarg(x_2, lean_box(0), x_11, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_3);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_5 = x_10;
x_6 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTreeNode_foldMatchingM_find___at_Lean_PrefixTree_forM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrefixTreeNode_foldMatchingM_find___at_Lean_PrefixTree_forM___spec__1___rarg), 7, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = lean_alloc_closure((void*)(l_Lean_PrefixTree_forMatchingM___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_box(0);
x_8 = l_Lean_PrefixTreeNode_foldMatchingM_find___at_Lean_PrefixTree_forM___spec__1___rarg(x_2, x_1, x_7, x_6, x_5, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrefixTree_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrefixTree_forM___rarg), 4, 0);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Std_Data_RBMap(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_PrefixTree(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_RBMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedPrefixTreeNode___closed__1 = _init_l_Lean_instInhabitedPrefixTreeNode___closed__1();
lean_mark_persistent(l_Lean_instInhabitedPrefixTreeNode___closed__1);
l_Lean_PrefixTree_empty___closed__1 = _init_l_Lean_PrefixTree_empty___closed__1();
lean_mark_persistent(l_Lean_PrefixTree_empty___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
