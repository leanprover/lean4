// Lean compiler output
// Module: init.data.rbtree.basic
// Imports: init.data.rbmap.basic
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
obj* l_RBTree_min___boxed(obj*, obj*);
obj* l_RBTree_HasEmptyc___boxed(obj*, obj*);
obj* l_RBNode_any___main___at_RBTree_any___spec__1(obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___boxed(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_findCore___main___rarg(obj*, obj*, obj*);
obj* l_rbtreeOf(obj*);
obj* l_List_foldl___main___at_RBTree_fromList___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBTree_max___boxed(obj*, obj*);
obj* l_RBTree_HasInsert(obj*);
obj* l_RBNode_all___main___at_RBTree_subset___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_RBTree_ofList___main(obj*);
obj* l_RBNode_fold___main___at_RBTree_fold___spec__1(obj*, obj*);
obj* l_RBTree_seteq___rarg___boxed(obj*, obj*, obj*);
obj* l_RBTree_toList(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_RBTree_any___rarg___boxed(obj*, obj*);
obj* l_RBTree_isEmpty___rarg___boxed(obj*);
uint8 l_RBTree_all___rarg(obj*, obj*);
obj* l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(obj*, obj*);
obj* l_RBTree_min___rarg(obj*);
obj* l_RBTree_all___boxed(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1(obj*, obj*, obj*);
obj* l_RBNode_erase___rarg(obj*, obj*, obj*);
obj* l_RBTree_depth___rarg___boxed(obj*, obj*);
obj* l_RBTree_fromList___rarg(obj*, obj*);
obj* l_RBNode_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_min___main___rarg(obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_RBNode_max___main___rarg(obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBTree_toList___rarg(obj*);
obj* l_RBTree_HasRepr___boxed(obj*, obj*);
obj* l_RBTree_HasRepr___rarg___boxed(obj*, obj*);
obj* l_RBNode_depth___main___rarg(obj*, obj*);
obj* l_RBNode_revFold___main___at_RBTree_toList___spec__1(obj*);
obj* l_RBTree_erase(obj*);
uint8 l_RBTree_any___rarg(obj*, obj*);
obj* l_RBTree_HasRepr___rarg___closed__1;
obj* l_RBTree_depth___boxed(obj*, obj*);
obj* l_RBTree_depth___rarg(obj*, obj*);
obj* l_RBTree_find(obj*);
obj* l_RBTree_find___rarg(obj*, obj*, obj*);
uint8 l_RBTree_contains___rarg(obj*, obj*, obj*);
obj* l_RBTree_max___rarg___boxed(obj*);
obj* l_RBTree_revFold___rarg(obj*, obj*, obj*);
obj* l_mkRBTree(obj*, obj*);
obj* l_RBTree_min(obj*, obj*);
uint8 l_RBNode_any___main___at_RBTree_any___spec__1___rarg(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_RBTree_min___rarg___boxed(obj*);
obj* l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBTree_contains___rarg___boxed(obj*, obj*, obj*);
uint8 l_RBTree_seteq___rarg(obj*, obj*, obj*);
obj* l_RBTree_fromList(obj*);
obj* l_RBTree_erase___rarg(obj*, obj*, obj*);
obj* l_RBTree_seteq(obj*);
obj* l_RBTree_HasEmptyc(obj*, obj*);
obj* l_RBTree_revFold___boxed(obj*, obj*, obj*);
obj* l_RBTree_isEmpty(obj*, obj*);
obj* l_RBTree_mfold___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_revFold___main___at_RBTree_revFold___spec__1(obj*, obj*);
obj* l_RBTree_mfor___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___boxed(obj*, obj*, obj*);
obj* l_RBTree_HasRepr(obj*, obj*);
uint8 l_RBNode_all___main___at_RBTree_all___spec__1___rarg(obj*, obj*);
obj* l_RBTree_revFold(obj*, obj*, obj*);
obj* l_RBTree_subset(obj*);
obj* l_RBTree_any___boxed(obj*, obj*);
obj* l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBTree_any(obj*, obj*);
obj* l_RBNode_all___main___at_RBTree_all___spec__1(obj*);
obj* l_RBNode_any___main___at_RBTree_any___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBTree_subset___rarg___boxed(obj*, obj*, obj*);
obj* l_RBTree_mfold(obj*, obj*, obj*, obj*);
obj* l_RBTree_insert___rarg(obj*, obj*, obj*);
obj* l_RBTree_mfor(obj*, obj*, obj*, obj*);
obj* l_RBTree_fold___rarg(obj*, obj*, obj*);
obj* l_RBTree_fold(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_all___main___at_RBTree_all___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBTree_contains(obj*);
obj* l_RBTree_HasRepr___rarg(obj*, obj*);
uint8 l_RBTree_subset___rarg(obj*, obj*, obj*);
obj* l_mkRBTree___boxed(obj*, obj*);
obj* l_List_foldl___main___at_RBTree_fromList___spec__1(obj*);
obj* l_rbtreeOf___rarg(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1(obj*, obj*, obj*);
obj* l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBTree_all___rarg___boxed(obj*, obj*);
uint8 l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBTree_ofList___main___rarg(obj*, obj*);
obj* l_RBTree_isEmpty___boxed(obj*, obj*);
obj* l_RBTree_max___rarg(obj*);
obj* l_RBTree_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_RBTree_insert(obj*);
obj* l_RBNode_all___main___at_RBTree_subset___spec__1(obj*);
uint8 l_RBTree_isEmpty___rarg(obj*);
obj* l_RBTree_ofList(obj*);
obj* l_RBTree_depth(obj*, obj*);
obj* l_RBTree_HasInsert___rarg(obj*, obj*, obj*);
obj* l_RBTree_fold___boxed(obj*, obj*, obj*);
obj* l_RBTree_toList___boxed(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBTree_ofList___rarg(obj*, obj*);
obj* l_RBTree_mfor___rarg(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBTree_all(obj*, obj*);
obj* l_RBTree_toList___rarg___boxed(obj*);
obj* l_List_repr___main___rarg(obj*, obj*);
obj* l_RBTree_max(obj*, obj*);
obj* l_mkRBTree(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_mkRBTree___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_mkRBTree(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBTree_HasEmptyc(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_RBTree_HasEmptyc___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_HasEmptyc(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBTree_depth___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_depth___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_RBTree_depth(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_depth___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBTree_depth___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_depth___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBTree_depth___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_depth(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 3);
lean::inc(x_6);
lean::dec(x_3);
lean::inc(x_1);
x_7 = l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg(x_1, x_2, x_4);
lean::inc(x_1);
x_8 = lean::apply_2(x_1, x_7, x_5);
x_2 = x_8;
x_3 = x_6;
goto _start;
}
}
}
obj* l_RBNode_fold___main___at_RBTree_fold___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg), 3, 0);
return x_3;
}
}
obj* l_RBTree_fold___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBTree_fold(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_fold___rarg), 3, 0);
return x_4;
}
}
obj* l_RBTree_fold___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBTree_fold(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 3);
lean::inc(x_6);
lean::dec(x_3);
lean::inc(x_1);
x_7 = l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg(x_1, x_2, x_6);
lean::inc(x_1);
x_8 = lean::apply_2(x_1, x_7, x_5);
x_2 = x_8;
x_3 = x_4;
goto _start;
}
}
}
obj* l_RBNode_revFold___main___at_RBTree_revFold___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg), 3, 0);
return x_3;
}
}
obj* l_RBTree_revFold___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBTree_revFold(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_revFold___rarg), 3, 0);
return x_4;
}
}
obj* l_RBTree_revFold___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBTree_revFold(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_1);
x_7 = lean::apply_2(x_1, x_6, x_2);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_3);
lean::closure_set(x_8, 1, x_1);
lean::closure_set(x_8, 2, x_4);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::apply_2(x_6, lean::box(0), x_3);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_4, 3);
lean::inc(x_10);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_1);
x_12 = l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(x_1, x_2, x_3, x_8);
lean::inc(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__2), 6, 5);
lean::closure_set(x_13, 0, x_2);
lean::closure_set(x_13, 1, x_9);
lean::closure_set(x_13, 2, x_1);
lean::closure_set(x_13, 3, x_10);
lean::closure_set(x_13, 4, x_11);
x_14 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg), 4, 0);
return x_4;
}
}
obj* l_RBTree_mfold___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_RBTree_mfold(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_mfold___rarg), 4, 0);
return x_5;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main___at_RBTree_mfold___spec__1(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBTree_mfold___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBTree_mfold(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_7, 4);
lean::inc(x_8);
lean::inc(x_2);
x_9 = lean::apply_1(x_2, x_3);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_11 = lean::box(0);
x_12 = lean::apply_2(x_10, lean::box(0), x_11);
x_13 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_9, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__1), 4, 3);
lean::closure_set(x_14, 0, x_1);
lean::closure_set(x_14, 1, x_2);
lean::closure_set(x_14, 2, x_4);
x_15 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::apply_2(x_6, lean::box(0), x_3);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_4, 3);
lean::inc(x_10);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_1);
x_12 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(x_1, x_2, x_3, x_8);
lean::inc(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2___boxed), 6, 5);
lean::closure_set(x_13, 0, x_1);
lean::closure_set(x_13, 1, x_2);
lean::closure_set(x_13, 2, x_9);
lean::closure_set(x_13, 3, x_10);
lean::closure_set(x_13, 4, x_11);
x_14 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg), 4, 0);
return x_4;
}
}
obj* l_RBTree_mfor___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_RBTree_mfor(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_mfor___rarg), 3, 0);
return x_5;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
return x_7;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBTree_mfor___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBTree_mfor(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
uint8 l_RBTree_isEmpty___rarg(obj* x_1) {
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
obj* l_RBTree_isEmpty(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_isEmpty___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_RBTree_isEmpty___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBTree_isEmpty___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBTree_isEmpty___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_isEmpty(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_2, 3);
x_6 = l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(x_1, x_5);
lean::inc(x_4);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_3;
goto _start;
}
}
}
obj* l_RBNode_revFold___main___at_RBTree_toList___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBTree_toList___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(x_2, x_1);
return x_3;
}
}
obj* l_RBTree_toList(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_toList___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBTree_toList___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_toList___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_toList___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_toList(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBTree_min___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_min___main___rarg(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
lean::cnstr_set(x_2, 0, x_6);
return x_2;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
}
}
}
obj* l_RBTree_min(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_min___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_RBTree_min___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_min___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_min___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_min(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBTree_max___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_max___main___rarg(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
lean::cnstr_set(x_2, 0, x_6);
return x_2;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
}
}
}
obj* l_RBTree_max(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_max___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_RBTree_max___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_max___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_max___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_max(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_RBTree_HasRepr___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("rbtreeOf ");
return x_1;
}
}
obj* l_RBTree_HasRepr___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_RBTree_toList___rarg(x_2);
x_4 = l_List_repr___main___rarg(x_1, x_3);
x_5 = l_RBTree_HasRepr___rarg___closed__1;
x_6 = lean::string_append(x_5, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l_RBTree_HasRepr(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_HasRepr___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBTree_HasRepr___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_HasRepr___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBTree_HasRepr___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_HasRepr(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBTree_insert___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_RBNode_insert___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_RBTree_insert(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_insert___rarg), 3, 0);
return x_2;
}
}
obj* l_RBTree_HasInsert___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_RBNode_insert___rarg(x_1, x_3, x_2, x_4);
return x_5;
}
}
obj* l_RBTree_HasInsert(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_HasInsert___rarg), 3, 0);
return x_2;
}
}
obj* l_RBTree_erase___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_erase___rarg(x_1, x_3, x_2);
return x_4;
}
}
obj* l_RBTree_erase(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_erase___rarg), 3, 0);
return x_2;
}
}
obj* l_RBTree_ofList___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
lean::inc(x_1);
x_6 = l_RBTree_ofList___main___rarg(x_1, x_5);
x_7 = lean::box(0);
x_8 = l_RBNode_insert___rarg(x_1, x_6, x_4, x_7);
return x_8;
}
}
}
obj* l_RBTree_ofList___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_ofList___main___rarg), 2, 0);
return x_2;
}
}
obj* l_RBTree_ofList___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_ofList___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_RBTree_ofList(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_ofList___rarg), 2, 0);
return x_2;
}
}
obj* l_RBTree_find___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_findCore___main___rarg(x_1, x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
else
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_4, 0);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
lean::dec(x_7);
lean::cnstr_set(x_4, 0, x_8);
return x_4;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
}
obj* l_RBTree_find(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_find___rarg), 3, 0);
return x_2;
}
}
uint8 l_RBTree_contains___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_findCore___main___rarg(x_1, x_2, x_3);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
lean::dec(x_4);
x_6 = 1;
return x_6;
}
}
}
obj* l_RBTree_contains(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_contains___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBTree_contains___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_RBTree_contains___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_List_foldl___main___at_RBTree_fromList___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
x_6 = lean::box(0);
lean::inc(x_1);
x_7 = l_RBNode_insert___rarg(x_1, x_2, x_4, x_6);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
}
}
obj* l_List_foldl___main___at_RBTree_fromList___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_RBTree_fromList___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_RBTree_fromList___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_List_foldl___main___at_RBTree_fromList___spec__1___rarg(x_2, x_3, x_1);
return x_4;
}
}
obj* l_RBTree_fromList(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_fromList___rarg), 2, 0);
return x_2;
}
}
uint8 l_RBNode_all___main___at_RBTree_all___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
lean::dec(x_1);
x_3 = 1;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_2, 3);
lean::inc(x_6);
lean::dec(x_2);
lean::inc(x_1);
x_7 = lean::apply_1(x_1, x_5);
x_8 = lean::unbox(x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_9; 
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_1);
x_9 = 0;
return x_9;
}
else
{
uint8 x_10; 
lean::inc(x_1);
x_10 = l_RBNode_all___main___at_RBTree_all___spec__1___rarg(x_1, x_4);
if (x_10 == 0)
{
uint8 x_11; 
lean::dec(x_6);
lean::dec(x_1);
x_11 = 0;
return x_11;
}
else
{
uint8 x_12; 
x_2 = x_6;
goto _start;
}
}
}
}
}
obj* l_RBNode_all___main___at_RBTree_all___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_all___main___at_RBTree_all___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
uint8 l_RBTree_all___rarg(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_all___main___at_RBTree_all___spec__1___rarg(x_2, x_1);
return x_3;
}
}
obj* l_RBTree_all(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_all___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBNode_all___main___at_RBTree_all___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBNode_all___main___at_RBTree_all___spec__1___rarg(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBTree_all___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBTree_all___rarg(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBTree_all___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_all(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBNode_any___main___at_RBTree_any___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
lean::dec(x_1);
x_3 = 0;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_2, 3);
lean::inc(x_6);
lean::dec(x_2);
lean::inc(x_1);
x_7 = lean::apply_1(x_1, x_5);
x_8 = lean::unbox(x_7);
lean::dec(x_7);
if (x_8 == 0)
{
uint8 x_9; 
lean::inc(x_1);
x_9 = l_RBNode_any___main___at_RBTree_any___spec__1___rarg(x_1, x_4);
if (x_9 == 0)
{
uint8 x_10; 
x_2 = x_6;
goto _start;
}
else
{
uint8 x_11; 
lean::dec(x_6);
lean::dec(x_1);
x_11 = 1;
return x_11;
}
}
else
{
uint8 x_12; 
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_1);
x_12 = 1;
return x_12;
}
}
}
}
obj* l_RBNode_any___main___at_RBTree_any___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_any___main___at_RBTree_any___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
uint8 l_RBTree_any___rarg(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_any___main___at_RBTree_any___spec__1___rarg(x_2, x_1);
return x_3;
}
}
obj* l_RBTree_any(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_any___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBNode_any___main___at_RBTree_any___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBNode_any___main___at_RBTree_any___spec__1___rarg(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBTree_any___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBTree_any___rarg(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBTree_any___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_any(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
lean::dec(x_2);
lean::dec(x_1);
x_4 = 1;
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_3, 3);
lean::inc(x_7);
lean::dec(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_8 = l_RBNode_findCore___main___rarg(x_1, x_2, x_6);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
x_9 = 0;
return x_9;
}
else
{
uint8 x_10; 
lean::dec(x_8);
lean::inc(x_2);
lean::inc(x_1);
x_10 = l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(x_1, x_2, x_5);
if (x_10 == 0)
{
uint8 x_11; 
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_1);
x_11 = 0;
return x_11;
}
else
{
uint8 x_12; 
x_3 = x_7;
goto _start;
}
}
}
}
}
obj* l_RBNode_all___main___at_RBTree_subset___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_all___main___at_RBTree_subset___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
uint8 l_RBTree_subset___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(x_1, x_3, x_2);
return x_4;
}
}
obj* l_RBTree_subset(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_subset___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBNode_all___main___at_RBTree_subset___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_RBTree_subset___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_RBTree_subset___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_RBTree_seteq___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
lean::inc(x_2);
lean::inc(x_3);
lean::inc(x_1);
x_4 = l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(x_1, x_3, x_2);
if (x_4 == 0)
{
uint8 x_5; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(x_1, x_2, x_3);
return x_6;
}
}
}
obj* l_RBTree_seteq(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_seteq___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBTree_seteq___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_RBTree_seteq___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_rbtreeOf___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_fromList___rarg(x_1, x_2);
return x_3;
}
}
obj* l_rbtreeOf(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtreeOf___rarg), 2, 0);
return x_2;
}
}
obj* initialize_init_data_rbmap_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_rbtree_basic(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_rbmap_basic(w);
if (io_result_is_error(w)) return w;
l_RBTree_HasRepr___rarg___closed__1 = _init_l_RBTree_HasRepr___rarg___closed__1();
lean::mark_persistent(l_RBTree_HasRepr___rarg___closed__1);
return w;
}
