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
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_RBTree_HasEmptyc___boxed(obj*, obj*);
obj* l_RBNode_any___main___at_RBTree_any___spec__1(obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___boxed(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBTree_find___boxed(obj*);
obj* l_RBNode_revFold___main___at_RBTree_revFold___spec__1___boxed(obj*, obj*);
obj* l_RBNode_findCore___main___rarg(obj*, obj*, obj*);
obj* l_rbtreeOf___boxed(obj*);
obj* l_rbtreeOf(obj*);
obj* l_List_foldl___main___at_RBTree_fromList___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBTree_max___boxed(obj*, obj*);
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
obj* l_RBTree_depth___rarg___boxed(obj*, obj*);
obj* l_RBTree_fromList___rarg(obj*, obj*);
obj* l_RBNode_min___main___rarg(obj*);
obj* l_RBNode_ins___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_RBNode_max___main___rarg(obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBTree_contains___boxed(obj*);
obj* l_RBTree_toList___rarg(obj*);
obj* l_RBTree_HasRepr___boxed(obj*, obj*);
obj* l_RBNode_depth___main___rarg(obj*, obj*);
obj* l_RBNode_revFold___main___at_RBTree_toList___spec__1(obj*);
uint8 l_RBTree_any___rarg(obj*, obj*);
obj* l_RBTree_HasRepr___rarg___closed__1;
obj* l_RBTree_depth___boxed(obj*, obj*);
obj* l_RBTree_depth___rarg(obj*, obj*);
obj* l_RBTree_find(obj*);
obj* l_RBTree_find___rarg(obj*, obj*, obj*);
uint8 l_RBTree_contains___rarg(obj*, obj*, obj*);
obj* l_RBTree_revFold___rarg(obj*, obj*, obj*);
obj* l_mkRBTree(obj*, obj*);
obj* l_RBTree_min(obj*, obj*);
uint8 l_RBNode_any___main___at_RBTree_any___spec__1___rarg(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_RBTree_contains___rarg___boxed(obj*, obj*, obj*);
uint8 l_RBTree_seteq___rarg(obj*, obj*, obj*);
obj* l_RBTree_fromList(obj*);
obj* l_RBTree_fromList___boxed(obj*);
obj* l_RBTree_seteq(obj*);
obj* l_RBNode_all___main___at_RBTree_subset___spec__1___boxed(obj*);
obj* l_RBTree_HasEmptyc(obj*, obj*);
obj* l_RBTree_revFold___boxed(obj*, obj*, obj*);
obj* l_RBTree_isEmpty(obj*, obj*);
obj* l_RBTree_mfold___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_revFold___main___at_RBTree_revFold___spec__1(obj*, obj*);
obj* l_RBTree_mfor___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___boxed(obj*, obj*, obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_RBTree_HasRepr(obj*, obj*);
uint8 l_RBNode_all___main___at_RBTree_all___spec__1___rarg(obj*, obj*);
obj* l_RBTree_revFold(obj*, obj*, obj*);
obj* l_RBTree_subset(obj*);
obj* l_RBTree_subset___boxed(obj*);
obj* l_RBTree_any___boxed(obj*, obj*);
obj* l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBTree_any(obj*, obj*);
obj* l_RBNode_all___main___at_RBTree_all___spec__1(obj*);
obj* l_RBNode_any___main___at_RBTree_any___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBTree_subset___rarg___boxed(obj*, obj*, obj*);
obj* l_RBTree_mfold(obj*, obj*, obj*, obj*);
obj* l_RBNode_fold___main___at_RBTree_fold___spec__1___boxed(obj*, obj*);
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
obj* l_RBNode_any___main___at_RBTree_any___spec__1___boxed(obj*);
uint8 l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBTree_ofList___main___rarg(obj*, obj*);
obj* l_RBTree_isEmpty___boxed(obj*, obj*);
obj* l_RBTree_max___rarg(obj*);
obj* l_RBTree_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_RBTree_insert(obj*);
obj* l_RBNode_all___main___at_RBTree_subset___spec__1(obj*);
obj* l_RBNode_revFold___main___at_RBTree_toList___spec__1___boxed(obj*);
uint8 l_RBTree_isEmpty___rarg(obj*);
obj* l_RBTree_ofList(obj*);
obj* l_RBTree_ofList___main___boxed(obj*);
obj* l_RBTree_depth(obj*, obj*);
obj* l_RBTree_fold___boxed(obj*, obj*, obj*);
obj* l_RBTree_toList___boxed(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBTree_ofList___rarg(obj*, obj*);
obj* l_RBTree_ofList___boxed(obj*);
obj* l_RBTree_mfor___rarg(obj*, obj*, obj*);
obj* l_RBTree_insert___boxed(obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBTree_all(obj*, obj*);
obj* l_List_foldl___main___at_RBTree_fromList___spec__1___boxed(obj*);
obj* l_List_repr___main___rarg(obj*, obj*);
obj* l_RBTree_max(obj*, obj*);
obj* l_RBNode_all___main___at_RBTree_all___spec__1___boxed(obj*);
obj* l_RBTree_seteq___boxed(obj*);
obj* l_mkRBTree(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_mkRBTree___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mkRBTree(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_HasEmptyc(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_RBTree_HasEmptyc___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_HasEmptyc(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_depth___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_depth___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBTree_depth(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_depth___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBTree_depth___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_depth___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_depth___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_depth(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_12; obj* x_14; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 3);
lean::inc(x_8);
lean::dec(x_2);
lean::inc(x_0);
x_12 = l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg(x_0, x_1, x_4);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_12, x_6);
x_1 = x_14;
x_2 = x_8;
goto _start;
}
}
}
obj* l_RBNode_fold___main___at_RBTree_fold___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_RBTree_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBTree_fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_fold___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_fold___main___at_RBTree_fold___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_fold___main___at_RBTree_fold___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_fold___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_fold(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_12; obj* x_14; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 3);
lean::inc(x_8);
lean::dec(x_2);
lean::inc(x_0);
x_12 = l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg(x_0, x_1, x_8);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_12, x_6);
x_1 = x_14;
x_2 = x_4;
goto _start;
}
}
}
obj* l_RBNode_revFold___main___at_RBTree_revFold___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_RBTree_revFold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBTree_revFold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_revFold___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_revFold___main___at_RBTree_revFold___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_revFold___main___at_RBTree_revFold___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_revFold___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_revFold(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(x_0, x_1, x_3, x_2);
return x_4;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_0);
x_7 = lean::apply_2(x_0, x_5, x_1);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_2);
lean::closure_set(x_8, 1, x_0);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_8; obj* x_11; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_2(x_8, lean::box(0), x_2);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_23; obj* x_25; obj* x_26; 
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_3, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_3, 3);
lean::inc(x_16);
lean::dec(x_3);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::inc(x_1);
lean::inc(x_0);
x_23 = l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(x_0, x_1, x_2, x_12);
lean::inc(x_19);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__2), 6, 5);
lean::closure_set(x_25, 0, x_1);
lean::closure_set(x_25, 1, x_14);
lean::closure_set(x_25, 2, x_0);
lean::closure_set(x_25, 3, x_16);
lean::closure_set(x_25, 4, x_19);
x_26 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_23, x_25);
return x_26;
}
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_RBTree_mfold___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBTree_mfold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_mfold___rarg), 4, 0);
return x_4;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_mfold___main___at_RBTree_mfold___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBTree_mfold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBTree_mfold(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(x_0, x_1, x_3, x_2);
return x_4;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_6, 4);
lean::inc(x_8);
lean::inc(x_1);
x_11 = lean::apply_1(x_1, x_2);
x_12 = lean::cnstr_get(x_6, 1);
lean::inc(x_12);
lean::dec(x_6);
x_15 = lean::box(0);
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
x_17 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_11, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__1), 4, 3);
lean::closure_set(x_18, 0, x_0);
lean::closure_set(x_18, 1, x_1);
lean::closure_set(x_18, 2, x_3);
x_19 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_8; obj* x_11; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_2(x_8, lean::box(0), x_2);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_23; obj* x_25; obj* x_26; 
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_3, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_3, 3);
lean::inc(x_16);
lean::dec(x_3);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::inc(x_1);
lean::inc(x_0);
x_23 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(x_0, x_1, x_2, x_12);
lean::inc(x_19);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2___boxed), 6, 5);
lean::closure_set(x_25, 0, x_0);
lean::closure_set(x_25, 1, x_1);
lean::closure_set(x_25, 2, x_14);
lean::closure_set(x_25, 3, x_16);
lean::closure_set(x_25, 4, x_19);
x_26 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_23, x_25);
return x_26;
}
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg), 4, 0);
return x_3;
}
}
obj* l_RBTree_mfor___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(x_0, x_1, x_3, x_2);
return x_4;
}
}
obj* l_RBTree_mfor(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_mfor___rarg), 3, 0);
return x_4;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBTree_mfor___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBTree_mfor(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
uint8 l_RBTree_isEmpty___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
}
}
obj* l_RBTree_isEmpty(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_isEmpty___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_RBTree_isEmpty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_RBTree_isEmpty___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBTree_isEmpty___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_isEmpty(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 3);
lean::inc(x_6);
lean::dec(x_1);
x_9 = l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(x_0, x_6);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
x_0 = x_10;
x_1 = x_2;
goto _start;
}
}
}
obj* l_RBNode_revFold___main___at_RBTree_toList___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg), 2, 0);
return x_1;
}
}
obj* l_RBTree_toList___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(x_1, x_0);
return x_2;
}
}
obj* l_RBTree_toList(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_toList___rarg), 1, 0);
return x_2;
}
}
obj* l_RBNode_revFold___main___at_RBTree_toList___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_revFold___main___at_RBTree_toList___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBTree_toList___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_toList(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_min___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_min___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
if (lean::is_scalar(x_5)) {
 x_9 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_9 = x_5;
}
lean::cnstr_set(x_9, 0, x_6);
return x_9;
}
}
}
obj* l_RBTree_min(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_min___rarg), 1, 0);
return x_2;
}
}
obj* l_RBTree_min___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_min(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_max___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_max___main___rarg(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
if (lean::is_scalar(x_5)) {
 x_9 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_9 = x_5;
}
lean::cnstr_set(x_9, 0, x_6);
return x_9;
}
}
}
obj* l_RBTree_max(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_max___rarg), 1, 0);
return x_2;
}
}
obj* l_RBTree_max___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_max(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_RBTree_HasRepr___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("rbtreeOf ");
return x_0;
}
}
obj* l_RBTree_HasRepr___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_RBTree_toList___rarg(x_1);
x_3 = l_List_repr___main___rarg(x_0, x_2);
x_4 = l_RBTree_HasRepr___rarg___closed__1;
x_5 = lean::string_append(x_4, x_3);
lean::dec(x_3);
return x_5;
}
}
obj* l_RBTree_HasRepr(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_HasRepr___rarg), 2, 0);
return x_2;
}
}
obj* l_RBTree_HasRepr___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_HasRepr(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_insert___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_isRed___main___rarg(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_RBNode_ins___main___rarg(x_0, x_1, x_2, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::box(0);
x_7 = l_RBNode_ins___main___rarg(x_0, x_1, x_2, x_6);
x_8 = l_RBNode_setBlack___main___rarg(x_7);
return x_8;
}
}
}
obj* l_RBTree_insert(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_insert___rarg), 3, 0);
return x_1;
}
}
obj* l_RBTree_insert___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBTree_insert(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBTree_ofList___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_10; uint8 x_11; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
lean::inc(x_0);
x_10 = l_RBTree_ofList___main___rarg(x_0, x_6);
x_11 = l_RBNode_isRed___main___rarg(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::box(0);
x_13 = l_RBNode_ins___main___rarg(x_0, x_10, x_4, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::box(0);
x_15 = l_RBNode_ins___main___rarg(x_0, x_10, x_4, x_14);
x_16 = l_RBNode_setBlack___main___rarg(x_15);
return x_16;
}
}
}
}
obj* l_RBTree_ofList___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_ofList___main___rarg), 2, 0);
return x_1;
}
}
obj* l_RBTree_ofList___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBTree_ofList___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBTree_ofList___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_ofList___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBTree_ofList(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_ofList___rarg), 2, 0);
return x_1;
}
}
obj* l_RBTree_ofList___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBTree_ofList(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBTree_find___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___rarg(x_0, x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_8; obj* x_11; 
x_5 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_7 = x_3;
} else {
 lean::inc(x_5);
 lean::dec(x_3);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_7;
}
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
}
}
obj* l_RBTree_find(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_find___rarg), 3, 0);
return x_1;
}
}
obj* l_RBTree_find___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBTree_find(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_RBTree_contains___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___rarg(x_0, x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_6; 
lean::dec(x_3);
x_6 = 1;
return x_6;
}
}
}
obj* l_RBTree_contains(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_contains___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_RBTree_contains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBTree_contains___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBTree_contains___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBTree_contains(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_foldl___main___at_RBTree_fromList___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; uint8 x_9; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = l_RBNode_isRed___main___rarg(x_1);
if (x_9 == 0)
{
obj* x_10; obj* x_12; 
x_10 = lean::box(0);
lean::inc(x_0);
x_12 = l_RBNode_ins___main___rarg(x_0, x_1, x_4, x_10);
x_1 = x_12;
x_2 = x_6;
goto _start;
}
else
{
obj* x_14; obj* x_16; obj* x_17; 
x_14 = lean::box(0);
lean::inc(x_0);
x_16 = l_RBNode_ins___main___rarg(x_0, x_1, x_4, x_14);
x_17 = l_RBNode_setBlack___main___rarg(x_16);
x_1 = x_17;
x_2 = x_6;
goto _start;
}
}
}
}
obj* l_List_foldl___main___at_RBTree_fromList___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_RBTree_fromList___spec__1___rarg), 3, 0);
return x_1;
}
}
obj* l_RBTree_fromList___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_List_foldl___main___at_RBTree_fromList___spec__1___rarg(x_1, x_2, x_0);
return x_3;
}
}
obj* l_RBTree_fromList(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_fromList___rarg), 2, 0);
return x_1;
}
}
obj* l_List_foldl___main___at_RBTree_fromList___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_foldl___main___at_RBTree_fromList___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBTree_fromList___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBTree_fromList(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_RBNode_all___main___at_RBTree_all___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; 
lean::dec(x_0);
x_3 = 1;
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_12; uint8 x_13; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_1(x_0, x_6);
x_13 = lean::unbox(x_12);
if (x_13 == 0)
{
uint8 x_17; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_4);
x_17 = 0;
return x_17;
}
else
{
uint8 x_19; 
lean::inc(x_0);
x_19 = l_RBNode_all___main___at_RBTree_all___spec__1___rarg(x_0, x_4);
if (x_19 == 0)
{
uint8 x_22; 
lean::dec(x_8);
lean::dec(x_0);
x_22 = 0;
return x_22;
}
else
{
x_1 = x_8;
goto _start;
}
}
}
}
}
obj* l_RBNode_all___main___at_RBTree_all___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_all___main___at_RBTree_all___spec__1___rarg___boxed), 2, 0);
return x_1;
}
}
uint8 l_RBTree_all___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_RBNode_all___main___at_RBTree_all___spec__1___rarg(x_1, x_0);
return x_2;
}
}
obj* l_RBTree_all(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_all___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_all___main___at_RBTree_all___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBNode_all___main___at_RBTree_all___spec__1___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBNode_all___main___at_RBTree_all___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_all___main___at_RBTree_all___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBTree_all___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBTree_all___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBTree_all___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_all(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBNode_any___main___at_RBTree_any___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; 
lean::dec(x_0);
x_3 = 0;
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_12; uint8 x_13; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = lean::apply_1(x_0, x_6);
x_13 = lean::unbox(x_12);
if (x_13 == 0)
{
uint8 x_15; 
lean::inc(x_0);
x_15 = l_RBNode_any___main___at_RBTree_any___spec__1___rarg(x_0, x_4);
if (x_15 == 0)
{
x_1 = x_8;
goto _start;
}
else
{
uint8 x_19; 
lean::dec(x_8);
lean::dec(x_0);
x_19 = 1;
return x_19;
}
}
else
{
uint8 x_23; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_4);
x_23 = 1;
return x_23;
}
}
}
}
obj* l_RBNode_any___main___at_RBTree_any___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_any___main___at_RBTree_any___spec__1___rarg___boxed), 2, 0);
return x_1;
}
}
uint8 l_RBTree_any___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_RBNode_any___main___at_RBTree_any___spec__1___rarg(x_1, x_0);
return x_2;
}
}
obj* l_RBTree_any(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_any___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_any___main___at_RBTree_any___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBNode_any___main___at_RBTree_any___spec__1___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBNode_any___main___at_RBTree_any___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_any___main___at_RBTree_any___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBTree_any___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBTree_any___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBTree_any___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_any(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = 1;
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_15; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 3);
lean::inc(x_10);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_15 = l_RBNode_findCore___main___rarg(x_0, x_1, x_8);
if (lean::obj_tag(x_15) == 0)
{
uint8 x_20; 
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_6);
x_20 = 0;
return x_20;
}
else
{
uint8 x_24; 
lean::dec(x_15);
lean::inc(x_1);
lean::inc(x_0);
x_24 = l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(x_0, x_1, x_6);
if (x_24 == 0)
{
uint8 x_28; 
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_0);
x_28 = 0;
return x_28;
}
else
{
x_2 = x_10;
goto _start;
}
}
}
}
}
obj* l_RBNode_all___main___at_RBTree_subset___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_all___main___at_RBTree_subset___spec__1___rarg___boxed), 3, 0);
return x_1;
}
}
uint8 l_RBTree_subset___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_RBTree_subset(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_subset___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_RBNode_all___main___at_RBTree_subset___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBNode_all___main___at_RBTree_subset___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_all___main___at_RBTree_subset___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBTree_subset___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBTree_subset___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBTree_subset___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBTree_subset(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_RBTree_seteq___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_6; 
lean::inc(x_1);
lean::inc(x_2);
lean::inc(x_0);
x_6 = l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(x_0, x_2, x_1);
if (x_6 == 0)
{
uint8 x_10; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_10 = 0;
return x_10;
}
else
{
uint8 x_11; 
x_11 = l_RBNode_all___main___at_RBTree_subset___spec__1___rarg(x_0, x_1, x_2);
return x_11;
}
}
}
obj* l_RBTree_seteq(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_seteq___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_RBTree_seteq___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBTree_seteq___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBTree_seteq___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBTree_seteq(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbtreeOf___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_fromList___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbtreeOf(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtreeOf___rarg), 2, 0);
return x_1;
}
}
obj* l_rbtreeOf___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbtreeOf(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* initialize_init_data_rbmap_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_rbtree_basic(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_rbmap_basic(w);
 l_RBTree_HasRepr___rarg___closed__1 = _init_l_RBTree_HasRepr___rarg___closed__1();
lean::mark_persistent(l_RBTree_HasRepr___rarg___closed__1);
return w;
}
