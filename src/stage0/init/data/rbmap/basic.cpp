// Lean compiler output
// Module: init.data.rbmap.basic
// Imports: init.data.repr init.data.option.basic
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
obj* l_RBNode_depth___rarg(obj*, obj*);
obj* l_RBNode_min___boxed(obj*, obj*);
obj* l_RBNode_max___main___boxed(obj*, obj*);
obj* l_List_repr___at_RBMap_HasRepr___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBNode_balance1(obj*, obj*);
obj* l_RBNode_del___main___rarg(obj*, obj*, obj*);
obj* l_RBNode_find(obj*);
obj* l_RBNode_depth___main___rarg___boxed(obj*, obj*);
obj* l_RBNode_appendTrees___main___boxed(obj*, obj*);
obj* l_RBNode_ins___main___boxed(obj*, obj*);
obj* l_RBMap_contains(obj*, obj*);
obj* l_RBNode_findCore(obj*, obj*);
obj* l_RBNode_balRight___boxed(obj*, obj*);
obj* l_RBMap_revFold___rarg(obj*, obj*, obj*);
obj* l_RBNode_lowerBound(obj*, obj*);
obj* l_RBNode_revFold___rarg(obj*, obj*, obj*);
obj* l_RBNode_findCore___main___rarg(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_appendTrees___rarg(obj*, obj*);
obj* l_RBNode_findCore___main___boxed(obj*, obj*);
obj* l_RBMap_find___rarg(obj*, obj*, obj*);
obj* l_RBMap_maxDepth(obj*, obj*, obj*);
obj* l_RBNode_insert___boxed(obj*, obj*);
obj* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBNode_setBlack(obj*, obj*);
obj* l_List_foldl___main___at_rbmapOf___spec__1(obj*, obj*);
obj* l_RBNode_isRed___boxed(obj*, obj*);
obj* l_RBNode_balRight___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main(obj*, obj*);
obj* l_RBMap_ofList(obj*, obj*);
extern obj* l_List_repr___rarg___closed__3;
obj* l_RBNode_find___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_min(obj*, obj*, obj*);
obj* l_RBMap_toList___rarg(obj*);
obj* l_RBNode_appendTrees___boxed(obj*, obj*);
obj* l_RBMap_depth___rarg___boxed(obj*, obj*);
obj* l_RBNode_isRed___rarg___boxed(obj*);
uint8 l_RBNode_all___rarg(obj*, obj*);
obj* l_RBNode_balance2(obj*, obj*);
obj* l_RBMap_findCore___rarg(obj*, obj*, obj*);
obj* l_RBNode_lowerBound___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_min___rarg(obj*);
obj* l_RBNode_del___main___boxed(obj*, obj*);
obj* l_RBNode_max___main___rarg___boxed(obj*);
obj* l_RBNode_min___main___rarg___boxed(obj*);
uint8 l_RBNode_any___main___rarg(obj*, obj*);
obj* l_RBMap_findCore(obj*, obj*);
obj* l_RBNode_lowerBound___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmapOf___rarg(obj*, obj*);
obj* l_RBNode_any___main(obj*, obj*);
obj* l_RBNode_mfold___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_revFold___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_erase___rarg(obj*, obj*, obj*);
obj* l_List_foldl___main___at_rbmapOf___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbmapOf(obj*, obj*);
obj* l_RBMap_erase___rarg(obj*, obj*, obj*);
obj* l_RBNode_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_revFold___main___at_RBMap_toList___spec__1(obj*, obj*);
obj* l_RBMap_toList___boxed(obj*, obj*, obj*);
obj* l_RBNode_min___main___rarg(obj*);
obj* l_RBMap_mfold(obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_max___rarg___boxed(obj*);
obj* l_RBNode_ins___boxed(obj*, obj*);
obj* l_RBMap_size(obj*, obj*, obj*);
obj* l_RBMap_mfor(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_lowerBound___main(obj*, obj*);
obj* l_RBNode_max___main___rarg(obj*);
obj* l_RBNode_isBlack___boxed(obj*, obj*);
obj* l_RBMap_all___boxed(obj*, obj*, obj*);
obj* l_RBNode_any(obj*, obj*);
obj* l_RBMap_depth(obj*, obj*, obj*);
obj* l_RBNode_max(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1(obj*, obj*, obj*, obj*);
obj* l_RBNode_isBlack___rarg___boxed(obj*);
obj* l_RBMap_empty___boxed(obj*, obj*, obj*);
obj* l_RBNode_fold___main___at_RBMap_size___spec__1(obj*, obj*);
obj* l_RBNode_mfold___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_isRed(obj*, obj*);
obj* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(obj*, obj*);
obj* l_RBNode_fold___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_min___rarg(obj*);
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(obj*, obj*, uint8, obj*);
obj* l_RBMap_fold___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_depth___boxed(obj*, obj*, obj*);
obj* l_RBNode_depth___main___rarg(obj*, obj*);
obj* l_RBNode_revFold___main___at_RBMap_toList___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_lowerBound(obj*, obj*);
obj* l_RBNode_lowerBound___main___boxed(obj*, obj*);
obj* l_RBNode_del___main(obj*, obj*);
obj* l_RBMap_isEmpty(obj*, obj*, obj*);
obj* l_RBNode_setBlack___boxed(obj*, obj*);
obj* l_RBMap_mfor___rarg(obj*, obj*, obj*);
obj* l_mkRBMap___boxed(obj*, obj*, obj*);
obj* l_RBNode_appendTrees(obj*, obj*);
obj* l_RBMap_maxDepth___rarg(obj*);
extern obj* l_List_repr___rarg___closed__2;
obj* l_RBNode_balRight(obj*, obj*);
obj* l_RBMap_ofList___main___rarg(obj*, obj*);
obj* l_RBMap_min___rarg___boxed(obj*);
obj* l_RBNode_all___main___rarg___boxed(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_singleton(obj*, obj*);
obj* l_RBMap_ofList___rarg(obj*, obj*);
obj* l_RBNode_balance_u2083___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_findCore___boxed(obj*, obj*);
obj* l_RBNode_balance2___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_mfold___rarg(obj*, obj*, obj*, obj*);
obj* lean_string_append(obj*, obj*);
obj* l_RBMap_contains___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_fold___rarg(obj*, obj*, obj*);
obj* l_RBNode_appendTrees___main(obj*, obj*);
extern obj* l_List_reprAux___main___rarg___closed__1;
obj* l_RBNode_insert(obj*, obj*);
uint8 l_RBNode_isRed___rarg(obj*);
obj* l_RBMap_HasRepr(obj*, obj*, obj*);
obj* l_RBMap_min___boxed(obj*, obj*, obj*);
extern obj* l_Option_HasRepr___rarg___closed__3;
obj* l_RBMap_fold___rarg(obj*, obj*, obj*);
obj* l_RBMap_toList___rarg___boxed(obj*);
obj* l_RBMap_mfor___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_HasRepr___rarg___closed__1;
obj* l_RBMap_max(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_all___boxed(obj*, obj*);
obj* l_RBNode_find___main(obj*);
obj* l_RBNode_del___rarg(obj*, obj*, obj*);
obj* l_RBNode_singleton___rarg(obj*, obj*);
obj* l_RBNode_revFold___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_appendTrees___main___rarg(obj*, obj*);
obj* l_RBMap_maxDepth___rarg___boxed(obj*);
obj* l_RBNode_revFold___main___at_RBMap_toList___spec__1___rarg(obj*, obj*);
obj* l_RBNode_max___boxed(obj*, obj*);
obj* lean_nat_add(obj*, obj*);
obj* l_RBNode_del___boxed(obj*, obj*);
obj* l_RBMap_HasEmptyc___boxed(obj*, obj*, obj*);
obj* l_RBMap_HasRepr___rarg___boxed(obj*, obj*, obj*);
obj* l_RBMap_maxDepth___rarg___closed__1;
obj* l_RBMap_HasRepr___rarg(obj*, obj*, obj*);
extern obj* l_Prod_HasRepr___rarg___closed__1;
obj* l_RBNode_balLeft(obj*, obj*);
obj* l_RBMap_find(obj*, obj*);
obj* l_RBNode_fold___main___rarg(obj*, obj*, obj*);
obj* l_RBMap_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins(obj*, obj*);
obj* l_RBNode_erase___boxed(obj*, obj*);
obj* l_RBMap_depth___rarg(obj*, obj*);
uint8 l_RBNode_all___main___rarg(obj*, obj*);
uint8 l_RBNode_any___rarg(obj*, obj*);
obj* l_RBMap_toList(obj*, obj*, obj*);
obj* l_RBNode_all(obj*, obj*);
obj* l_RBNode_mfold___main(obj*, obj*, obj*, obj*);
uint8 l_RBNode_isBlack___rarg(obj*);
obj* l_RBNode_any___main___rarg___boxed(obj*, obj*);
obj* l_RBNode_all___main(obj*, obj*);
obj* l_RBMap_empty(obj*, obj*, obj*);
obj* l_RBNode_max___rarg(obj*);
obj* l_RBNode_depth___rarg___boxed(obj*, obj*);
obj* l_RBNode_balance2___boxed(obj*, obj*);
obj* l_RBNode_all___rarg___boxed(obj*, obj*);
obj* l_RBNode_depth___main(obj*, obj*);
obj* l_RBNode_mfold___main___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_balLeft___boxed(obj*, obj*);
obj* l_RBNode_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_min(obj*, obj*);
obj* l_RBNode_min___main(obj*, obj*);
obj* l_RBNode_any___main___boxed(obj*, obj*);
obj* l_RBMap_fold(obj*, obj*, obj*, obj*);
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_singleton___boxed(obj*, obj*);
obj* l_RBNode_any___boxed(obj*, obj*);
obj* l_RBMap_any___boxed(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*);
uint8 l_RBMap_all___rarg(obj*, obj*);
obj* l_List_repr___at_RBMap_HasRepr___spec__1(obj*, obj*);
obj* l_RBMap_any___rarg___boxed(obj*, obj*);
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2(obj*, obj*);
obj* l_RBMap_insert(obj*, obj*);
obj* l_RBMap_revFold(obj*, obj*, obj*, obj*);
obj* l_RBNode_revFold___main(obj*, obj*, obj*);
obj* l_List_foldl___main___at_RBMap_fromList___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_erase(obj*, obj*);
obj* l_RBMap_isEmpty___boxed(obj*, obj*, obj*);
obj* l_RBNode_balance1___boxed(obj*, obj*);
obj* l_RBNode_depth___main___boxed(obj*, obj*);
obj* l_RBNode_isBlack(obj*, obj*);
obj* l_RBMap_size___rarg___boxed(obj*);
obj* l_RBMap_fromList(obj*, obj*);
obj* l_RBNode_any___rarg___boxed(obj*, obj*);
obj* l_RBNode_max___main(obj*, obj*);
obj* l_RBNode_setBlack___rarg(obj*);
obj* l_RBMap_lowerBound___rarg(obj*, obj*, obj*);
obj* l_RBMap_HasEmptyc(obj*, obj*, obj*);
obj* l_RBNode_max___rarg___boxed(obj*);
obj* l_RBNode_balLeft___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_min___main___boxed(obj*, obj*);
obj* l_RBNode_balance_u2083___boxed(obj*, obj*);
obj* l_RBNode_depth___boxed(obj*, obj*);
obj* l_RBNode_min___rarg___boxed(obj*);
obj* l_RBMap_isEmpty___rarg___boxed(obj*);
obj* l_RBNode_revFold___main___rarg(obj*, obj*, obj*);
obj* l_mkRBMap(obj*, obj*, obj*);
obj* l_RBMap_all(obj*, obj*, obj*);
obj* l_RBMap_ofList___main(obj*, obj*);
obj* l_RBNode_findCore___main(obj*, obj*);
obj* l_RBNode_lowerBound___boxed(obj*, obj*);
obj* l_RBMap_fromList___rarg(obj*, obj*);
obj* l_RBNode_ins___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_all___rarg___boxed(obj*, obj*);
obj* l_RBNode_setRed___rarg(obj*);
obj* l_RBNode_fold___boxed(obj*, obj*, obj*);
obj* l_RBMap_size___rarg(obj*);
obj* l_RBNode_fold___main(obj*, obj*, obj*);
obj* l_Nat_max___boxed(obj*, obj*);
obj* l_RBMap_maxDepth___boxed(obj*, obj*, obj*);
obj* l_RBNode_fold(obj*, obj*, obj*);
obj* l_RBNode_depth(obj*, obj*);
obj* l_RBNode_all___main___boxed(obj*, obj*);
obj* l_RBNode_mfold(obj*, obj*, obj*, obj*);
obj* l_RBNode_balance1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_del(obj*, obj*);
obj* l_RBNode_setRed___boxed(obj*, obj*);
uint8 l_RBMap_any___rarg(obj*, obj*);
obj* l_RBMap_size___boxed(obj*, obj*, obj*);
obj* l_RBMap_any(obj*, obj*, obj*);
obj* l_RBNode_setRed(obj*, obj*);
obj* l_RBNode_balance_u2083(obj*, obj*);
obj* l_RBMap_HasRepr___boxed(obj*, obj*, obj*);
obj* l_RBNode_findCore___rarg(obj*, obj*, obj*);
obj* l_RBMap_max___rarg(obj*);
uint8 l_RBMap_isEmpty___rarg(obj*);
extern obj* l_List_repr___rarg___closed__1;
obj* l_List_foldl___main___at_RBMap_fromList___spec__1(obj*, obj*);
obj* l_RBNode_mfold___main___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_RBNode_revFold(obj*, obj*, obj*);
uint8 l_RBMap_contains___rarg(obj*, obj*, obj*);
obj* l_RBNode_revFold___boxed(obj*, obj*, obj*);
obj* l_RBMap_mfold___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_RBMap_max___boxed(obj*, obj*, obj*);
obj* l_RBMap_erase(obj*, obj*);
obj* l_RBNode_depth___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::mk_nat_obj(0u);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 3);
lean::inc(x_1);
x_6 = l_RBNode_depth___main___rarg(x_1, x_4);
lean::inc(x_1);
x_7 = l_RBNode_depth___main___rarg(x_1, x_5);
x_8 = lean::apply_2(x_1, x_6, x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean_nat_add(x_8, x_9);
lean::dec(x_8);
return x_10;
}
}
}
obj* l_RBNode_depth___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_depth___main___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBNode_depth___main___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_depth___main___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_depth___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_depth___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_depth___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_depth___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_RBNode_depth(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_depth___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBNode_depth___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_depth___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_depth___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_depth(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_min___main___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
x_1 = x_3;
goto _start;
}
}
}
}
obj* l_RBNode_min___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_min___main___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_RBNode_min___main___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_min___main___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_min___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_min___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_min___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_min___main___rarg(x_1);
return x_2;
}
}
obj* l_RBNode_min(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_min___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_RBNode_min___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_min___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_min___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_min(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_max___main___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_1, 2);
lean::inc(x_5);
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
else
{
x_1 = x_3;
goto _start;
}
}
}
}
obj* l_RBNode_max___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_max___main___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_RBNode_max___main___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_max___main___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_max___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_max___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_max___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_max___main___rarg(x_1);
return x_2;
}
}
obj* l_RBNode_max(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_max___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_RBNode_max___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_max___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_max___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_max(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_fold___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_3, 3);
lean::inc(x_7);
lean::dec(x_3);
lean::inc(x_1);
x_8 = l_RBNode_fold___main___rarg(x_1, x_2, x_4);
lean::inc(x_1);
x_9 = lean::apply_3(x_1, x_8, x_5, x_6);
x_2 = x_9;
x_3 = x_7;
goto _start;
}
}
}
obj* l_RBNode_fold___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_fold___main___rarg), 3, 0);
return x_4;
}
}
obj* l_RBNode_fold___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_fold___main(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_RBNode_fold___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_fold___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBNode_fold(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_fold___rarg), 3, 0);
return x_4;
}
}
obj* l_RBNode_fold___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_fold(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_RBNode_mfold___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBNode_mfold___main___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_RBNode_mfold___main___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_1);
x_8 = lean::apply_3(x_1, x_7, x_2, x_3);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___rarg___lambda__1), 4, 3);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_1);
lean::closure_set(x_9, 2, x_5);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_RBNode_mfold___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_4, 2);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_4, 3);
lean::inc(x_11);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::inc(x_2);
lean::inc(x_1);
x_13 = l_RBNode_mfold___main___rarg(x_1, x_2, x_3, x_8);
lean::inc(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___rarg___lambda__2), 7, 6);
lean::closure_set(x_14, 0, x_2);
lean::closure_set(x_14, 1, x_9);
lean::closure_set(x_14, 2, x_10);
lean::closure_set(x_14, 3, x_1);
lean::closure_set(x_14, 4, x_11);
lean::closure_set(x_14, 5, x_12);
x_15 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
}
obj* l_RBNode_mfold___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___rarg), 4, 0);
return x_5;
}
}
obj* l_RBNode_mfold___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBNode_mfold___main(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_RBNode_mfold___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBNode_mfold___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_RBNode_mfold(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___rarg), 4, 0);
return x_5;
}
}
obj* l_RBNode_mfold___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBNode_mfold(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_RBNode_revFold___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_3, 3);
lean::inc(x_7);
lean::dec(x_3);
lean::inc(x_1);
x_8 = l_RBNode_revFold___main___rarg(x_1, x_2, x_7);
lean::inc(x_1);
x_9 = lean::apply_3(x_1, x_8, x_5, x_6);
x_2 = x_9;
x_3 = x_4;
goto _start;
}
}
}
obj* l_RBNode_revFold___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_revFold___main___rarg), 3, 0);
return x_4;
}
}
obj* l_RBNode_revFold___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_revFold___main(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_RBNode_revFold___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_revFold___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBNode_revFold(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_revFold___rarg), 3, 0);
return x_4;
}
}
obj* l_RBNode_revFold___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_revFold(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
uint8 l_RBNode_all___main___rarg(obj* x_1, obj* x_2) {
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
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_2, 2);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 3);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_1);
x_8 = lean::apply_2(x_1, x_5, x_6);
x_9 = lean::unbox(x_8);
lean::dec(x_8);
if (x_9 == 0)
{
uint8 x_10; 
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_1);
x_10 = 0;
return x_10;
}
else
{
uint8 x_11; 
lean::inc(x_1);
x_11 = l_RBNode_all___main___rarg(x_1, x_4);
if (x_11 == 0)
{
uint8 x_12; 
lean::dec(x_7);
lean::dec(x_1);
x_12 = 0;
return x_12;
}
else
{
x_2 = x_7;
goto _start;
}
}
}
}
}
obj* l_RBNode_all___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_all___main___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBNode_all___main___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBNode_all___main___rarg(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBNode_all___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_all___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBNode_all___rarg(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_all___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_RBNode_all(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_all___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBNode_all___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBNode_all___rarg(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBNode_all___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_all(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBNode_any___main___rarg(obj* x_1, obj* x_2) {
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
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_2, 2);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 3);
lean::inc(x_7);
lean::dec(x_2);
lean::inc(x_1);
x_8 = lean::apply_2(x_1, x_5, x_6);
x_9 = lean::unbox(x_8);
lean::dec(x_8);
if (x_9 == 0)
{
uint8 x_10; 
lean::inc(x_1);
x_10 = l_RBNode_any___main___rarg(x_1, x_4);
if (x_10 == 0)
{
x_2 = x_7;
goto _start;
}
else
{
uint8 x_12; 
lean::dec(x_7);
lean::dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8 x_13; 
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_1);
x_13 = 1;
return x_13;
}
}
}
}
obj* l_RBNode_any___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_any___main___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBNode_any___main___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBNode_any___main___rarg(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBNode_any___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_any___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBNode_any___rarg(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_any___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_RBNode_any(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_any___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBNode_any___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBNode_any___rarg(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBNode_any___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_any(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_singleton___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; obj* x_5; 
x_3 = lean::box(0);
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 2, x_2);
lean::cnstr_set(x_5, 3, x_3);
lean::cnstr_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
}
obj* l_RBNode_singleton(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_singleton___rarg), 2, 0);
return x_3;
}
}
obj* l_RBNode_singleton___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_singleton(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_balance1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
else
{
obj* x_5; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; 
x_6 = lean::cnstr_get(x_4, 3);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_4);
if (x_7 == 0)
{
obj* x_8; obj* x_9; uint8 x_10; uint8 x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_4, 3);
lean::dec(x_8);
x_9 = lean::cnstr_get(x_4, 0);
lean::dec(x_9);
x_10 = 0;
lean::cnstr_set(x_4, 0, x_6);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_10);
x_11 = 1;
x_12 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_1);
lean::cnstr_set(x_12, 2, x_2);
lean::cnstr_set(x_12, 3, x_3);
lean::cnstr_set_uint8(x_12, sizeof(void*)*4, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_14; uint8 x_15; obj* x_16; uint8 x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_4, 1);
x_14 = lean::cnstr_get(x_4, 2);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_4);
x_15 = 0;
x_16 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_16, 0, x_6);
lean::cnstr_set(x_16, 1, x_13);
lean::cnstr_set(x_16, 2, x_14);
lean::cnstr_set(x_16, 3, x_6);
lean::cnstr_set_uint8(x_16, sizeof(void*)*4, x_15);
x_17 = 1;
x_18 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_1);
lean::cnstr_set(x_18, 2, x_2);
lean::cnstr_set(x_18, 3, x_3);
lean::cnstr_set_uint8(x_18, sizeof(void*)*4, x_17);
return x_18;
}
}
else
{
uint8 x_19; 
x_19 = lean::cnstr_get_uint8(x_6, sizeof(void*)*4);
if (x_19 == 0)
{
uint8 x_20; 
x_20 = !lean::is_exclusive(x_4);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; 
x_21 = lean::cnstr_get(x_4, 1);
x_22 = lean::cnstr_get(x_4, 2);
x_23 = lean::cnstr_get(x_4, 3);
lean::dec(x_23);
x_24 = lean::cnstr_get(x_4, 0);
lean::dec(x_24);
x_25 = !lean::is_exclusive(x_6);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; uint8 x_30; obj* x_31; 
x_26 = lean::cnstr_get(x_6, 0);
x_27 = lean::cnstr_get(x_6, 1);
x_28 = lean::cnstr_get(x_6, 2);
x_29 = lean::cnstr_get(x_6, 3);
x_30 = 1;
lean::cnstr_set(x_6, 3, x_26);
lean::cnstr_set(x_6, 2, x_22);
lean::cnstr_set(x_6, 1, x_21);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set_uint8(x_6, sizeof(void*)*4, x_30);
lean::cnstr_set(x_4, 3, x_3);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 0, x_29);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_30);
x_31 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_31, 0, x_6);
lean::cnstr_set(x_31, 1, x_27);
lean::cnstr_set(x_31, 2, x_28);
lean::cnstr_set(x_31, 3, x_4);
lean::cnstr_set_uint8(x_31, sizeof(void*)*4, x_19);
return x_31;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; uint8 x_36; obj* x_37; obj* x_38; 
x_32 = lean::cnstr_get(x_6, 0);
x_33 = lean::cnstr_get(x_6, 1);
x_34 = lean::cnstr_get(x_6, 2);
x_35 = lean::cnstr_get(x_6, 3);
lean::inc(x_35);
lean::inc(x_34);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_6);
x_36 = 1;
x_37 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_37, 0, x_5);
lean::cnstr_set(x_37, 1, x_21);
lean::cnstr_set(x_37, 2, x_22);
lean::cnstr_set(x_37, 3, x_32);
lean::cnstr_set_uint8(x_37, sizeof(void*)*4, x_36);
lean::cnstr_set(x_4, 3, x_3);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 0, x_35);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_36);
x_38 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_33);
lean::cnstr_set(x_38, 2, x_34);
lean::cnstr_set(x_38, 3, x_4);
lean::cnstr_set_uint8(x_38, sizeof(void*)*4, x_19);
return x_38;
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_4, 1);
x_40 = lean::cnstr_get(x_4, 2);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_4);
x_41 = lean::cnstr_get(x_6, 0);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_6, 1);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_6, 2);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_6, 3);
lean::inc(x_44);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 lean::cnstr_release(x_6, 3);
 x_45 = x_6;
} else {
 lean::dec_ref(x_6);
 x_45 = lean::box(0);
}
x_46 = 1;
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_5);
lean::cnstr_set(x_47, 1, x_39);
lean::cnstr_set(x_47, 2, x_40);
lean::cnstr_set(x_47, 3, x_41);
lean::cnstr_set_uint8(x_47, sizeof(void*)*4, x_46);
x_48 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_48, 0, x_44);
lean::cnstr_set(x_48, 1, x_1);
lean::cnstr_set(x_48, 2, x_2);
lean::cnstr_set(x_48, 3, x_3);
lean::cnstr_set_uint8(x_48, sizeof(void*)*4, x_46);
x_49 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_42);
lean::cnstr_set(x_49, 2, x_43);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_uint8(x_49, sizeof(void*)*4, x_19);
return x_49;
}
}
else
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_4);
if (x_50 == 0)
{
obj* x_51; obj* x_52; uint8 x_53; obj* x_54; 
x_51 = lean::cnstr_get(x_4, 3);
lean::dec(x_51);
x_52 = lean::cnstr_get(x_4, 0);
lean::dec(x_52);
x_53 = 0;
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_53);
x_54 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_54, 0, x_4);
lean::cnstr_set(x_54, 1, x_1);
lean::cnstr_set(x_54, 2, x_2);
lean::cnstr_set(x_54, 3, x_3);
lean::cnstr_set_uint8(x_54, sizeof(void*)*4, x_19);
return x_54;
}
else
{
obj* x_55; obj* x_56; uint8 x_57; obj* x_58; obj* x_59; 
x_55 = lean::cnstr_get(x_4, 1);
x_56 = lean::cnstr_get(x_4, 2);
lean::inc(x_56);
lean::inc(x_55);
lean::dec(x_4);
x_57 = 0;
x_58 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_58, 0, x_5);
lean::cnstr_set(x_58, 1, x_55);
lean::cnstr_set(x_58, 2, x_56);
lean::cnstr_set(x_58, 3, x_6);
lean::cnstr_set_uint8(x_58, sizeof(void*)*4, x_57);
x_59 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_1);
lean::cnstr_set(x_59, 2, x_2);
lean::cnstr_set(x_59, 3, x_3);
lean::cnstr_set_uint8(x_59, sizeof(void*)*4, x_19);
return x_59;
}
}
}
}
else
{
uint8 x_60; 
x_60 = lean::cnstr_get_uint8(x_5, sizeof(void*)*4);
if (x_60 == 0)
{
uint8 x_61; 
x_61 = !lean::is_exclusive(x_4);
if (x_61 == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; uint8 x_66; 
x_62 = lean::cnstr_get(x_4, 1);
x_63 = lean::cnstr_get(x_4, 2);
x_64 = lean::cnstr_get(x_4, 3);
x_65 = lean::cnstr_get(x_4, 0);
lean::dec(x_65);
x_66 = !lean::is_exclusive(x_5);
if (x_66 == 0)
{
uint8 x_67; obj* x_68; 
x_67 = 1;
lean::cnstr_set_uint8(x_5, sizeof(void*)*4, x_67);
lean::cnstr_set(x_4, 3, x_3);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 0, x_64);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_67);
x_68 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_68, 0, x_5);
lean::cnstr_set(x_68, 1, x_62);
lean::cnstr_set(x_68, 2, x_63);
lean::cnstr_set(x_68, 3, x_4);
lean::cnstr_set_uint8(x_68, sizeof(void*)*4, x_60);
return x_68;
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; uint8 x_73; obj* x_74; obj* x_75; 
x_69 = lean::cnstr_get(x_5, 0);
x_70 = lean::cnstr_get(x_5, 1);
x_71 = lean::cnstr_get(x_5, 2);
x_72 = lean::cnstr_get(x_5, 3);
lean::inc(x_72);
lean::inc(x_71);
lean::inc(x_70);
lean::inc(x_69);
lean::dec(x_5);
x_73 = 1;
x_74 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_74, 0, x_69);
lean::cnstr_set(x_74, 1, x_70);
lean::cnstr_set(x_74, 2, x_71);
lean::cnstr_set(x_74, 3, x_72);
lean::cnstr_set_uint8(x_74, sizeof(void*)*4, x_73);
lean::cnstr_set(x_4, 3, x_3);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 0, x_64);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_73);
x_75 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_62);
lean::cnstr_set(x_75, 2, x_63);
lean::cnstr_set(x_75, 3, x_4);
lean::cnstr_set_uint8(x_75, sizeof(void*)*4, x_60);
return x_75;
}
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; uint8 x_84; obj* x_85; obj* x_86; obj* x_87; 
x_76 = lean::cnstr_get(x_4, 1);
x_77 = lean::cnstr_get(x_4, 2);
x_78 = lean::cnstr_get(x_4, 3);
lean::inc(x_78);
lean::inc(x_77);
lean::inc(x_76);
lean::dec(x_4);
x_79 = lean::cnstr_get(x_5, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_5, 1);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_5, 2);
lean::inc(x_81);
x_82 = lean::cnstr_get(x_5, 3);
lean::inc(x_82);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 lean::cnstr_release(x_5, 3);
 x_83 = x_5;
} else {
 lean::dec_ref(x_5);
 x_83 = lean::box(0);
}
x_84 = 1;
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_79);
lean::cnstr_set(x_85, 1, x_80);
lean::cnstr_set(x_85, 2, x_81);
lean::cnstr_set(x_85, 3, x_82);
lean::cnstr_set_uint8(x_85, sizeof(void*)*4, x_84);
x_86 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_86, 0, x_78);
lean::cnstr_set(x_86, 1, x_1);
lean::cnstr_set(x_86, 2, x_2);
lean::cnstr_set(x_86, 3, x_3);
lean::cnstr_set_uint8(x_86, sizeof(void*)*4, x_84);
x_87 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set(x_87, 1, x_76);
lean::cnstr_set(x_87, 2, x_77);
lean::cnstr_set(x_87, 3, x_86);
lean::cnstr_set_uint8(x_87, sizeof(void*)*4, x_60);
return x_87;
}
}
else
{
obj* x_88; 
x_88 = lean::cnstr_get(x_4, 3);
lean::inc(x_88);
if (lean::obj_tag(x_88) == 0)
{
uint8 x_89; 
x_89 = !lean::is_exclusive(x_4);
if (x_89 == 0)
{
obj* x_90; obj* x_91; uint8 x_92; obj* x_93; 
x_90 = lean::cnstr_get(x_4, 3);
lean::dec(x_90);
x_91 = lean::cnstr_get(x_4, 0);
lean::dec(x_91);
x_92 = 0;
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_92);
x_93 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_93, 0, x_4);
lean::cnstr_set(x_93, 1, x_1);
lean::cnstr_set(x_93, 2, x_2);
lean::cnstr_set(x_93, 3, x_3);
lean::cnstr_set_uint8(x_93, sizeof(void*)*4, x_60);
return x_93;
}
else
{
obj* x_94; obj* x_95; uint8 x_96; obj* x_97; obj* x_98; 
x_94 = lean::cnstr_get(x_4, 1);
x_95 = lean::cnstr_get(x_4, 2);
lean::inc(x_95);
lean::inc(x_94);
lean::dec(x_4);
x_96 = 0;
x_97 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_97, 0, x_5);
lean::cnstr_set(x_97, 1, x_94);
lean::cnstr_set(x_97, 2, x_95);
lean::cnstr_set(x_97, 3, x_88);
lean::cnstr_set_uint8(x_97, sizeof(void*)*4, x_96);
x_98 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_1);
lean::cnstr_set(x_98, 2, x_2);
lean::cnstr_set(x_98, 3, x_3);
lean::cnstr_set_uint8(x_98, sizeof(void*)*4, x_60);
return x_98;
}
}
else
{
uint8 x_99; 
x_99 = lean::cnstr_get_uint8(x_88, sizeof(void*)*4);
if (x_99 == 0)
{
uint8 x_100; 
x_100 = !lean::is_exclusive(x_4);
if (x_100 == 0)
{
obj* x_101; obj* x_102; obj* x_103; obj* x_104; uint8 x_105; 
x_101 = lean::cnstr_get(x_4, 1);
x_102 = lean::cnstr_get(x_4, 2);
x_103 = lean::cnstr_get(x_4, 3);
lean::dec(x_103);
x_104 = lean::cnstr_get(x_4, 0);
lean::dec(x_104);
x_105 = !lean::is_exclusive(x_88);
if (x_105 == 0)
{
obj* x_106; obj* x_107; obj* x_108; obj* x_109; uint8 x_110; 
x_106 = lean::cnstr_get(x_88, 0);
x_107 = lean::cnstr_get(x_88, 1);
x_108 = lean::cnstr_get(x_88, 2);
x_109 = lean::cnstr_get(x_88, 3);
lean::inc(x_5);
lean::cnstr_set(x_88, 3, x_106);
lean::cnstr_set(x_88, 2, x_102);
lean::cnstr_set(x_88, 1, x_101);
lean::cnstr_set(x_88, 0, x_5);
x_110 = !lean::is_exclusive(x_5);
if (x_110 == 0)
{
obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
x_111 = lean::cnstr_get(x_5, 3);
lean::dec(x_111);
x_112 = lean::cnstr_get(x_5, 2);
lean::dec(x_112);
x_113 = lean::cnstr_get(x_5, 1);
lean::dec(x_113);
x_114 = lean::cnstr_get(x_5, 0);
lean::dec(x_114);
lean::cnstr_set_uint8(x_88, sizeof(void*)*4, x_60);
lean::cnstr_set(x_5, 3, x_3);
lean::cnstr_set(x_5, 2, x_2);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 0, x_109);
lean::cnstr_set(x_4, 3, x_5);
lean::cnstr_set(x_4, 2, x_108);
lean::cnstr_set(x_4, 1, x_107);
lean::cnstr_set(x_4, 0, x_88);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_99);
return x_4;
}
else
{
obj* x_115; 
lean::dec(x_5);
lean::cnstr_set_uint8(x_88, sizeof(void*)*4, x_60);
x_115 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_115, 0, x_109);
lean::cnstr_set(x_115, 1, x_1);
lean::cnstr_set(x_115, 2, x_2);
lean::cnstr_set(x_115, 3, x_3);
lean::cnstr_set_uint8(x_115, sizeof(void*)*4, x_60);
lean::cnstr_set(x_4, 3, x_115);
lean::cnstr_set(x_4, 2, x_108);
lean::cnstr_set(x_4, 1, x_107);
lean::cnstr_set(x_4, 0, x_88);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_99);
return x_4;
}
}
else
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_116 = lean::cnstr_get(x_88, 0);
x_117 = lean::cnstr_get(x_88, 1);
x_118 = lean::cnstr_get(x_88, 2);
x_119 = lean::cnstr_get(x_88, 3);
lean::inc(x_119);
lean::inc(x_118);
lean::inc(x_117);
lean::inc(x_116);
lean::dec(x_88);
lean::inc(x_5);
x_120 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_120, 0, x_5);
lean::cnstr_set(x_120, 1, x_101);
lean::cnstr_set(x_120, 2, x_102);
lean::cnstr_set(x_120, 3, x_116);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 lean::cnstr_release(x_5, 3);
 x_121 = x_5;
} else {
 lean::dec_ref(x_5);
 x_121 = lean::box(0);
}
lean::cnstr_set_uint8(x_120, sizeof(void*)*4, x_60);
if (lean::is_scalar(x_121)) {
 x_122 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_122 = x_121;
}
lean::cnstr_set(x_122, 0, x_119);
lean::cnstr_set(x_122, 1, x_1);
lean::cnstr_set(x_122, 2, x_2);
lean::cnstr_set(x_122, 3, x_3);
lean::cnstr_set_uint8(x_122, sizeof(void*)*4, x_60);
lean::cnstr_set(x_4, 3, x_122);
lean::cnstr_set(x_4, 2, x_118);
lean::cnstr_set(x_4, 1, x_117);
lean::cnstr_set(x_4, 0, x_120);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_99);
return x_4;
}
}
else
{
obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_123 = lean::cnstr_get(x_4, 1);
x_124 = lean::cnstr_get(x_4, 2);
lean::inc(x_124);
lean::inc(x_123);
lean::dec(x_4);
x_125 = lean::cnstr_get(x_88, 0);
lean::inc(x_125);
x_126 = lean::cnstr_get(x_88, 1);
lean::inc(x_126);
x_127 = lean::cnstr_get(x_88, 2);
lean::inc(x_127);
x_128 = lean::cnstr_get(x_88, 3);
lean::inc(x_128);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 lean::cnstr_release(x_88, 1);
 lean::cnstr_release(x_88, 2);
 lean::cnstr_release(x_88, 3);
 x_129 = x_88;
} else {
 lean::dec_ref(x_88);
 x_129 = lean::box(0);
}
lean::inc(x_5);
if (lean::is_scalar(x_129)) {
 x_130 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_130 = x_129;
}
lean::cnstr_set(x_130, 0, x_5);
lean::cnstr_set(x_130, 1, x_123);
lean::cnstr_set(x_130, 2, x_124);
lean::cnstr_set(x_130, 3, x_125);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 lean::cnstr_release(x_5, 3);
 x_131 = x_5;
} else {
 lean::dec_ref(x_5);
 x_131 = lean::box(0);
}
lean::cnstr_set_uint8(x_130, sizeof(void*)*4, x_60);
if (lean::is_scalar(x_131)) {
 x_132 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_132 = x_131;
}
lean::cnstr_set(x_132, 0, x_128);
lean::cnstr_set(x_132, 1, x_1);
lean::cnstr_set(x_132, 2, x_2);
lean::cnstr_set(x_132, 3, x_3);
lean::cnstr_set_uint8(x_132, sizeof(void*)*4, x_60);
x_133 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_133, 0, x_130);
lean::cnstr_set(x_133, 1, x_126);
lean::cnstr_set(x_133, 2, x_127);
lean::cnstr_set(x_133, 3, x_132);
lean::cnstr_set_uint8(x_133, sizeof(void*)*4, x_99);
return x_133;
}
}
else
{
uint8 x_134; 
x_134 = !lean::is_exclusive(x_4);
if (x_134 == 0)
{
obj* x_135; obj* x_136; uint8 x_137; 
x_135 = lean::cnstr_get(x_4, 3);
lean::dec(x_135);
x_136 = lean::cnstr_get(x_4, 0);
lean::dec(x_136);
x_137 = !lean::is_exclusive(x_5);
if (x_137 == 0)
{
uint8 x_138; obj* x_139; 
lean::cnstr_set_uint8(x_5, sizeof(void*)*4, x_99);
x_138 = 0;
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_138);
x_139 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_139, 0, x_4);
lean::cnstr_set(x_139, 1, x_1);
lean::cnstr_set(x_139, 2, x_2);
lean::cnstr_set(x_139, 3, x_3);
lean::cnstr_set_uint8(x_139, sizeof(void*)*4, x_99);
return x_139;
}
else
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; uint8 x_145; obj* x_146; 
x_140 = lean::cnstr_get(x_5, 0);
x_141 = lean::cnstr_get(x_5, 1);
x_142 = lean::cnstr_get(x_5, 2);
x_143 = lean::cnstr_get(x_5, 3);
lean::inc(x_143);
lean::inc(x_142);
lean::inc(x_141);
lean::inc(x_140);
lean::dec(x_5);
x_144 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_144, 0, x_140);
lean::cnstr_set(x_144, 1, x_141);
lean::cnstr_set(x_144, 2, x_142);
lean::cnstr_set(x_144, 3, x_143);
lean::cnstr_set_uint8(x_144, sizeof(void*)*4, x_99);
x_145 = 0;
lean::cnstr_set(x_4, 0, x_144);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_145);
x_146 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_146, 0, x_4);
lean::cnstr_set(x_146, 1, x_1);
lean::cnstr_set(x_146, 2, x_2);
lean::cnstr_set(x_146, 3, x_3);
lean::cnstr_set_uint8(x_146, sizeof(void*)*4, x_99);
return x_146;
}
}
else
{
obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; uint8 x_155; obj* x_156; obj* x_157; 
x_147 = lean::cnstr_get(x_4, 1);
x_148 = lean::cnstr_get(x_4, 2);
lean::inc(x_148);
lean::inc(x_147);
lean::dec(x_4);
x_149 = lean::cnstr_get(x_5, 0);
lean::inc(x_149);
x_150 = lean::cnstr_get(x_5, 1);
lean::inc(x_150);
x_151 = lean::cnstr_get(x_5, 2);
lean::inc(x_151);
x_152 = lean::cnstr_get(x_5, 3);
lean::inc(x_152);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 lean::cnstr_release(x_5, 3);
 x_153 = x_5;
} else {
 lean::dec_ref(x_5);
 x_153 = lean::box(0);
}
if (lean::is_scalar(x_153)) {
 x_154 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_154 = x_153;
}
lean::cnstr_set(x_154, 0, x_149);
lean::cnstr_set(x_154, 1, x_150);
lean::cnstr_set(x_154, 2, x_151);
lean::cnstr_set(x_154, 3, x_152);
lean::cnstr_set_uint8(x_154, sizeof(void*)*4, x_99);
x_155 = 0;
x_156 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_156, 0, x_154);
lean::cnstr_set(x_156, 1, x_147);
lean::cnstr_set(x_156, 2, x_148);
lean::cnstr_set(x_156, 3, x_88);
lean::cnstr_set_uint8(x_156, sizeof(void*)*4, x_155);
x_157 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_157, 0, x_156);
lean::cnstr_set(x_157, 1, x_1);
lean::cnstr_set(x_157, 2, x_2);
lean::cnstr_set(x_157, 3, x_3);
lean::cnstr_set_uint8(x_157, sizeof(void*)*4, x_99);
return x_157;
}
}
}
}
}
}
}
}
obj* l_RBNode_balance1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balance1___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_balance1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_balance1(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_balance2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
else
{
obj* x_5; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; 
x_6 = lean::cnstr_get(x_4, 3);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_4);
if (x_7 == 0)
{
obj* x_8; obj* x_9; uint8 x_10; uint8 x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_4, 3);
lean::dec(x_8);
x_9 = lean::cnstr_get(x_4, 0);
lean::dec(x_9);
x_10 = 0;
lean::cnstr_set(x_4, 0, x_6);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_10);
x_11 = 1;
x_12 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_12, 0, x_1);
lean::cnstr_set(x_12, 1, x_2);
lean::cnstr_set(x_12, 2, x_3);
lean::cnstr_set(x_12, 3, x_4);
lean::cnstr_set_uint8(x_12, sizeof(void*)*4, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_14; uint8 x_15; obj* x_16; uint8 x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_4, 1);
x_14 = lean::cnstr_get(x_4, 2);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_4);
x_15 = 0;
x_16 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_16, 0, x_6);
lean::cnstr_set(x_16, 1, x_13);
lean::cnstr_set(x_16, 2, x_14);
lean::cnstr_set(x_16, 3, x_6);
lean::cnstr_set_uint8(x_16, sizeof(void*)*4, x_15);
x_17 = 1;
x_18 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_18, 0, x_1);
lean::cnstr_set(x_18, 1, x_2);
lean::cnstr_set(x_18, 2, x_3);
lean::cnstr_set(x_18, 3, x_16);
lean::cnstr_set_uint8(x_18, sizeof(void*)*4, x_17);
return x_18;
}
}
else
{
uint8 x_19; 
x_19 = lean::cnstr_get_uint8(x_6, sizeof(void*)*4);
if (x_19 == 0)
{
uint8 x_20; 
x_20 = !lean::is_exclusive(x_4);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; 
x_21 = lean::cnstr_get(x_4, 1);
x_22 = lean::cnstr_get(x_4, 2);
x_23 = lean::cnstr_get(x_4, 3);
lean::dec(x_23);
x_24 = lean::cnstr_get(x_4, 0);
lean::dec(x_24);
x_25 = !lean::is_exclusive(x_6);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; uint8 x_30; obj* x_31; 
x_26 = lean::cnstr_get(x_6, 0);
x_27 = lean::cnstr_get(x_6, 1);
x_28 = lean::cnstr_get(x_6, 2);
x_29 = lean::cnstr_get(x_6, 3);
x_30 = 1;
lean::cnstr_set(x_6, 3, x_5);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set_uint8(x_6, sizeof(void*)*4, x_30);
lean::cnstr_set(x_4, 3, x_29);
lean::cnstr_set(x_4, 2, x_28);
lean::cnstr_set(x_4, 1, x_27);
lean::cnstr_set(x_4, 0, x_26);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_30);
x_31 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_31, 0, x_6);
lean::cnstr_set(x_31, 1, x_21);
lean::cnstr_set(x_31, 2, x_22);
lean::cnstr_set(x_31, 3, x_4);
lean::cnstr_set_uint8(x_31, sizeof(void*)*4, x_19);
return x_31;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; uint8 x_36; obj* x_37; obj* x_38; 
x_32 = lean::cnstr_get(x_6, 0);
x_33 = lean::cnstr_get(x_6, 1);
x_34 = lean::cnstr_get(x_6, 2);
x_35 = lean::cnstr_get(x_6, 3);
lean::inc(x_35);
lean::inc(x_34);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_6);
x_36 = 1;
x_37 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_37, 0, x_1);
lean::cnstr_set(x_37, 1, x_2);
lean::cnstr_set(x_37, 2, x_3);
lean::cnstr_set(x_37, 3, x_5);
lean::cnstr_set_uint8(x_37, sizeof(void*)*4, x_36);
lean::cnstr_set(x_4, 3, x_35);
lean::cnstr_set(x_4, 2, x_34);
lean::cnstr_set(x_4, 1, x_33);
lean::cnstr_set(x_4, 0, x_32);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_36);
x_38 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_21);
lean::cnstr_set(x_38, 2, x_22);
lean::cnstr_set(x_38, 3, x_4);
lean::cnstr_set_uint8(x_38, sizeof(void*)*4, x_19);
return x_38;
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = lean::cnstr_get(x_4, 1);
x_40 = lean::cnstr_get(x_4, 2);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_4);
x_41 = lean::cnstr_get(x_6, 0);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_6, 1);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_6, 2);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_6, 3);
lean::inc(x_44);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 lean::cnstr_release(x_6, 3);
 x_45 = x_6;
} else {
 lean::dec_ref(x_6);
 x_45 = lean::box(0);
}
x_46 = 1;
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_1);
lean::cnstr_set(x_47, 1, x_2);
lean::cnstr_set(x_47, 2, x_3);
lean::cnstr_set(x_47, 3, x_5);
lean::cnstr_set_uint8(x_47, sizeof(void*)*4, x_46);
x_48 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_48, 0, x_41);
lean::cnstr_set(x_48, 1, x_42);
lean::cnstr_set(x_48, 2, x_43);
lean::cnstr_set(x_48, 3, x_44);
lean::cnstr_set_uint8(x_48, sizeof(void*)*4, x_46);
x_49 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_39);
lean::cnstr_set(x_49, 2, x_40);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_uint8(x_49, sizeof(void*)*4, x_19);
return x_49;
}
}
else
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_4);
if (x_50 == 0)
{
obj* x_51; obj* x_52; uint8 x_53; obj* x_54; 
x_51 = lean::cnstr_get(x_4, 3);
lean::dec(x_51);
x_52 = lean::cnstr_get(x_4, 0);
lean::dec(x_52);
x_53 = 0;
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_53);
x_54 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_54, 0, x_1);
lean::cnstr_set(x_54, 1, x_2);
lean::cnstr_set(x_54, 2, x_3);
lean::cnstr_set(x_54, 3, x_4);
lean::cnstr_set_uint8(x_54, sizeof(void*)*4, x_19);
return x_54;
}
else
{
obj* x_55; obj* x_56; uint8 x_57; obj* x_58; obj* x_59; 
x_55 = lean::cnstr_get(x_4, 1);
x_56 = lean::cnstr_get(x_4, 2);
lean::inc(x_56);
lean::inc(x_55);
lean::dec(x_4);
x_57 = 0;
x_58 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_58, 0, x_5);
lean::cnstr_set(x_58, 1, x_55);
lean::cnstr_set(x_58, 2, x_56);
lean::cnstr_set(x_58, 3, x_6);
lean::cnstr_set_uint8(x_58, sizeof(void*)*4, x_57);
x_59 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_59, 0, x_1);
lean::cnstr_set(x_59, 1, x_2);
lean::cnstr_set(x_59, 2, x_3);
lean::cnstr_set(x_59, 3, x_58);
lean::cnstr_set_uint8(x_59, sizeof(void*)*4, x_19);
return x_59;
}
}
}
}
else
{
uint8 x_60; 
x_60 = lean::cnstr_get_uint8(x_5, sizeof(void*)*4);
if (x_60 == 0)
{
uint8 x_61; 
x_61 = !lean::is_exclusive(x_4);
if (x_61 == 0)
{
obj* x_62; uint8 x_63; 
x_62 = lean::cnstr_get(x_4, 0);
lean::dec(x_62);
x_63 = !lean::is_exclusive(x_5);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; uint8 x_68; obj* x_69; 
x_64 = lean::cnstr_get(x_5, 0);
x_65 = lean::cnstr_get(x_5, 1);
x_66 = lean::cnstr_get(x_5, 2);
x_67 = lean::cnstr_get(x_5, 3);
x_68 = 1;
lean::cnstr_set(x_5, 3, x_64);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set_uint8(x_5, sizeof(void*)*4, x_68);
lean::cnstr_set(x_4, 0, x_67);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_68);
x_69 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_69, 0, x_5);
lean::cnstr_set(x_69, 1, x_65);
lean::cnstr_set(x_69, 2, x_66);
lean::cnstr_set(x_69, 3, x_4);
lean::cnstr_set_uint8(x_69, sizeof(void*)*4, x_60);
return x_69;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; 
x_70 = lean::cnstr_get(x_5, 0);
x_71 = lean::cnstr_get(x_5, 1);
x_72 = lean::cnstr_get(x_5, 2);
x_73 = lean::cnstr_get(x_5, 3);
lean::inc(x_73);
lean::inc(x_72);
lean::inc(x_71);
lean::inc(x_70);
lean::dec(x_5);
x_74 = 1;
x_75 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_75, 0, x_1);
lean::cnstr_set(x_75, 1, x_2);
lean::cnstr_set(x_75, 2, x_3);
lean::cnstr_set(x_75, 3, x_70);
lean::cnstr_set_uint8(x_75, sizeof(void*)*4, x_74);
lean::cnstr_set(x_4, 0, x_73);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_74);
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_71);
lean::cnstr_set(x_76, 2, x_72);
lean::cnstr_set(x_76, 3, x_4);
lean::cnstr_set_uint8(x_76, sizeof(void*)*4, x_60);
return x_76;
}
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; 
x_77 = lean::cnstr_get(x_4, 1);
x_78 = lean::cnstr_get(x_4, 2);
x_79 = lean::cnstr_get(x_4, 3);
lean::inc(x_79);
lean::inc(x_78);
lean::inc(x_77);
lean::dec(x_4);
x_80 = lean::cnstr_get(x_5, 0);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_5, 1);
lean::inc(x_81);
x_82 = lean::cnstr_get(x_5, 2);
lean::inc(x_82);
x_83 = lean::cnstr_get(x_5, 3);
lean::inc(x_83);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 lean::cnstr_release(x_5, 3);
 x_84 = x_5;
} else {
 lean::dec_ref(x_5);
 x_84 = lean::box(0);
}
x_85 = 1;
if (lean::is_scalar(x_84)) {
 x_86 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_86 = x_84;
}
lean::cnstr_set(x_86, 0, x_1);
lean::cnstr_set(x_86, 1, x_2);
lean::cnstr_set(x_86, 2, x_3);
lean::cnstr_set(x_86, 3, x_80);
lean::cnstr_set_uint8(x_86, sizeof(void*)*4, x_85);
x_87 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_87, 0, x_83);
lean::cnstr_set(x_87, 1, x_77);
lean::cnstr_set(x_87, 2, x_78);
lean::cnstr_set(x_87, 3, x_79);
lean::cnstr_set_uint8(x_87, sizeof(void*)*4, x_85);
x_88 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_81);
lean::cnstr_set(x_88, 2, x_82);
lean::cnstr_set(x_88, 3, x_87);
lean::cnstr_set_uint8(x_88, sizeof(void*)*4, x_60);
return x_88;
}
}
else
{
obj* x_89; 
x_89 = lean::cnstr_get(x_4, 3);
lean::inc(x_89);
if (lean::obj_tag(x_89) == 0)
{
uint8 x_90; 
x_90 = !lean::is_exclusive(x_4);
if (x_90 == 0)
{
obj* x_91; obj* x_92; uint8 x_93; obj* x_94; 
x_91 = lean::cnstr_get(x_4, 3);
lean::dec(x_91);
x_92 = lean::cnstr_get(x_4, 0);
lean::dec(x_92);
x_93 = 0;
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_93);
x_94 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_94, 0, x_1);
lean::cnstr_set(x_94, 1, x_2);
lean::cnstr_set(x_94, 2, x_3);
lean::cnstr_set(x_94, 3, x_4);
lean::cnstr_set_uint8(x_94, sizeof(void*)*4, x_60);
return x_94;
}
else
{
obj* x_95; obj* x_96; uint8 x_97; obj* x_98; obj* x_99; 
x_95 = lean::cnstr_get(x_4, 1);
x_96 = lean::cnstr_get(x_4, 2);
lean::inc(x_96);
lean::inc(x_95);
lean::dec(x_4);
x_97 = 0;
x_98 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_98, 0, x_5);
lean::cnstr_set(x_98, 1, x_95);
lean::cnstr_set(x_98, 2, x_96);
lean::cnstr_set(x_98, 3, x_89);
lean::cnstr_set_uint8(x_98, sizeof(void*)*4, x_97);
x_99 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_99, 0, x_1);
lean::cnstr_set(x_99, 1, x_2);
lean::cnstr_set(x_99, 2, x_3);
lean::cnstr_set(x_99, 3, x_98);
lean::cnstr_set_uint8(x_99, sizeof(void*)*4, x_60);
return x_99;
}
}
else
{
uint8 x_100; 
x_100 = lean::cnstr_get_uint8(x_89, sizeof(void*)*4);
if (x_100 == 0)
{
uint8 x_101; 
x_101 = !lean::is_exclusive(x_4);
if (x_101 == 0)
{
obj* x_102; obj* x_103; uint8 x_104; 
x_102 = lean::cnstr_get(x_4, 3);
lean::dec(x_102);
x_103 = lean::cnstr_get(x_4, 0);
lean::dec(x_103);
x_104 = !lean::is_exclusive(x_89);
if (x_104 == 0)
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; uint8 x_109; 
x_105 = lean::cnstr_get(x_89, 0);
x_106 = lean::cnstr_get(x_89, 1);
x_107 = lean::cnstr_get(x_89, 2);
x_108 = lean::cnstr_get(x_89, 3);
lean::inc(x_5);
lean::cnstr_set(x_89, 3, x_5);
lean::cnstr_set(x_89, 2, x_3);
lean::cnstr_set(x_89, 1, x_2);
lean::cnstr_set(x_89, 0, x_1);
x_109 = !lean::is_exclusive(x_5);
if (x_109 == 0)
{
obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_110 = lean::cnstr_get(x_5, 3);
lean::dec(x_110);
x_111 = lean::cnstr_get(x_5, 2);
lean::dec(x_111);
x_112 = lean::cnstr_get(x_5, 1);
lean::dec(x_112);
x_113 = lean::cnstr_get(x_5, 0);
lean::dec(x_113);
lean::cnstr_set_uint8(x_89, sizeof(void*)*4, x_60);
lean::cnstr_set(x_5, 3, x_108);
lean::cnstr_set(x_5, 2, x_107);
lean::cnstr_set(x_5, 1, x_106);
lean::cnstr_set(x_5, 0, x_105);
lean::cnstr_set(x_4, 3, x_5);
lean::cnstr_set(x_4, 0, x_89);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_100);
return x_4;
}
else
{
obj* x_114; 
lean::dec(x_5);
lean::cnstr_set_uint8(x_89, sizeof(void*)*4, x_60);
x_114 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_114, 0, x_105);
lean::cnstr_set(x_114, 1, x_106);
lean::cnstr_set(x_114, 2, x_107);
lean::cnstr_set(x_114, 3, x_108);
lean::cnstr_set_uint8(x_114, sizeof(void*)*4, x_60);
lean::cnstr_set(x_4, 3, x_114);
lean::cnstr_set(x_4, 0, x_89);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_100);
return x_4;
}
}
else
{
obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
x_115 = lean::cnstr_get(x_89, 0);
x_116 = lean::cnstr_get(x_89, 1);
x_117 = lean::cnstr_get(x_89, 2);
x_118 = lean::cnstr_get(x_89, 3);
lean::inc(x_118);
lean::inc(x_117);
lean::inc(x_116);
lean::inc(x_115);
lean::dec(x_89);
lean::inc(x_5);
x_119 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_119, 0, x_1);
lean::cnstr_set(x_119, 1, x_2);
lean::cnstr_set(x_119, 2, x_3);
lean::cnstr_set(x_119, 3, x_5);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 lean::cnstr_release(x_5, 3);
 x_120 = x_5;
} else {
 lean::dec_ref(x_5);
 x_120 = lean::box(0);
}
lean::cnstr_set_uint8(x_119, sizeof(void*)*4, x_60);
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_115);
lean::cnstr_set(x_121, 1, x_116);
lean::cnstr_set(x_121, 2, x_117);
lean::cnstr_set(x_121, 3, x_118);
lean::cnstr_set_uint8(x_121, sizeof(void*)*4, x_60);
lean::cnstr_set(x_4, 3, x_121);
lean::cnstr_set(x_4, 0, x_119);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_100);
return x_4;
}
}
else
{
obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; 
x_122 = lean::cnstr_get(x_4, 1);
x_123 = lean::cnstr_get(x_4, 2);
lean::inc(x_123);
lean::inc(x_122);
lean::dec(x_4);
x_124 = lean::cnstr_get(x_89, 0);
lean::inc(x_124);
x_125 = lean::cnstr_get(x_89, 1);
lean::inc(x_125);
x_126 = lean::cnstr_get(x_89, 2);
lean::inc(x_126);
x_127 = lean::cnstr_get(x_89, 3);
lean::inc(x_127);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 lean::cnstr_release(x_89, 2);
 lean::cnstr_release(x_89, 3);
 x_128 = x_89;
} else {
 lean::dec_ref(x_89);
 x_128 = lean::box(0);
}
lean::inc(x_5);
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_1);
lean::cnstr_set(x_129, 1, x_2);
lean::cnstr_set(x_129, 2, x_3);
lean::cnstr_set(x_129, 3, x_5);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 lean::cnstr_release(x_5, 3);
 x_130 = x_5;
} else {
 lean::dec_ref(x_5);
 x_130 = lean::box(0);
}
lean::cnstr_set_uint8(x_129, sizeof(void*)*4, x_60);
if (lean::is_scalar(x_130)) {
 x_131 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_131 = x_130;
}
lean::cnstr_set(x_131, 0, x_124);
lean::cnstr_set(x_131, 1, x_125);
lean::cnstr_set(x_131, 2, x_126);
lean::cnstr_set(x_131, 3, x_127);
lean::cnstr_set_uint8(x_131, sizeof(void*)*4, x_60);
x_132 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_132, 0, x_129);
lean::cnstr_set(x_132, 1, x_122);
lean::cnstr_set(x_132, 2, x_123);
lean::cnstr_set(x_132, 3, x_131);
lean::cnstr_set_uint8(x_132, sizeof(void*)*4, x_100);
return x_132;
}
}
else
{
uint8 x_133; 
x_133 = !lean::is_exclusive(x_4);
if (x_133 == 0)
{
obj* x_134; obj* x_135; uint8 x_136; 
x_134 = lean::cnstr_get(x_4, 3);
lean::dec(x_134);
x_135 = lean::cnstr_get(x_4, 0);
lean::dec(x_135);
x_136 = !lean::is_exclusive(x_5);
if (x_136 == 0)
{
uint8 x_137; obj* x_138; 
lean::cnstr_set_uint8(x_5, sizeof(void*)*4, x_100);
x_137 = 0;
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_137);
x_138 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_138, 0, x_1);
lean::cnstr_set(x_138, 1, x_2);
lean::cnstr_set(x_138, 2, x_3);
lean::cnstr_set(x_138, 3, x_4);
lean::cnstr_set_uint8(x_138, sizeof(void*)*4, x_100);
return x_138;
}
else
{
obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; uint8 x_144; obj* x_145; 
x_139 = lean::cnstr_get(x_5, 0);
x_140 = lean::cnstr_get(x_5, 1);
x_141 = lean::cnstr_get(x_5, 2);
x_142 = lean::cnstr_get(x_5, 3);
lean::inc(x_142);
lean::inc(x_141);
lean::inc(x_140);
lean::inc(x_139);
lean::dec(x_5);
x_143 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_143, 0, x_139);
lean::cnstr_set(x_143, 1, x_140);
lean::cnstr_set(x_143, 2, x_141);
lean::cnstr_set(x_143, 3, x_142);
lean::cnstr_set_uint8(x_143, sizeof(void*)*4, x_100);
x_144 = 0;
lean::cnstr_set(x_4, 0, x_143);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_144);
x_145 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_145, 0, x_1);
lean::cnstr_set(x_145, 1, x_2);
lean::cnstr_set(x_145, 2, x_3);
lean::cnstr_set(x_145, 3, x_4);
lean::cnstr_set_uint8(x_145, sizeof(void*)*4, x_100);
return x_145;
}
}
else
{
obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; uint8 x_154; obj* x_155; obj* x_156; 
x_146 = lean::cnstr_get(x_4, 1);
x_147 = lean::cnstr_get(x_4, 2);
lean::inc(x_147);
lean::inc(x_146);
lean::dec(x_4);
x_148 = lean::cnstr_get(x_5, 0);
lean::inc(x_148);
x_149 = lean::cnstr_get(x_5, 1);
lean::inc(x_149);
x_150 = lean::cnstr_get(x_5, 2);
lean::inc(x_150);
x_151 = lean::cnstr_get(x_5, 3);
lean::inc(x_151);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 lean::cnstr_release(x_5, 3);
 x_152 = x_5;
} else {
 lean::dec_ref(x_5);
 x_152 = lean::box(0);
}
if (lean::is_scalar(x_152)) {
 x_153 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_153 = x_152;
}
lean::cnstr_set(x_153, 0, x_148);
lean::cnstr_set(x_153, 1, x_149);
lean::cnstr_set(x_153, 2, x_150);
lean::cnstr_set(x_153, 3, x_151);
lean::cnstr_set_uint8(x_153, sizeof(void*)*4, x_100);
x_154 = 0;
x_155 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_155, 0, x_153);
lean::cnstr_set(x_155, 1, x_146);
lean::cnstr_set(x_155, 2, x_147);
lean::cnstr_set(x_155, 3, x_89);
lean::cnstr_set_uint8(x_155, sizeof(void*)*4, x_154);
x_156 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_156, 0, x_1);
lean::cnstr_set(x_156, 1, x_2);
lean::cnstr_set(x_156, 2, x_3);
lean::cnstr_set(x_156, 3, x_155);
lean::cnstr_set_uint8(x_156, sizeof(void*)*4, x_100);
return x_156;
}
}
}
}
}
}
}
}
obj* l_RBNode_balance2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balance2___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_balance2___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_balance2(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBNode_isRed___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8 x_3; 
x_3 = lean::cnstr_get_uint8(x_1, sizeof(void*)*4);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
}
}
}
obj* l_RBNode_isRed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_isRed___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_RBNode_isRed___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBNode_isRed___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBNode_isRed___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_isRed(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBNode_isBlack___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8 x_3; 
x_3 = lean::cnstr_get_uint8(x_1, sizeof(void*)*4);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8 x_5; 
x_5 = 1;
return x_5;
}
}
}
}
obj* l_RBNode_isBlack(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_isBlack___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_RBNode_isBlack___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBNode_isBlack___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBNode_isBlack___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_isBlack(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_ins___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_5; obj* x_6; 
lean::dec(x_1);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_3);
lean::cnstr_set(x_6, 2, x_4);
lean::cnstr_set(x_6, 3, x_2);
lean::cnstr_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_uint8(x_2, sizeof(void*)*4);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_2);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_9 = lean::cnstr_get(x_2, 0);
x_10 = lean::cnstr_get(x_2, 1);
x_11 = lean::cnstr_get(x_2, 2);
x_12 = lean::cnstr_get(x_2, 3);
lean::inc(x_1);
lean::inc(x_10);
lean::inc(x_3);
x_13 = lean::apply_2(x_1, x_3, x_10);
x_14 = lean::unbox(x_13);
lean::dec(x_13);
if (x_14 == 0)
{
obj* x_15; uint8 x_16; 
lean::inc(x_1);
lean::inc(x_3);
lean::inc(x_10);
x_15 = lean::apply_2(x_1, x_10, x_3);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
lean::dec(x_11);
lean::dec(x_10);
lean::dec(x_1);
lean::cnstr_set(x_2, 2, x_4);
lean::cnstr_set(x_2, 1, x_3);
return x_2;
}
else
{
obj* x_17; 
x_17 = l_RBNode_ins___main___rarg(x_1, x_12, x_3, x_4);
lean::cnstr_set(x_2, 3, x_17);
return x_2;
}
}
else
{
obj* x_18; 
x_18 = l_RBNode_ins___main___rarg(x_1, x_9, x_3, x_4);
lean::cnstr_set(x_2, 0, x_18);
return x_2;
}
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_19 = lean::cnstr_get(x_2, 0);
x_20 = lean::cnstr_get(x_2, 1);
x_21 = lean::cnstr_get(x_2, 2);
x_22 = lean::cnstr_get(x_2, 3);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_20);
lean::inc(x_3);
x_23 = lean::apply_2(x_1, x_3, x_20);
x_24 = lean::unbox(x_23);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_25; uint8 x_26; 
lean::inc(x_1);
lean::inc(x_3);
lean::inc(x_20);
x_25 = lean::apply_2(x_1, x_20, x_3);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_27; 
lean::dec(x_21);
lean::dec(x_20);
lean::dec(x_1);
x_27 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_27, 0, x_19);
lean::cnstr_set(x_27, 1, x_3);
lean::cnstr_set(x_27, 2, x_4);
lean::cnstr_set(x_27, 3, x_22);
lean::cnstr_set_uint8(x_27, sizeof(void*)*4, x_7);
return x_27;
}
else
{
obj* x_28; obj* x_29; 
x_28 = l_RBNode_ins___main___rarg(x_1, x_22, x_3, x_4);
x_29 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_29, 0, x_19);
lean::cnstr_set(x_29, 1, x_20);
lean::cnstr_set(x_29, 2, x_21);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_uint8(x_29, sizeof(void*)*4, x_7);
return x_29;
}
}
else
{
obj* x_30; obj* x_31; 
x_30 = l_RBNode_ins___main___rarg(x_1, x_19, x_3, x_4);
x_31 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_20);
lean::cnstr_set(x_31, 2, x_21);
lean::cnstr_set(x_31, 3, x_22);
lean::cnstr_set_uint8(x_31, sizeof(void*)*4, x_7);
return x_31;
}
}
}
else
{
uint8 x_32; 
x_32 = !lean::is_exclusive(x_2);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; uint8 x_38; 
x_33 = lean::cnstr_get(x_2, 0);
x_34 = lean::cnstr_get(x_2, 1);
x_35 = lean::cnstr_get(x_2, 2);
x_36 = lean::cnstr_get(x_2, 3);
lean::inc(x_1);
lean::inc(x_34);
lean::inc(x_3);
x_37 = lean::apply_2(x_1, x_3, x_34);
x_38 = lean::unbox(x_37);
lean::dec(x_37);
if (x_38 == 0)
{
obj* x_39; uint8 x_40; 
lean::inc(x_1);
lean::inc(x_3);
lean::inc(x_34);
x_39 = lean::apply_2(x_1, x_34, x_3);
x_40 = lean::unbox(x_39);
lean::dec(x_39);
if (x_40 == 0)
{
lean::dec(x_35);
lean::dec(x_34);
lean::dec(x_1);
lean::cnstr_set(x_2, 2, x_4);
lean::cnstr_set(x_2, 1, x_3);
return x_2;
}
else
{
uint8 x_41; 
x_41 = l_RBNode_isRed___rarg(x_36);
if (x_41 == 0)
{
obj* x_42; 
x_42 = l_RBNode_ins___main___rarg(x_1, x_36, x_3, x_4);
lean::cnstr_set(x_2, 3, x_42);
return x_2;
}
else
{
obj* x_43; 
x_43 = l_RBNode_ins___main___rarg(x_1, x_36, x_3, x_4);
if (lean::obj_tag(x_43) == 0)
{
lean::free_heap_obj(x_2);
lean::dec(x_35);
lean::dec(x_34);
lean::dec(x_33);
return x_43;
}
else
{
obj* x_44; 
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; 
x_45 = lean::cnstr_get(x_43, 3);
lean::inc(x_45);
if (lean::obj_tag(x_45) == 0)
{
uint8 x_46; 
x_46 = !lean::is_exclusive(x_43);
if (x_46 == 0)
{
obj* x_47; obj* x_48; uint8 x_49; uint8 x_50; 
x_47 = lean::cnstr_get(x_43, 3);
lean::dec(x_47);
x_48 = lean::cnstr_get(x_43, 0);
lean::dec(x_48);
x_49 = 0;
lean::cnstr_set(x_43, 0, x_45);
lean::cnstr_set_uint8(x_43, sizeof(void*)*4, x_49);
x_50 = 1;
lean::cnstr_set(x_2, 3, x_43);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_50);
return x_2;
}
else
{
obj* x_51; obj* x_52; uint8 x_53; obj* x_54; uint8 x_55; 
x_51 = lean::cnstr_get(x_43, 1);
x_52 = lean::cnstr_get(x_43, 2);
lean::inc(x_52);
lean::inc(x_51);
lean::dec(x_43);
x_53 = 0;
x_54 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_54, 0, x_45);
lean::cnstr_set(x_54, 1, x_51);
lean::cnstr_set(x_54, 2, x_52);
lean::cnstr_set(x_54, 3, x_45);
lean::cnstr_set_uint8(x_54, sizeof(void*)*4, x_53);
x_55 = 1;
lean::cnstr_set(x_2, 3, x_54);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_55);
return x_2;
}
}
else
{
uint8 x_56; 
x_56 = lean::cnstr_get_uint8(x_45, sizeof(void*)*4);
if (x_56 == 0)
{
uint8 x_57; 
x_57 = !lean::is_exclusive(x_43);
if (x_57 == 0)
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; uint8 x_62; 
x_58 = lean::cnstr_get(x_43, 1);
x_59 = lean::cnstr_get(x_43, 2);
x_60 = lean::cnstr_get(x_43, 3);
lean::dec(x_60);
x_61 = lean::cnstr_get(x_43, 0);
lean::dec(x_61);
x_62 = !lean::is_exclusive(x_45);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; uint8 x_67; 
x_63 = lean::cnstr_get(x_45, 0);
x_64 = lean::cnstr_get(x_45, 1);
x_65 = lean::cnstr_get(x_45, 2);
x_66 = lean::cnstr_get(x_45, 3);
x_67 = 1;
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set(x_45, 2, x_35);
lean::cnstr_set(x_45, 1, x_34);
lean::cnstr_set(x_45, 0, x_33);
lean::cnstr_set_uint8(x_45, sizeof(void*)*4, x_67);
lean::cnstr_set(x_43, 3, x_66);
lean::cnstr_set(x_43, 2, x_65);
lean::cnstr_set(x_43, 1, x_64);
lean::cnstr_set(x_43, 0, x_63);
lean::cnstr_set_uint8(x_43, sizeof(void*)*4, x_67);
lean::cnstr_set(x_2, 3, x_43);
lean::cnstr_set(x_2, 2, x_59);
lean::cnstr_set(x_2, 1, x_58);
lean::cnstr_set(x_2, 0, x_45);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_56);
return x_2;
}
else
{
obj* x_68; obj* x_69; obj* x_70; obj* x_71; uint8 x_72; obj* x_73; 
x_68 = lean::cnstr_get(x_45, 0);
x_69 = lean::cnstr_get(x_45, 1);
x_70 = lean::cnstr_get(x_45, 2);
x_71 = lean::cnstr_get(x_45, 3);
lean::inc(x_71);
lean::inc(x_70);
lean::inc(x_69);
lean::inc(x_68);
lean::dec(x_45);
x_72 = 1;
x_73 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_73, 0, x_33);
lean::cnstr_set(x_73, 1, x_34);
lean::cnstr_set(x_73, 2, x_35);
lean::cnstr_set(x_73, 3, x_44);
lean::cnstr_set_uint8(x_73, sizeof(void*)*4, x_72);
lean::cnstr_set(x_43, 3, x_71);
lean::cnstr_set(x_43, 2, x_70);
lean::cnstr_set(x_43, 1, x_69);
lean::cnstr_set(x_43, 0, x_68);
lean::cnstr_set_uint8(x_43, sizeof(void*)*4, x_72);
lean::cnstr_set(x_2, 3, x_43);
lean::cnstr_set(x_2, 2, x_59);
lean::cnstr_set(x_2, 1, x_58);
lean::cnstr_set(x_2, 0, x_73);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_56);
return x_2;
}
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; uint8 x_81; obj* x_82; obj* x_83; 
x_74 = lean::cnstr_get(x_43, 1);
x_75 = lean::cnstr_get(x_43, 2);
lean::inc(x_75);
lean::inc(x_74);
lean::dec(x_43);
x_76 = lean::cnstr_get(x_45, 0);
lean::inc(x_76);
x_77 = lean::cnstr_get(x_45, 1);
lean::inc(x_77);
x_78 = lean::cnstr_get(x_45, 2);
lean::inc(x_78);
x_79 = lean::cnstr_get(x_45, 3);
lean::inc(x_79);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 lean::cnstr_release(x_45, 2);
 lean::cnstr_release(x_45, 3);
 x_80 = x_45;
} else {
 lean::dec_ref(x_45);
 x_80 = lean::box(0);
}
x_81 = 1;
if (lean::is_scalar(x_80)) {
 x_82 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_82 = x_80;
}
lean::cnstr_set(x_82, 0, x_33);
lean::cnstr_set(x_82, 1, x_34);
lean::cnstr_set(x_82, 2, x_35);
lean::cnstr_set(x_82, 3, x_44);
lean::cnstr_set_uint8(x_82, sizeof(void*)*4, x_81);
x_83 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_83, 0, x_76);
lean::cnstr_set(x_83, 1, x_77);
lean::cnstr_set(x_83, 2, x_78);
lean::cnstr_set(x_83, 3, x_79);
lean::cnstr_set_uint8(x_83, sizeof(void*)*4, x_81);
lean::cnstr_set(x_2, 3, x_83);
lean::cnstr_set(x_2, 2, x_75);
lean::cnstr_set(x_2, 1, x_74);
lean::cnstr_set(x_2, 0, x_82);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_56);
return x_2;
}
}
else
{
uint8 x_84; 
x_84 = !lean::is_exclusive(x_43);
if (x_84 == 0)
{
obj* x_85; obj* x_86; uint8 x_87; 
x_85 = lean::cnstr_get(x_43, 3);
lean::dec(x_85);
x_86 = lean::cnstr_get(x_43, 0);
lean::dec(x_86);
x_87 = 0;
lean::cnstr_set_uint8(x_43, sizeof(void*)*4, x_87);
lean::cnstr_set(x_2, 3, x_43);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_56);
return x_2;
}
else
{
obj* x_88; obj* x_89; uint8 x_90; obj* x_91; 
x_88 = lean::cnstr_get(x_43, 1);
x_89 = lean::cnstr_get(x_43, 2);
lean::inc(x_89);
lean::inc(x_88);
lean::dec(x_43);
x_90 = 0;
x_91 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_91, 0, x_44);
lean::cnstr_set(x_91, 1, x_88);
lean::cnstr_set(x_91, 2, x_89);
lean::cnstr_set(x_91, 3, x_45);
lean::cnstr_set_uint8(x_91, sizeof(void*)*4, x_90);
lean::cnstr_set(x_2, 3, x_91);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_56);
return x_2;
}
}
}
}
else
{
uint8 x_92; 
x_92 = lean::cnstr_get_uint8(x_44, sizeof(void*)*4);
if (x_92 == 0)
{
uint8 x_93; 
x_93 = !lean::is_exclusive(x_43);
if (x_93 == 0)
{
obj* x_94; uint8 x_95; 
x_94 = lean::cnstr_get(x_43, 0);
lean::dec(x_94);
x_95 = !lean::is_exclusive(x_44);
if (x_95 == 0)
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; uint8 x_100; 
x_96 = lean::cnstr_get(x_44, 0);
x_97 = lean::cnstr_get(x_44, 1);
x_98 = lean::cnstr_get(x_44, 2);
x_99 = lean::cnstr_get(x_44, 3);
x_100 = 1;
lean::cnstr_set(x_44, 3, x_96);
lean::cnstr_set(x_44, 2, x_35);
lean::cnstr_set(x_44, 1, x_34);
lean::cnstr_set(x_44, 0, x_33);
lean::cnstr_set_uint8(x_44, sizeof(void*)*4, x_100);
lean::cnstr_set(x_43, 0, x_99);
lean::cnstr_set_uint8(x_43, sizeof(void*)*4, x_100);
lean::cnstr_set(x_2, 3, x_43);
lean::cnstr_set(x_2, 2, x_98);
lean::cnstr_set(x_2, 1, x_97);
lean::cnstr_set(x_2, 0, x_44);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_92);
return x_2;
}
else
{
obj* x_101; obj* x_102; obj* x_103; obj* x_104; uint8 x_105; obj* x_106; 
x_101 = lean::cnstr_get(x_44, 0);
x_102 = lean::cnstr_get(x_44, 1);
x_103 = lean::cnstr_get(x_44, 2);
x_104 = lean::cnstr_get(x_44, 3);
lean::inc(x_104);
lean::inc(x_103);
lean::inc(x_102);
lean::inc(x_101);
lean::dec(x_44);
x_105 = 1;
x_106 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_106, 0, x_33);
lean::cnstr_set(x_106, 1, x_34);
lean::cnstr_set(x_106, 2, x_35);
lean::cnstr_set(x_106, 3, x_101);
lean::cnstr_set_uint8(x_106, sizeof(void*)*4, x_105);
lean::cnstr_set(x_43, 0, x_104);
lean::cnstr_set_uint8(x_43, sizeof(void*)*4, x_105);
lean::cnstr_set(x_2, 3, x_43);
lean::cnstr_set(x_2, 2, x_103);
lean::cnstr_set(x_2, 1, x_102);
lean::cnstr_set(x_2, 0, x_106);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_92);
return x_2;
}
}
else
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; uint8 x_115; obj* x_116; obj* x_117; 
x_107 = lean::cnstr_get(x_43, 1);
x_108 = lean::cnstr_get(x_43, 2);
x_109 = lean::cnstr_get(x_43, 3);
lean::inc(x_109);
lean::inc(x_108);
lean::inc(x_107);
lean::dec(x_43);
x_110 = lean::cnstr_get(x_44, 0);
lean::inc(x_110);
x_111 = lean::cnstr_get(x_44, 1);
lean::inc(x_111);
x_112 = lean::cnstr_get(x_44, 2);
lean::inc(x_112);
x_113 = lean::cnstr_get(x_44, 3);
lean::inc(x_113);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 lean::cnstr_release(x_44, 2);
 lean::cnstr_release(x_44, 3);
 x_114 = x_44;
} else {
 lean::dec_ref(x_44);
 x_114 = lean::box(0);
}
x_115 = 1;
if (lean::is_scalar(x_114)) {
 x_116 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_116 = x_114;
}
lean::cnstr_set(x_116, 0, x_33);
lean::cnstr_set(x_116, 1, x_34);
lean::cnstr_set(x_116, 2, x_35);
lean::cnstr_set(x_116, 3, x_110);
lean::cnstr_set_uint8(x_116, sizeof(void*)*4, x_115);
x_117 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_117, 0, x_113);
lean::cnstr_set(x_117, 1, x_107);
lean::cnstr_set(x_117, 2, x_108);
lean::cnstr_set(x_117, 3, x_109);
lean::cnstr_set_uint8(x_117, sizeof(void*)*4, x_115);
lean::cnstr_set(x_2, 3, x_117);
lean::cnstr_set(x_2, 2, x_112);
lean::cnstr_set(x_2, 1, x_111);
lean::cnstr_set(x_2, 0, x_116);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_92);
return x_2;
}
}
else
{
obj* x_118; 
x_118 = lean::cnstr_get(x_43, 3);
lean::inc(x_118);
if (lean::obj_tag(x_118) == 0)
{
uint8 x_119; 
x_119 = !lean::is_exclusive(x_43);
if (x_119 == 0)
{
obj* x_120; obj* x_121; uint8 x_122; 
x_120 = lean::cnstr_get(x_43, 3);
lean::dec(x_120);
x_121 = lean::cnstr_get(x_43, 0);
lean::dec(x_121);
x_122 = 0;
lean::cnstr_set_uint8(x_43, sizeof(void*)*4, x_122);
lean::cnstr_set(x_2, 3, x_43);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_92);
return x_2;
}
else
{
obj* x_123; obj* x_124; uint8 x_125; obj* x_126; 
x_123 = lean::cnstr_get(x_43, 1);
x_124 = lean::cnstr_get(x_43, 2);
lean::inc(x_124);
lean::inc(x_123);
lean::dec(x_43);
x_125 = 0;
x_126 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_126, 0, x_44);
lean::cnstr_set(x_126, 1, x_123);
lean::cnstr_set(x_126, 2, x_124);
lean::cnstr_set(x_126, 3, x_118);
lean::cnstr_set_uint8(x_126, sizeof(void*)*4, x_125);
lean::cnstr_set(x_2, 3, x_126);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_92);
return x_2;
}
}
else
{
uint8 x_127; 
x_127 = lean::cnstr_get_uint8(x_118, sizeof(void*)*4);
if (x_127 == 0)
{
uint8 x_128; 
lean::free_heap_obj(x_2);
x_128 = !lean::is_exclusive(x_43);
if (x_128 == 0)
{
obj* x_129; obj* x_130; uint8 x_131; 
x_129 = lean::cnstr_get(x_43, 3);
lean::dec(x_129);
x_130 = lean::cnstr_get(x_43, 0);
lean::dec(x_130);
x_131 = !lean::is_exclusive(x_118);
if (x_131 == 0)
{
obj* x_132; obj* x_133; obj* x_134; obj* x_135; uint8 x_136; 
x_132 = lean::cnstr_get(x_118, 0);
x_133 = lean::cnstr_get(x_118, 1);
x_134 = lean::cnstr_get(x_118, 2);
x_135 = lean::cnstr_get(x_118, 3);
lean::inc(x_44);
lean::cnstr_set(x_118, 3, x_44);
lean::cnstr_set(x_118, 2, x_35);
lean::cnstr_set(x_118, 1, x_34);
lean::cnstr_set(x_118, 0, x_33);
x_136 = !lean::is_exclusive(x_44);
if (x_136 == 0)
{
obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_137 = lean::cnstr_get(x_44, 3);
lean::dec(x_137);
x_138 = lean::cnstr_get(x_44, 2);
lean::dec(x_138);
x_139 = lean::cnstr_get(x_44, 1);
lean::dec(x_139);
x_140 = lean::cnstr_get(x_44, 0);
lean::dec(x_140);
lean::cnstr_set_uint8(x_118, sizeof(void*)*4, x_92);
lean::cnstr_set(x_44, 3, x_135);
lean::cnstr_set(x_44, 2, x_134);
lean::cnstr_set(x_44, 1, x_133);
lean::cnstr_set(x_44, 0, x_132);
lean::cnstr_set(x_43, 3, x_44);
lean::cnstr_set(x_43, 0, x_118);
lean::cnstr_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
else
{
obj* x_141; 
lean::dec(x_44);
lean::cnstr_set_uint8(x_118, sizeof(void*)*4, x_92);
x_141 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_141, 0, x_132);
lean::cnstr_set(x_141, 1, x_133);
lean::cnstr_set(x_141, 2, x_134);
lean::cnstr_set(x_141, 3, x_135);
lean::cnstr_set_uint8(x_141, sizeof(void*)*4, x_92);
lean::cnstr_set(x_43, 3, x_141);
lean::cnstr_set(x_43, 0, x_118);
lean::cnstr_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
}
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
x_142 = lean::cnstr_get(x_118, 0);
x_143 = lean::cnstr_get(x_118, 1);
x_144 = lean::cnstr_get(x_118, 2);
x_145 = lean::cnstr_get(x_118, 3);
lean::inc(x_145);
lean::inc(x_144);
lean::inc(x_143);
lean::inc(x_142);
lean::dec(x_118);
lean::inc(x_44);
x_146 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_146, 0, x_33);
lean::cnstr_set(x_146, 1, x_34);
lean::cnstr_set(x_146, 2, x_35);
lean::cnstr_set(x_146, 3, x_44);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 lean::cnstr_release(x_44, 2);
 lean::cnstr_release(x_44, 3);
 x_147 = x_44;
} else {
 lean::dec_ref(x_44);
 x_147 = lean::box(0);
}
lean::cnstr_set_uint8(x_146, sizeof(void*)*4, x_92);
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_142);
lean::cnstr_set(x_148, 1, x_143);
lean::cnstr_set(x_148, 2, x_144);
lean::cnstr_set(x_148, 3, x_145);
lean::cnstr_set_uint8(x_148, sizeof(void*)*4, x_92);
lean::cnstr_set(x_43, 3, x_148);
lean::cnstr_set(x_43, 0, x_146);
lean::cnstr_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
}
else
{
obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; 
x_149 = lean::cnstr_get(x_43, 1);
x_150 = lean::cnstr_get(x_43, 2);
lean::inc(x_150);
lean::inc(x_149);
lean::dec(x_43);
x_151 = lean::cnstr_get(x_118, 0);
lean::inc(x_151);
x_152 = lean::cnstr_get(x_118, 1);
lean::inc(x_152);
x_153 = lean::cnstr_get(x_118, 2);
lean::inc(x_153);
x_154 = lean::cnstr_get(x_118, 3);
lean::inc(x_154);
if (lean::is_exclusive(x_118)) {
 lean::cnstr_release(x_118, 0);
 lean::cnstr_release(x_118, 1);
 lean::cnstr_release(x_118, 2);
 lean::cnstr_release(x_118, 3);
 x_155 = x_118;
} else {
 lean::dec_ref(x_118);
 x_155 = lean::box(0);
}
lean::inc(x_44);
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_33);
lean::cnstr_set(x_156, 1, x_34);
lean::cnstr_set(x_156, 2, x_35);
lean::cnstr_set(x_156, 3, x_44);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 lean::cnstr_release(x_44, 2);
 lean::cnstr_release(x_44, 3);
 x_157 = x_44;
} else {
 lean::dec_ref(x_44);
 x_157 = lean::box(0);
}
lean::cnstr_set_uint8(x_156, sizeof(void*)*4, x_92);
if (lean::is_scalar(x_157)) {
 x_158 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_158 = x_157;
}
lean::cnstr_set(x_158, 0, x_151);
lean::cnstr_set(x_158, 1, x_152);
lean::cnstr_set(x_158, 2, x_153);
lean::cnstr_set(x_158, 3, x_154);
lean::cnstr_set_uint8(x_158, sizeof(void*)*4, x_92);
x_159 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_159, 0, x_156);
lean::cnstr_set(x_159, 1, x_149);
lean::cnstr_set(x_159, 2, x_150);
lean::cnstr_set(x_159, 3, x_158);
lean::cnstr_set_uint8(x_159, sizeof(void*)*4, x_127);
return x_159;
}
}
else
{
uint8 x_160; 
x_160 = !lean::is_exclusive(x_43);
if (x_160 == 0)
{
obj* x_161; obj* x_162; uint8 x_163; 
x_161 = lean::cnstr_get(x_43, 3);
lean::dec(x_161);
x_162 = lean::cnstr_get(x_43, 0);
lean::dec(x_162);
x_163 = !lean::is_exclusive(x_44);
if (x_163 == 0)
{
uint8 x_164; 
lean::cnstr_set_uint8(x_44, sizeof(void*)*4, x_127);
x_164 = 0;
lean::cnstr_set_uint8(x_43, sizeof(void*)*4, x_164);
lean::cnstr_set(x_2, 3, x_43);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_127);
return x_2;
}
else
{
obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; uint8 x_170; 
x_165 = lean::cnstr_get(x_44, 0);
x_166 = lean::cnstr_get(x_44, 1);
x_167 = lean::cnstr_get(x_44, 2);
x_168 = lean::cnstr_get(x_44, 3);
lean::inc(x_168);
lean::inc(x_167);
lean::inc(x_166);
lean::inc(x_165);
lean::dec(x_44);
x_169 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_169, 0, x_165);
lean::cnstr_set(x_169, 1, x_166);
lean::cnstr_set(x_169, 2, x_167);
lean::cnstr_set(x_169, 3, x_168);
lean::cnstr_set_uint8(x_169, sizeof(void*)*4, x_127);
x_170 = 0;
lean::cnstr_set(x_43, 0, x_169);
lean::cnstr_set_uint8(x_43, sizeof(void*)*4, x_170);
lean::cnstr_set(x_2, 3, x_43);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_127);
return x_2;
}
}
else
{
obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; uint8 x_179; obj* x_180; 
x_171 = lean::cnstr_get(x_43, 1);
x_172 = lean::cnstr_get(x_43, 2);
lean::inc(x_172);
lean::inc(x_171);
lean::dec(x_43);
x_173 = lean::cnstr_get(x_44, 0);
lean::inc(x_173);
x_174 = lean::cnstr_get(x_44, 1);
lean::inc(x_174);
x_175 = lean::cnstr_get(x_44, 2);
lean::inc(x_175);
x_176 = lean::cnstr_get(x_44, 3);
lean::inc(x_176);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 lean::cnstr_release(x_44, 2);
 lean::cnstr_release(x_44, 3);
 x_177 = x_44;
} else {
 lean::dec_ref(x_44);
 x_177 = lean::box(0);
}
if (lean::is_scalar(x_177)) {
 x_178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_178 = x_177;
}
lean::cnstr_set(x_178, 0, x_173);
lean::cnstr_set(x_178, 1, x_174);
lean::cnstr_set(x_178, 2, x_175);
lean::cnstr_set(x_178, 3, x_176);
lean::cnstr_set_uint8(x_178, sizeof(void*)*4, x_127);
x_179 = 0;
x_180 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_180, 0, x_178);
lean::cnstr_set(x_180, 1, x_171);
lean::cnstr_set(x_180, 2, x_172);
lean::cnstr_set(x_180, 3, x_118);
lean::cnstr_set_uint8(x_180, sizeof(void*)*4, x_179);
lean::cnstr_set(x_2, 3, x_180);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_127);
return x_2;
}
}
}
}
}
}
}
}
}
else
{
uint8 x_181; 
x_181 = l_RBNode_isRed___rarg(x_33);
if (x_181 == 0)
{
obj* x_182; 
x_182 = l_RBNode_ins___main___rarg(x_1, x_33, x_3, x_4);
lean::cnstr_set(x_2, 0, x_182);
return x_2;
}
else
{
obj* x_183; 
x_183 = l_RBNode_ins___main___rarg(x_1, x_33, x_3, x_4);
if (lean::obj_tag(x_183) == 0)
{
lean::free_heap_obj(x_2);
lean::dec(x_36);
lean::dec(x_35);
lean::dec(x_34);
return x_183;
}
else
{
obj* x_184; 
x_184 = lean::cnstr_get(x_183, 0);
lean::inc(x_184);
if (lean::obj_tag(x_184) == 0)
{
obj* x_185; 
x_185 = lean::cnstr_get(x_183, 3);
lean::inc(x_185);
if (lean::obj_tag(x_185) == 0)
{
uint8 x_186; 
x_186 = !lean::is_exclusive(x_183);
if (x_186 == 0)
{
obj* x_187; obj* x_188; uint8 x_189; uint8 x_190; 
x_187 = lean::cnstr_get(x_183, 3);
lean::dec(x_187);
x_188 = lean::cnstr_get(x_183, 0);
lean::dec(x_188);
x_189 = 0;
lean::cnstr_set(x_183, 0, x_185);
lean::cnstr_set_uint8(x_183, sizeof(void*)*4, x_189);
x_190 = 1;
lean::cnstr_set(x_2, 0, x_183);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_190);
return x_2;
}
else
{
obj* x_191; obj* x_192; uint8 x_193; obj* x_194; uint8 x_195; 
x_191 = lean::cnstr_get(x_183, 1);
x_192 = lean::cnstr_get(x_183, 2);
lean::inc(x_192);
lean::inc(x_191);
lean::dec(x_183);
x_193 = 0;
x_194 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_194, 0, x_185);
lean::cnstr_set(x_194, 1, x_191);
lean::cnstr_set(x_194, 2, x_192);
lean::cnstr_set(x_194, 3, x_185);
lean::cnstr_set_uint8(x_194, sizeof(void*)*4, x_193);
x_195 = 1;
lean::cnstr_set(x_2, 0, x_194);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_195);
return x_2;
}
}
else
{
uint8 x_196; 
x_196 = lean::cnstr_get_uint8(x_185, sizeof(void*)*4);
if (x_196 == 0)
{
uint8 x_197; 
x_197 = !lean::is_exclusive(x_183);
if (x_197 == 0)
{
obj* x_198; obj* x_199; obj* x_200; obj* x_201; uint8 x_202; 
x_198 = lean::cnstr_get(x_183, 1);
x_199 = lean::cnstr_get(x_183, 2);
x_200 = lean::cnstr_get(x_183, 3);
lean::dec(x_200);
x_201 = lean::cnstr_get(x_183, 0);
lean::dec(x_201);
x_202 = !lean::is_exclusive(x_185);
if (x_202 == 0)
{
obj* x_203; obj* x_204; obj* x_205; obj* x_206; uint8 x_207; 
x_203 = lean::cnstr_get(x_185, 0);
x_204 = lean::cnstr_get(x_185, 1);
x_205 = lean::cnstr_get(x_185, 2);
x_206 = lean::cnstr_get(x_185, 3);
x_207 = 1;
lean::cnstr_set(x_185, 3, x_203);
lean::cnstr_set(x_185, 2, x_199);
lean::cnstr_set(x_185, 1, x_198);
lean::cnstr_set(x_185, 0, x_184);
lean::cnstr_set_uint8(x_185, sizeof(void*)*4, x_207);
lean::cnstr_set(x_183, 3, x_36);
lean::cnstr_set(x_183, 2, x_35);
lean::cnstr_set(x_183, 1, x_34);
lean::cnstr_set(x_183, 0, x_206);
lean::cnstr_set_uint8(x_183, sizeof(void*)*4, x_207);
lean::cnstr_set(x_2, 3, x_183);
lean::cnstr_set(x_2, 2, x_205);
lean::cnstr_set(x_2, 1, x_204);
lean::cnstr_set(x_2, 0, x_185);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_196);
return x_2;
}
else
{
obj* x_208; obj* x_209; obj* x_210; obj* x_211; uint8 x_212; obj* x_213; 
x_208 = lean::cnstr_get(x_185, 0);
x_209 = lean::cnstr_get(x_185, 1);
x_210 = lean::cnstr_get(x_185, 2);
x_211 = lean::cnstr_get(x_185, 3);
lean::inc(x_211);
lean::inc(x_210);
lean::inc(x_209);
lean::inc(x_208);
lean::dec(x_185);
x_212 = 1;
x_213 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_213, 0, x_184);
lean::cnstr_set(x_213, 1, x_198);
lean::cnstr_set(x_213, 2, x_199);
lean::cnstr_set(x_213, 3, x_208);
lean::cnstr_set_uint8(x_213, sizeof(void*)*4, x_212);
lean::cnstr_set(x_183, 3, x_36);
lean::cnstr_set(x_183, 2, x_35);
lean::cnstr_set(x_183, 1, x_34);
lean::cnstr_set(x_183, 0, x_211);
lean::cnstr_set_uint8(x_183, sizeof(void*)*4, x_212);
lean::cnstr_set(x_2, 3, x_183);
lean::cnstr_set(x_2, 2, x_210);
lean::cnstr_set(x_2, 1, x_209);
lean::cnstr_set(x_2, 0, x_213);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_196);
return x_2;
}
}
else
{
obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; uint8 x_221; obj* x_222; obj* x_223; 
x_214 = lean::cnstr_get(x_183, 1);
x_215 = lean::cnstr_get(x_183, 2);
lean::inc(x_215);
lean::inc(x_214);
lean::dec(x_183);
x_216 = lean::cnstr_get(x_185, 0);
lean::inc(x_216);
x_217 = lean::cnstr_get(x_185, 1);
lean::inc(x_217);
x_218 = lean::cnstr_get(x_185, 2);
lean::inc(x_218);
x_219 = lean::cnstr_get(x_185, 3);
lean::inc(x_219);
if (lean::is_exclusive(x_185)) {
 lean::cnstr_release(x_185, 0);
 lean::cnstr_release(x_185, 1);
 lean::cnstr_release(x_185, 2);
 lean::cnstr_release(x_185, 3);
 x_220 = x_185;
} else {
 lean::dec_ref(x_185);
 x_220 = lean::box(0);
}
x_221 = 1;
if (lean::is_scalar(x_220)) {
 x_222 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_222 = x_220;
}
lean::cnstr_set(x_222, 0, x_184);
lean::cnstr_set(x_222, 1, x_214);
lean::cnstr_set(x_222, 2, x_215);
lean::cnstr_set(x_222, 3, x_216);
lean::cnstr_set_uint8(x_222, sizeof(void*)*4, x_221);
x_223 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_223, 0, x_219);
lean::cnstr_set(x_223, 1, x_34);
lean::cnstr_set(x_223, 2, x_35);
lean::cnstr_set(x_223, 3, x_36);
lean::cnstr_set_uint8(x_223, sizeof(void*)*4, x_221);
lean::cnstr_set(x_2, 3, x_223);
lean::cnstr_set(x_2, 2, x_218);
lean::cnstr_set(x_2, 1, x_217);
lean::cnstr_set(x_2, 0, x_222);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_196);
return x_2;
}
}
else
{
uint8 x_224; 
x_224 = !lean::is_exclusive(x_183);
if (x_224 == 0)
{
obj* x_225; obj* x_226; uint8 x_227; 
x_225 = lean::cnstr_get(x_183, 3);
lean::dec(x_225);
x_226 = lean::cnstr_get(x_183, 0);
lean::dec(x_226);
x_227 = 0;
lean::cnstr_set_uint8(x_183, sizeof(void*)*4, x_227);
lean::cnstr_set(x_2, 0, x_183);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_196);
return x_2;
}
else
{
obj* x_228; obj* x_229; uint8 x_230; obj* x_231; 
x_228 = lean::cnstr_get(x_183, 1);
x_229 = lean::cnstr_get(x_183, 2);
lean::inc(x_229);
lean::inc(x_228);
lean::dec(x_183);
x_230 = 0;
x_231 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_231, 0, x_184);
lean::cnstr_set(x_231, 1, x_228);
lean::cnstr_set(x_231, 2, x_229);
lean::cnstr_set(x_231, 3, x_185);
lean::cnstr_set_uint8(x_231, sizeof(void*)*4, x_230);
lean::cnstr_set(x_2, 0, x_231);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_196);
return x_2;
}
}
}
}
else
{
uint8 x_232; 
x_232 = lean::cnstr_get_uint8(x_184, sizeof(void*)*4);
if (x_232 == 0)
{
uint8 x_233; 
x_233 = !lean::is_exclusive(x_183);
if (x_233 == 0)
{
obj* x_234; obj* x_235; obj* x_236; obj* x_237; uint8 x_238; 
x_234 = lean::cnstr_get(x_183, 1);
x_235 = lean::cnstr_get(x_183, 2);
x_236 = lean::cnstr_get(x_183, 3);
x_237 = lean::cnstr_get(x_183, 0);
lean::dec(x_237);
x_238 = !lean::is_exclusive(x_184);
if (x_238 == 0)
{
uint8 x_239; 
x_239 = 1;
lean::cnstr_set_uint8(x_184, sizeof(void*)*4, x_239);
lean::cnstr_set(x_183, 3, x_36);
lean::cnstr_set(x_183, 2, x_35);
lean::cnstr_set(x_183, 1, x_34);
lean::cnstr_set(x_183, 0, x_236);
lean::cnstr_set_uint8(x_183, sizeof(void*)*4, x_239);
lean::cnstr_set(x_2, 3, x_183);
lean::cnstr_set(x_2, 2, x_235);
lean::cnstr_set(x_2, 1, x_234);
lean::cnstr_set(x_2, 0, x_184);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_232);
return x_2;
}
else
{
obj* x_240; obj* x_241; obj* x_242; obj* x_243; uint8 x_244; obj* x_245; 
x_240 = lean::cnstr_get(x_184, 0);
x_241 = lean::cnstr_get(x_184, 1);
x_242 = lean::cnstr_get(x_184, 2);
x_243 = lean::cnstr_get(x_184, 3);
lean::inc(x_243);
lean::inc(x_242);
lean::inc(x_241);
lean::inc(x_240);
lean::dec(x_184);
x_244 = 1;
x_245 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_245, 0, x_240);
lean::cnstr_set(x_245, 1, x_241);
lean::cnstr_set(x_245, 2, x_242);
lean::cnstr_set(x_245, 3, x_243);
lean::cnstr_set_uint8(x_245, sizeof(void*)*4, x_244);
lean::cnstr_set(x_183, 3, x_36);
lean::cnstr_set(x_183, 2, x_35);
lean::cnstr_set(x_183, 1, x_34);
lean::cnstr_set(x_183, 0, x_236);
lean::cnstr_set_uint8(x_183, sizeof(void*)*4, x_244);
lean::cnstr_set(x_2, 3, x_183);
lean::cnstr_set(x_2, 2, x_235);
lean::cnstr_set(x_2, 1, x_234);
lean::cnstr_set(x_2, 0, x_245);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_232);
return x_2;
}
}
else
{
obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; uint8 x_254; obj* x_255; obj* x_256; 
x_246 = lean::cnstr_get(x_183, 1);
x_247 = lean::cnstr_get(x_183, 2);
x_248 = lean::cnstr_get(x_183, 3);
lean::inc(x_248);
lean::inc(x_247);
lean::inc(x_246);
lean::dec(x_183);
x_249 = lean::cnstr_get(x_184, 0);
lean::inc(x_249);
x_250 = lean::cnstr_get(x_184, 1);
lean::inc(x_250);
x_251 = lean::cnstr_get(x_184, 2);
lean::inc(x_251);
x_252 = lean::cnstr_get(x_184, 3);
lean::inc(x_252);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 1);
 lean::cnstr_release(x_184, 2);
 lean::cnstr_release(x_184, 3);
 x_253 = x_184;
} else {
 lean::dec_ref(x_184);
 x_253 = lean::box(0);
}
x_254 = 1;
if (lean::is_scalar(x_253)) {
 x_255 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_255 = x_253;
}
lean::cnstr_set(x_255, 0, x_249);
lean::cnstr_set(x_255, 1, x_250);
lean::cnstr_set(x_255, 2, x_251);
lean::cnstr_set(x_255, 3, x_252);
lean::cnstr_set_uint8(x_255, sizeof(void*)*4, x_254);
x_256 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_256, 0, x_248);
lean::cnstr_set(x_256, 1, x_34);
lean::cnstr_set(x_256, 2, x_35);
lean::cnstr_set(x_256, 3, x_36);
lean::cnstr_set_uint8(x_256, sizeof(void*)*4, x_254);
lean::cnstr_set(x_2, 3, x_256);
lean::cnstr_set(x_2, 2, x_247);
lean::cnstr_set(x_2, 1, x_246);
lean::cnstr_set(x_2, 0, x_255);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_232);
return x_2;
}
}
else
{
obj* x_257; 
x_257 = lean::cnstr_get(x_183, 3);
lean::inc(x_257);
if (lean::obj_tag(x_257) == 0)
{
uint8 x_258; 
x_258 = !lean::is_exclusive(x_183);
if (x_258 == 0)
{
obj* x_259; obj* x_260; uint8 x_261; 
x_259 = lean::cnstr_get(x_183, 3);
lean::dec(x_259);
x_260 = lean::cnstr_get(x_183, 0);
lean::dec(x_260);
x_261 = 0;
lean::cnstr_set_uint8(x_183, sizeof(void*)*4, x_261);
lean::cnstr_set(x_2, 0, x_183);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_232);
return x_2;
}
else
{
obj* x_262; obj* x_263; uint8 x_264; obj* x_265; 
x_262 = lean::cnstr_get(x_183, 1);
x_263 = lean::cnstr_get(x_183, 2);
lean::inc(x_263);
lean::inc(x_262);
lean::dec(x_183);
x_264 = 0;
x_265 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_265, 0, x_184);
lean::cnstr_set(x_265, 1, x_262);
lean::cnstr_set(x_265, 2, x_263);
lean::cnstr_set(x_265, 3, x_257);
lean::cnstr_set_uint8(x_265, sizeof(void*)*4, x_264);
lean::cnstr_set(x_2, 0, x_265);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_232);
return x_2;
}
}
else
{
uint8 x_266; 
x_266 = lean::cnstr_get_uint8(x_257, sizeof(void*)*4);
if (x_266 == 0)
{
uint8 x_267; 
lean::free_heap_obj(x_2);
x_267 = !lean::is_exclusive(x_183);
if (x_267 == 0)
{
obj* x_268; obj* x_269; obj* x_270; obj* x_271; uint8 x_272; 
x_268 = lean::cnstr_get(x_183, 1);
x_269 = lean::cnstr_get(x_183, 2);
x_270 = lean::cnstr_get(x_183, 3);
lean::dec(x_270);
x_271 = lean::cnstr_get(x_183, 0);
lean::dec(x_271);
x_272 = !lean::is_exclusive(x_257);
if (x_272 == 0)
{
obj* x_273; obj* x_274; obj* x_275; obj* x_276; uint8 x_277; 
x_273 = lean::cnstr_get(x_257, 0);
x_274 = lean::cnstr_get(x_257, 1);
x_275 = lean::cnstr_get(x_257, 2);
x_276 = lean::cnstr_get(x_257, 3);
lean::inc(x_184);
lean::cnstr_set(x_257, 3, x_273);
lean::cnstr_set(x_257, 2, x_269);
lean::cnstr_set(x_257, 1, x_268);
lean::cnstr_set(x_257, 0, x_184);
x_277 = !lean::is_exclusive(x_184);
if (x_277 == 0)
{
obj* x_278; obj* x_279; obj* x_280; obj* x_281; 
x_278 = lean::cnstr_get(x_184, 3);
lean::dec(x_278);
x_279 = lean::cnstr_get(x_184, 2);
lean::dec(x_279);
x_280 = lean::cnstr_get(x_184, 1);
lean::dec(x_280);
x_281 = lean::cnstr_get(x_184, 0);
lean::dec(x_281);
lean::cnstr_set_uint8(x_257, sizeof(void*)*4, x_232);
lean::cnstr_set(x_184, 3, x_36);
lean::cnstr_set(x_184, 2, x_35);
lean::cnstr_set(x_184, 1, x_34);
lean::cnstr_set(x_184, 0, x_276);
lean::cnstr_set(x_183, 3, x_184);
lean::cnstr_set(x_183, 2, x_275);
lean::cnstr_set(x_183, 1, x_274);
lean::cnstr_set(x_183, 0, x_257);
lean::cnstr_set_uint8(x_183, sizeof(void*)*4, x_266);
return x_183;
}
else
{
obj* x_282; 
lean::dec(x_184);
lean::cnstr_set_uint8(x_257, sizeof(void*)*4, x_232);
x_282 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_282, 0, x_276);
lean::cnstr_set(x_282, 1, x_34);
lean::cnstr_set(x_282, 2, x_35);
lean::cnstr_set(x_282, 3, x_36);
lean::cnstr_set_uint8(x_282, sizeof(void*)*4, x_232);
lean::cnstr_set(x_183, 3, x_282);
lean::cnstr_set(x_183, 2, x_275);
lean::cnstr_set(x_183, 1, x_274);
lean::cnstr_set(x_183, 0, x_257);
lean::cnstr_set_uint8(x_183, sizeof(void*)*4, x_266);
return x_183;
}
}
else
{
obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; 
x_283 = lean::cnstr_get(x_257, 0);
x_284 = lean::cnstr_get(x_257, 1);
x_285 = lean::cnstr_get(x_257, 2);
x_286 = lean::cnstr_get(x_257, 3);
lean::inc(x_286);
lean::inc(x_285);
lean::inc(x_284);
lean::inc(x_283);
lean::dec(x_257);
lean::inc(x_184);
x_287 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_287, 0, x_184);
lean::cnstr_set(x_287, 1, x_268);
lean::cnstr_set(x_287, 2, x_269);
lean::cnstr_set(x_287, 3, x_283);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 1);
 lean::cnstr_release(x_184, 2);
 lean::cnstr_release(x_184, 3);
 x_288 = x_184;
} else {
 lean::dec_ref(x_184);
 x_288 = lean::box(0);
}
lean::cnstr_set_uint8(x_287, sizeof(void*)*4, x_232);
if (lean::is_scalar(x_288)) {
 x_289 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_289 = x_288;
}
lean::cnstr_set(x_289, 0, x_286);
lean::cnstr_set(x_289, 1, x_34);
lean::cnstr_set(x_289, 2, x_35);
lean::cnstr_set(x_289, 3, x_36);
lean::cnstr_set_uint8(x_289, sizeof(void*)*4, x_232);
lean::cnstr_set(x_183, 3, x_289);
lean::cnstr_set(x_183, 2, x_285);
lean::cnstr_set(x_183, 1, x_284);
lean::cnstr_set(x_183, 0, x_287);
lean::cnstr_set_uint8(x_183, sizeof(void*)*4, x_266);
return x_183;
}
}
else
{
obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; 
x_290 = lean::cnstr_get(x_183, 1);
x_291 = lean::cnstr_get(x_183, 2);
lean::inc(x_291);
lean::inc(x_290);
lean::dec(x_183);
x_292 = lean::cnstr_get(x_257, 0);
lean::inc(x_292);
x_293 = lean::cnstr_get(x_257, 1);
lean::inc(x_293);
x_294 = lean::cnstr_get(x_257, 2);
lean::inc(x_294);
x_295 = lean::cnstr_get(x_257, 3);
lean::inc(x_295);
if (lean::is_exclusive(x_257)) {
 lean::cnstr_release(x_257, 0);
 lean::cnstr_release(x_257, 1);
 lean::cnstr_release(x_257, 2);
 lean::cnstr_release(x_257, 3);
 x_296 = x_257;
} else {
 lean::dec_ref(x_257);
 x_296 = lean::box(0);
}
lean::inc(x_184);
if (lean::is_scalar(x_296)) {
 x_297 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_297 = x_296;
}
lean::cnstr_set(x_297, 0, x_184);
lean::cnstr_set(x_297, 1, x_290);
lean::cnstr_set(x_297, 2, x_291);
lean::cnstr_set(x_297, 3, x_292);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 1);
 lean::cnstr_release(x_184, 2);
 lean::cnstr_release(x_184, 3);
 x_298 = x_184;
} else {
 lean::dec_ref(x_184);
 x_298 = lean::box(0);
}
lean::cnstr_set_uint8(x_297, sizeof(void*)*4, x_232);
if (lean::is_scalar(x_298)) {
 x_299 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_299 = x_298;
}
lean::cnstr_set(x_299, 0, x_295);
lean::cnstr_set(x_299, 1, x_34);
lean::cnstr_set(x_299, 2, x_35);
lean::cnstr_set(x_299, 3, x_36);
lean::cnstr_set_uint8(x_299, sizeof(void*)*4, x_232);
x_300 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_300, 0, x_297);
lean::cnstr_set(x_300, 1, x_293);
lean::cnstr_set(x_300, 2, x_294);
lean::cnstr_set(x_300, 3, x_299);
lean::cnstr_set_uint8(x_300, sizeof(void*)*4, x_266);
return x_300;
}
}
else
{
uint8 x_301; 
x_301 = !lean::is_exclusive(x_183);
if (x_301 == 0)
{
obj* x_302; obj* x_303; uint8 x_304; 
x_302 = lean::cnstr_get(x_183, 3);
lean::dec(x_302);
x_303 = lean::cnstr_get(x_183, 0);
lean::dec(x_303);
x_304 = !lean::is_exclusive(x_184);
if (x_304 == 0)
{
uint8 x_305; 
lean::cnstr_set_uint8(x_184, sizeof(void*)*4, x_266);
x_305 = 0;
lean::cnstr_set_uint8(x_183, sizeof(void*)*4, x_305);
lean::cnstr_set(x_2, 0, x_183);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_266);
return x_2;
}
else
{
obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; uint8 x_311; 
x_306 = lean::cnstr_get(x_184, 0);
x_307 = lean::cnstr_get(x_184, 1);
x_308 = lean::cnstr_get(x_184, 2);
x_309 = lean::cnstr_get(x_184, 3);
lean::inc(x_309);
lean::inc(x_308);
lean::inc(x_307);
lean::inc(x_306);
lean::dec(x_184);
x_310 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_310, 0, x_306);
lean::cnstr_set(x_310, 1, x_307);
lean::cnstr_set(x_310, 2, x_308);
lean::cnstr_set(x_310, 3, x_309);
lean::cnstr_set_uint8(x_310, sizeof(void*)*4, x_266);
x_311 = 0;
lean::cnstr_set(x_183, 0, x_310);
lean::cnstr_set_uint8(x_183, sizeof(void*)*4, x_311);
lean::cnstr_set(x_2, 0, x_183);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_266);
return x_2;
}
}
else
{
obj* x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; obj* x_317; obj* x_318; obj* x_319; uint8 x_320; obj* x_321; 
x_312 = lean::cnstr_get(x_183, 1);
x_313 = lean::cnstr_get(x_183, 2);
lean::inc(x_313);
lean::inc(x_312);
lean::dec(x_183);
x_314 = lean::cnstr_get(x_184, 0);
lean::inc(x_314);
x_315 = lean::cnstr_get(x_184, 1);
lean::inc(x_315);
x_316 = lean::cnstr_get(x_184, 2);
lean::inc(x_316);
x_317 = lean::cnstr_get(x_184, 3);
lean::inc(x_317);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 1);
 lean::cnstr_release(x_184, 2);
 lean::cnstr_release(x_184, 3);
 x_318 = x_184;
} else {
 lean::dec_ref(x_184);
 x_318 = lean::box(0);
}
if (lean::is_scalar(x_318)) {
 x_319 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_319 = x_318;
}
lean::cnstr_set(x_319, 0, x_314);
lean::cnstr_set(x_319, 1, x_315);
lean::cnstr_set(x_319, 2, x_316);
lean::cnstr_set(x_319, 3, x_317);
lean::cnstr_set_uint8(x_319, sizeof(void*)*4, x_266);
x_320 = 0;
x_321 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_321, 0, x_319);
lean::cnstr_set(x_321, 1, x_312);
lean::cnstr_set(x_321, 2, x_313);
lean::cnstr_set(x_321, 3, x_257);
lean::cnstr_set_uint8(x_321, sizeof(void*)*4, x_320);
lean::cnstr_set(x_2, 0, x_321);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_266);
return x_2;
}
}
}
}
}
}
}
}
}
else
{
obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; uint8 x_327; 
x_322 = lean::cnstr_get(x_2, 0);
x_323 = lean::cnstr_get(x_2, 1);
x_324 = lean::cnstr_get(x_2, 2);
x_325 = lean::cnstr_get(x_2, 3);
lean::inc(x_325);
lean::inc(x_324);
lean::inc(x_323);
lean::inc(x_322);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_323);
lean::inc(x_3);
x_326 = lean::apply_2(x_1, x_3, x_323);
x_327 = lean::unbox(x_326);
lean::dec(x_326);
if (x_327 == 0)
{
obj* x_328; uint8 x_329; 
lean::inc(x_1);
lean::inc(x_3);
lean::inc(x_323);
x_328 = lean::apply_2(x_1, x_323, x_3);
x_329 = lean::unbox(x_328);
lean::dec(x_328);
if (x_329 == 0)
{
obj* x_330; 
lean::dec(x_324);
lean::dec(x_323);
lean::dec(x_1);
x_330 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_330, 0, x_322);
lean::cnstr_set(x_330, 1, x_3);
lean::cnstr_set(x_330, 2, x_4);
lean::cnstr_set(x_330, 3, x_325);
lean::cnstr_set_uint8(x_330, sizeof(void*)*4, x_7);
return x_330;
}
else
{
uint8 x_331; 
x_331 = l_RBNode_isRed___rarg(x_325);
if (x_331 == 0)
{
obj* x_332; obj* x_333; 
x_332 = l_RBNode_ins___main___rarg(x_1, x_325, x_3, x_4);
x_333 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_333, 0, x_322);
lean::cnstr_set(x_333, 1, x_323);
lean::cnstr_set(x_333, 2, x_324);
lean::cnstr_set(x_333, 3, x_332);
lean::cnstr_set_uint8(x_333, sizeof(void*)*4, x_7);
return x_333;
}
else
{
obj* x_334; 
x_334 = l_RBNode_ins___main___rarg(x_1, x_325, x_3, x_4);
if (lean::obj_tag(x_334) == 0)
{
lean::dec(x_324);
lean::dec(x_323);
lean::dec(x_322);
return x_334;
}
else
{
obj* x_335; 
x_335 = lean::cnstr_get(x_334, 0);
lean::inc(x_335);
if (lean::obj_tag(x_335) == 0)
{
obj* x_336; 
x_336 = lean::cnstr_get(x_334, 3);
lean::inc(x_336);
if (lean::obj_tag(x_336) == 0)
{
obj* x_337; obj* x_338; obj* x_339; uint8 x_340; obj* x_341; uint8 x_342; obj* x_343; 
x_337 = lean::cnstr_get(x_334, 1);
lean::inc(x_337);
x_338 = lean::cnstr_get(x_334, 2);
lean::inc(x_338);
if (lean::is_exclusive(x_334)) {
 lean::cnstr_release(x_334, 0);
 lean::cnstr_release(x_334, 1);
 lean::cnstr_release(x_334, 2);
 lean::cnstr_release(x_334, 3);
 x_339 = x_334;
} else {
 lean::dec_ref(x_334);
 x_339 = lean::box(0);
}
x_340 = 0;
if (lean::is_scalar(x_339)) {
 x_341 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_341 = x_339;
}
lean::cnstr_set(x_341, 0, x_336);
lean::cnstr_set(x_341, 1, x_337);
lean::cnstr_set(x_341, 2, x_338);
lean::cnstr_set(x_341, 3, x_336);
lean::cnstr_set_uint8(x_341, sizeof(void*)*4, x_340);
x_342 = 1;
x_343 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_343, 0, x_322);
lean::cnstr_set(x_343, 1, x_323);
lean::cnstr_set(x_343, 2, x_324);
lean::cnstr_set(x_343, 3, x_341);
lean::cnstr_set_uint8(x_343, sizeof(void*)*4, x_342);
return x_343;
}
else
{
uint8 x_344; 
x_344 = lean::cnstr_get_uint8(x_336, sizeof(void*)*4);
if (x_344 == 0)
{
obj* x_345; obj* x_346; obj* x_347; obj* x_348; obj* x_349; obj* x_350; obj* x_351; obj* x_352; uint8 x_353; obj* x_354; obj* x_355; obj* x_356; 
x_345 = lean::cnstr_get(x_334, 1);
lean::inc(x_345);
x_346 = lean::cnstr_get(x_334, 2);
lean::inc(x_346);
if (lean::is_exclusive(x_334)) {
 lean::cnstr_release(x_334, 0);
 lean::cnstr_release(x_334, 1);
 lean::cnstr_release(x_334, 2);
 lean::cnstr_release(x_334, 3);
 x_347 = x_334;
} else {
 lean::dec_ref(x_334);
 x_347 = lean::box(0);
}
x_348 = lean::cnstr_get(x_336, 0);
lean::inc(x_348);
x_349 = lean::cnstr_get(x_336, 1);
lean::inc(x_349);
x_350 = lean::cnstr_get(x_336, 2);
lean::inc(x_350);
x_351 = lean::cnstr_get(x_336, 3);
lean::inc(x_351);
if (lean::is_exclusive(x_336)) {
 lean::cnstr_release(x_336, 0);
 lean::cnstr_release(x_336, 1);
 lean::cnstr_release(x_336, 2);
 lean::cnstr_release(x_336, 3);
 x_352 = x_336;
} else {
 lean::dec_ref(x_336);
 x_352 = lean::box(0);
}
x_353 = 1;
if (lean::is_scalar(x_352)) {
 x_354 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_354 = x_352;
}
lean::cnstr_set(x_354, 0, x_322);
lean::cnstr_set(x_354, 1, x_323);
lean::cnstr_set(x_354, 2, x_324);
lean::cnstr_set(x_354, 3, x_335);
lean::cnstr_set_uint8(x_354, sizeof(void*)*4, x_353);
if (lean::is_scalar(x_347)) {
 x_355 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_355 = x_347;
}
lean::cnstr_set(x_355, 0, x_348);
lean::cnstr_set(x_355, 1, x_349);
lean::cnstr_set(x_355, 2, x_350);
lean::cnstr_set(x_355, 3, x_351);
lean::cnstr_set_uint8(x_355, sizeof(void*)*4, x_353);
x_356 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_356, 0, x_354);
lean::cnstr_set(x_356, 1, x_345);
lean::cnstr_set(x_356, 2, x_346);
lean::cnstr_set(x_356, 3, x_355);
lean::cnstr_set_uint8(x_356, sizeof(void*)*4, x_344);
return x_356;
}
else
{
obj* x_357; obj* x_358; obj* x_359; uint8 x_360; obj* x_361; obj* x_362; 
x_357 = lean::cnstr_get(x_334, 1);
lean::inc(x_357);
x_358 = lean::cnstr_get(x_334, 2);
lean::inc(x_358);
if (lean::is_exclusive(x_334)) {
 lean::cnstr_release(x_334, 0);
 lean::cnstr_release(x_334, 1);
 lean::cnstr_release(x_334, 2);
 lean::cnstr_release(x_334, 3);
 x_359 = x_334;
} else {
 lean::dec_ref(x_334);
 x_359 = lean::box(0);
}
x_360 = 0;
if (lean::is_scalar(x_359)) {
 x_361 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_361 = x_359;
}
lean::cnstr_set(x_361, 0, x_335);
lean::cnstr_set(x_361, 1, x_357);
lean::cnstr_set(x_361, 2, x_358);
lean::cnstr_set(x_361, 3, x_336);
lean::cnstr_set_uint8(x_361, sizeof(void*)*4, x_360);
x_362 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_362, 0, x_322);
lean::cnstr_set(x_362, 1, x_323);
lean::cnstr_set(x_362, 2, x_324);
lean::cnstr_set(x_362, 3, x_361);
lean::cnstr_set_uint8(x_362, sizeof(void*)*4, x_344);
return x_362;
}
}
}
else
{
uint8 x_363; 
x_363 = lean::cnstr_get_uint8(x_335, sizeof(void*)*4);
if (x_363 == 0)
{
obj* x_364; obj* x_365; obj* x_366; obj* x_367; obj* x_368; obj* x_369; obj* x_370; obj* x_371; obj* x_372; uint8 x_373; obj* x_374; obj* x_375; obj* x_376; 
x_364 = lean::cnstr_get(x_334, 1);
lean::inc(x_364);
x_365 = lean::cnstr_get(x_334, 2);
lean::inc(x_365);
x_366 = lean::cnstr_get(x_334, 3);
lean::inc(x_366);
if (lean::is_exclusive(x_334)) {
 lean::cnstr_release(x_334, 0);
 lean::cnstr_release(x_334, 1);
 lean::cnstr_release(x_334, 2);
 lean::cnstr_release(x_334, 3);
 x_367 = x_334;
} else {
 lean::dec_ref(x_334);
 x_367 = lean::box(0);
}
x_368 = lean::cnstr_get(x_335, 0);
lean::inc(x_368);
x_369 = lean::cnstr_get(x_335, 1);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_335, 2);
lean::inc(x_370);
x_371 = lean::cnstr_get(x_335, 3);
lean::inc(x_371);
if (lean::is_exclusive(x_335)) {
 lean::cnstr_release(x_335, 0);
 lean::cnstr_release(x_335, 1);
 lean::cnstr_release(x_335, 2);
 lean::cnstr_release(x_335, 3);
 x_372 = x_335;
} else {
 lean::dec_ref(x_335);
 x_372 = lean::box(0);
}
x_373 = 1;
if (lean::is_scalar(x_372)) {
 x_374 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_374 = x_372;
}
lean::cnstr_set(x_374, 0, x_322);
lean::cnstr_set(x_374, 1, x_323);
lean::cnstr_set(x_374, 2, x_324);
lean::cnstr_set(x_374, 3, x_368);
lean::cnstr_set_uint8(x_374, sizeof(void*)*4, x_373);
if (lean::is_scalar(x_367)) {
 x_375 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_375 = x_367;
}
lean::cnstr_set(x_375, 0, x_371);
lean::cnstr_set(x_375, 1, x_364);
lean::cnstr_set(x_375, 2, x_365);
lean::cnstr_set(x_375, 3, x_366);
lean::cnstr_set_uint8(x_375, sizeof(void*)*4, x_373);
x_376 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_376, 0, x_374);
lean::cnstr_set(x_376, 1, x_369);
lean::cnstr_set(x_376, 2, x_370);
lean::cnstr_set(x_376, 3, x_375);
lean::cnstr_set_uint8(x_376, sizeof(void*)*4, x_363);
return x_376;
}
else
{
obj* x_377; 
x_377 = lean::cnstr_get(x_334, 3);
lean::inc(x_377);
if (lean::obj_tag(x_377) == 0)
{
obj* x_378; obj* x_379; obj* x_380; uint8 x_381; obj* x_382; obj* x_383; 
x_378 = lean::cnstr_get(x_334, 1);
lean::inc(x_378);
x_379 = lean::cnstr_get(x_334, 2);
lean::inc(x_379);
if (lean::is_exclusive(x_334)) {
 lean::cnstr_release(x_334, 0);
 lean::cnstr_release(x_334, 1);
 lean::cnstr_release(x_334, 2);
 lean::cnstr_release(x_334, 3);
 x_380 = x_334;
} else {
 lean::dec_ref(x_334);
 x_380 = lean::box(0);
}
x_381 = 0;
if (lean::is_scalar(x_380)) {
 x_382 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_382 = x_380;
}
lean::cnstr_set(x_382, 0, x_335);
lean::cnstr_set(x_382, 1, x_378);
lean::cnstr_set(x_382, 2, x_379);
lean::cnstr_set(x_382, 3, x_377);
lean::cnstr_set_uint8(x_382, sizeof(void*)*4, x_381);
x_383 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_383, 0, x_322);
lean::cnstr_set(x_383, 1, x_323);
lean::cnstr_set(x_383, 2, x_324);
lean::cnstr_set(x_383, 3, x_382);
lean::cnstr_set_uint8(x_383, sizeof(void*)*4, x_363);
return x_383;
}
else
{
uint8 x_384; 
x_384 = lean::cnstr_get_uint8(x_377, sizeof(void*)*4);
if (x_384 == 0)
{
obj* x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; 
x_385 = lean::cnstr_get(x_334, 1);
lean::inc(x_385);
x_386 = lean::cnstr_get(x_334, 2);
lean::inc(x_386);
if (lean::is_exclusive(x_334)) {
 lean::cnstr_release(x_334, 0);
 lean::cnstr_release(x_334, 1);
 lean::cnstr_release(x_334, 2);
 lean::cnstr_release(x_334, 3);
 x_387 = x_334;
} else {
 lean::dec_ref(x_334);
 x_387 = lean::box(0);
}
x_388 = lean::cnstr_get(x_377, 0);
lean::inc(x_388);
x_389 = lean::cnstr_get(x_377, 1);
lean::inc(x_389);
x_390 = lean::cnstr_get(x_377, 2);
lean::inc(x_390);
x_391 = lean::cnstr_get(x_377, 3);
lean::inc(x_391);
if (lean::is_exclusive(x_377)) {
 lean::cnstr_release(x_377, 0);
 lean::cnstr_release(x_377, 1);
 lean::cnstr_release(x_377, 2);
 lean::cnstr_release(x_377, 3);
 x_392 = x_377;
} else {
 lean::dec_ref(x_377);
 x_392 = lean::box(0);
}
lean::inc(x_335);
if (lean::is_scalar(x_392)) {
 x_393 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_393 = x_392;
}
lean::cnstr_set(x_393, 0, x_322);
lean::cnstr_set(x_393, 1, x_323);
lean::cnstr_set(x_393, 2, x_324);
lean::cnstr_set(x_393, 3, x_335);
if (lean::is_exclusive(x_335)) {
 lean::cnstr_release(x_335, 0);
 lean::cnstr_release(x_335, 1);
 lean::cnstr_release(x_335, 2);
 lean::cnstr_release(x_335, 3);
 x_394 = x_335;
} else {
 lean::dec_ref(x_335);
 x_394 = lean::box(0);
}
lean::cnstr_set_uint8(x_393, sizeof(void*)*4, x_363);
if (lean::is_scalar(x_394)) {
 x_395 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_395 = x_394;
}
lean::cnstr_set(x_395, 0, x_388);
lean::cnstr_set(x_395, 1, x_389);
lean::cnstr_set(x_395, 2, x_390);
lean::cnstr_set(x_395, 3, x_391);
lean::cnstr_set_uint8(x_395, sizeof(void*)*4, x_363);
if (lean::is_scalar(x_387)) {
 x_396 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_396 = x_387;
}
lean::cnstr_set(x_396, 0, x_393);
lean::cnstr_set(x_396, 1, x_385);
lean::cnstr_set(x_396, 2, x_386);
lean::cnstr_set(x_396, 3, x_395);
lean::cnstr_set_uint8(x_396, sizeof(void*)*4, x_384);
return x_396;
}
else
{
obj* x_397; obj* x_398; obj* x_399; obj* x_400; obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; uint8 x_406; obj* x_407; obj* x_408; 
x_397 = lean::cnstr_get(x_334, 1);
lean::inc(x_397);
x_398 = lean::cnstr_get(x_334, 2);
lean::inc(x_398);
if (lean::is_exclusive(x_334)) {
 lean::cnstr_release(x_334, 0);
 lean::cnstr_release(x_334, 1);
 lean::cnstr_release(x_334, 2);
 lean::cnstr_release(x_334, 3);
 x_399 = x_334;
} else {
 lean::dec_ref(x_334);
 x_399 = lean::box(0);
}
x_400 = lean::cnstr_get(x_335, 0);
lean::inc(x_400);
x_401 = lean::cnstr_get(x_335, 1);
lean::inc(x_401);
x_402 = lean::cnstr_get(x_335, 2);
lean::inc(x_402);
x_403 = lean::cnstr_get(x_335, 3);
lean::inc(x_403);
if (lean::is_exclusive(x_335)) {
 lean::cnstr_release(x_335, 0);
 lean::cnstr_release(x_335, 1);
 lean::cnstr_release(x_335, 2);
 lean::cnstr_release(x_335, 3);
 x_404 = x_335;
} else {
 lean::dec_ref(x_335);
 x_404 = lean::box(0);
}
if (lean::is_scalar(x_404)) {
 x_405 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_405 = x_404;
}
lean::cnstr_set(x_405, 0, x_400);
lean::cnstr_set(x_405, 1, x_401);
lean::cnstr_set(x_405, 2, x_402);
lean::cnstr_set(x_405, 3, x_403);
lean::cnstr_set_uint8(x_405, sizeof(void*)*4, x_384);
x_406 = 0;
if (lean::is_scalar(x_399)) {
 x_407 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_407 = x_399;
}
lean::cnstr_set(x_407, 0, x_405);
lean::cnstr_set(x_407, 1, x_397);
lean::cnstr_set(x_407, 2, x_398);
lean::cnstr_set(x_407, 3, x_377);
lean::cnstr_set_uint8(x_407, sizeof(void*)*4, x_406);
x_408 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_408, 0, x_322);
lean::cnstr_set(x_408, 1, x_323);
lean::cnstr_set(x_408, 2, x_324);
lean::cnstr_set(x_408, 3, x_407);
lean::cnstr_set_uint8(x_408, sizeof(void*)*4, x_384);
return x_408;
}
}
}
}
}
}
}
}
else
{
uint8 x_409; 
x_409 = l_RBNode_isRed___rarg(x_322);
if (x_409 == 0)
{
obj* x_410; obj* x_411; 
x_410 = l_RBNode_ins___main___rarg(x_1, x_322, x_3, x_4);
x_411 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_411, 0, x_410);
lean::cnstr_set(x_411, 1, x_323);
lean::cnstr_set(x_411, 2, x_324);
lean::cnstr_set(x_411, 3, x_325);
lean::cnstr_set_uint8(x_411, sizeof(void*)*4, x_7);
return x_411;
}
else
{
obj* x_412; 
x_412 = l_RBNode_ins___main___rarg(x_1, x_322, x_3, x_4);
if (lean::obj_tag(x_412) == 0)
{
lean::dec(x_325);
lean::dec(x_324);
lean::dec(x_323);
return x_412;
}
else
{
obj* x_413; 
x_413 = lean::cnstr_get(x_412, 0);
lean::inc(x_413);
if (lean::obj_tag(x_413) == 0)
{
obj* x_414; 
x_414 = lean::cnstr_get(x_412, 3);
lean::inc(x_414);
if (lean::obj_tag(x_414) == 0)
{
obj* x_415; obj* x_416; obj* x_417; uint8 x_418; obj* x_419; uint8 x_420; obj* x_421; 
x_415 = lean::cnstr_get(x_412, 1);
lean::inc(x_415);
x_416 = lean::cnstr_get(x_412, 2);
lean::inc(x_416);
if (lean::is_exclusive(x_412)) {
 lean::cnstr_release(x_412, 0);
 lean::cnstr_release(x_412, 1);
 lean::cnstr_release(x_412, 2);
 lean::cnstr_release(x_412, 3);
 x_417 = x_412;
} else {
 lean::dec_ref(x_412);
 x_417 = lean::box(0);
}
x_418 = 0;
if (lean::is_scalar(x_417)) {
 x_419 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_419 = x_417;
}
lean::cnstr_set(x_419, 0, x_414);
lean::cnstr_set(x_419, 1, x_415);
lean::cnstr_set(x_419, 2, x_416);
lean::cnstr_set(x_419, 3, x_414);
lean::cnstr_set_uint8(x_419, sizeof(void*)*4, x_418);
x_420 = 1;
x_421 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_421, 0, x_419);
lean::cnstr_set(x_421, 1, x_323);
lean::cnstr_set(x_421, 2, x_324);
lean::cnstr_set(x_421, 3, x_325);
lean::cnstr_set_uint8(x_421, sizeof(void*)*4, x_420);
return x_421;
}
else
{
uint8 x_422; 
x_422 = lean::cnstr_get_uint8(x_414, sizeof(void*)*4);
if (x_422 == 0)
{
obj* x_423; obj* x_424; obj* x_425; obj* x_426; obj* x_427; obj* x_428; obj* x_429; obj* x_430; uint8 x_431; obj* x_432; obj* x_433; obj* x_434; 
x_423 = lean::cnstr_get(x_412, 1);
lean::inc(x_423);
x_424 = lean::cnstr_get(x_412, 2);
lean::inc(x_424);
if (lean::is_exclusive(x_412)) {
 lean::cnstr_release(x_412, 0);
 lean::cnstr_release(x_412, 1);
 lean::cnstr_release(x_412, 2);
 lean::cnstr_release(x_412, 3);
 x_425 = x_412;
} else {
 lean::dec_ref(x_412);
 x_425 = lean::box(0);
}
x_426 = lean::cnstr_get(x_414, 0);
lean::inc(x_426);
x_427 = lean::cnstr_get(x_414, 1);
lean::inc(x_427);
x_428 = lean::cnstr_get(x_414, 2);
lean::inc(x_428);
x_429 = lean::cnstr_get(x_414, 3);
lean::inc(x_429);
if (lean::is_exclusive(x_414)) {
 lean::cnstr_release(x_414, 0);
 lean::cnstr_release(x_414, 1);
 lean::cnstr_release(x_414, 2);
 lean::cnstr_release(x_414, 3);
 x_430 = x_414;
} else {
 lean::dec_ref(x_414);
 x_430 = lean::box(0);
}
x_431 = 1;
if (lean::is_scalar(x_430)) {
 x_432 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_432 = x_430;
}
lean::cnstr_set(x_432, 0, x_413);
lean::cnstr_set(x_432, 1, x_423);
lean::cnstr_set(x_432, 2, x_424);
lean::cnstr_set(x_432, 3, x_426);
lean::cnstr_set_uint8(x_432, sizeof(void*)*4, x_431);
if (lean::is_scalar(x_425)) {
 x_433 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_433 = x_425;
}
lean::cnstr_set(x_433, 0, x_429);
lean::cnstr_set(x_433, 1, x_323);
lean::cnstr_set(x_433, 2, x_324);
lean::cnstr_set(x_433, 3, x_325);
lean::cnstr_set_uint8(x_433, sizeof(void*)*4, x_431);
x_434 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_434, 0, x_432);
lean::cnstr_set(x_434, 1, x_427);
lean::cnstr_set(x_434, 2, x_428);
lean::cnstr_set(x_434, 3, x_433);
lean::cnstr_set_uint8(x_434, sizeof(void*)*4, x_422);
return x_434;
}
else
{
obj* x_435; obj* x_436; obj* x_437; uint8 x_438; obj* x_439; obj* x_440; 
x_435 = lean::cnstr_get(x_412, 1);
lean::inc(x_435);
x_436 = lean::cnstr_get(x_412, 2);
lean::inc(x_436);
if (lean::is_exclusive(x_412)) {
 lean::cnstr_release(x_412, 0);
 lean::cnstr_release(x_412, 1);
 lean::cnstr_release(x_412, 2);
 lean::cnstr_release(x_412, 3);
 x_437 = x_412;
} else {
 lean::dec_ref(x_412);
 x_437 = lean::box(0);
}
x_438 = 0;
if (lean::is_scalar(x_437)) {
 x_439 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_439 = x_437;
}
lean::cnstr_set(x_439, 0, x_413);
lean::cnstr_set(x_439, 1, x_435);
lean::cnstr_set(x_439, 2, x_436);
lean::cnstr_set(x_439, 3, x_414);
lean::cnstr_set_uint8(x_439, sizeof(void*)*4, x_438);
x_440 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_440, 0, x_439);
lean::cnstr_set(x_440, 1, x_323);
lean::cnstr_set(x_440, 2, x_324);
lean::cnstr_set(x_440, 3, x_325);
lean::cnstr_set_uint8(x_440, sizeof(void*)*4, x_422);
return x_440;
}
}
}
else
{
uint8 x_441; 
x_441 = lean::cnstr_get_uint8(x_413, sizeof(void*)*4);
if (x_441 == 0)
{
obj* x_442; obj* x_443; obj* x_444; obj* x_445; obj* x_446; obj* x_447; obj* x_448; obj* x_449; obj* x_450; uint8 x_451; obj* x_452; obj* x_453; obj* x_454; 
x_442 = lean::cnstr_get(x_412, 1);
lean::inc(x_442);
x_443 = lean::cnstr_get(x_412, 2);
lean::inc(x_443);
x_444 = lean::cnstr_get(x_412, 3);
lean::inc(x_444);
if (lean::is_exclusive(x_412)) {
 lean::cnstr_release(x_412, 0);
 lean::cnstr_release(x_412, 1);
 lean::cnstr_release(x_412, 2);
 lean::cnstr_release(x_412, 3);
 x_445 = x_412;
} else {
 lean::dec_ref(x_412);
 x_445 = lean::box(0);
}
x_446 = lean::cnstr_get(x_413, 0);
lean::inc(x_446);
x_447 = lean::cnstr_get(x_413, 1);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_413, 2);
lean::inc(x_448);
x_449 = lean::cnstr_get(x_413, 3);
lean::inc(x_449);
if (lean::is_exclusive(x_413)) {
 lean::cnstr_release(x_413, 0);
 lean::cnstr_release(x_413, 1);
 lean::cnstr_release(x_413, 2);
 lean::cnstr_release(x_413, 3);
 x_450 = x_413;
} else {
 lean::dec_ref(x_413);
 x_450 = lean::box(0);
}
x_451 = 1;
if (lean::is_scalar(x_450)) {
 x_452 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_452 = x_450;
}
lean::cnstr_set(x_452, 0, x_446);
lean::cnstr_set(x_452, 1, x_447);
lean::cnstr_set(x_452, 2, x_448);
lean::cnstr_set(x_452, 3, x_449);
lean::cnstr_set_uint8(x_452, sizeof(void*)*4, x_451);
if (lean::is_scalar(x_445)) {
 x_453 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_453 = x_445;
}
lean::cnstr_set(x_453, 0, x_444);
lean::cnstr_set(x_453, 1, x_323);
lean::cnstr_set(x_453, 2, x_324);
lean::cnstr_set(x_453, 3, x_325);
lean::cnstr_set_uint8(x_453, sizeof(void*)*4, x_451);
x_454 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_454, 0, x_452);
lean::cnstr_set(x_454, 1, x_442);
lean::cnstr_set(x_454, 2, x_443);
lean::cnstr_set(x_454, 3, x_453);
lean::cnstr_set_uint8(x_454, sizeof(void*)*4, x_441);
return x_454;
}
else
{
obj* x_455; 
x_455 = lean::cnstr_get(x_412, 3);
lean::inc(x_455);
if (lean::obj_tag(x_455) == 0)
{
obj* x_456; obj* x_457; obj* x_458; uint8 x_459; obj* x_460; obj* x_461; 
x_456 = lean::cnstr_get(x_412, 1);
lean::inc(x_456);
x_457 = lean::cnstr_get(x_412, 2);
lean::inc(x_457);
if (lean::is_exclusive(x_412)) {
 lean::cnstr_release(x_412, 0);
 lean::cnstr_release(x_412, 1);
 lean::cnstr_release(x_412, 2);
 lean::cnstr_release(x_412, 3);
 x_458 = x_412;
} else {
 lean::dec_ref(x_412);
 x_458 = lean::box(0);
}
x_459 = 0;
if (lean::is_scalar(x_458)) {
 x_460 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_460 = x_458;
}
lean::cnstr_set(x_460, 0, x_413);
lean::cnstr_set(x_460, 1, x_456);
lean::cnstr_set(x_460, 2, x_457);
lean::cnstr_set(x_460, 3, x_455);
lean::cnstr_set_uint8(x_460, sizeof(void*)*4, x_459);
x_461 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_461, 0, x_460);
lean::cnstr_set(x_461, 1, x_323);
lean::cnstr_set(x_461, 2, x_324);
lean::cnstr_set(x_461, 3, x_325);
lean::cnstr_set_uint8(x_461, sizeof(void*)*4, x_441);
return x_461;
}
else
{
uint8 x_462; 
x_462 = lean::cnstr_get_uint8(x_455, sizeof(void*)*4);
if (x_462 == 0)
{
obj* x_463; obj* x_464; obj* x_465; obj* x_466; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; 
x_463 = lean::cnstr_get(x_412, 1);
lean::inc(x_463);
x_464 = lean::cnstr_get(x_412, 2);
lean::inc(x_464);
if (lean::is_exclusive(x_412)) {
 lean::cnstr_release(x_412, 0);
 lean::cnstr_release(x_412, 1);
 lean::cnstr_release(x_412, 2);
 lean::cnstr_release(x_412, 3);
 x_465 = x_412;
} else {
 lean::dec_ref(x_412);
 x_465 = lean::box(0);
}
x_466 = lean::cnstr_get(x_455, 0);
lean::inc(x_466);
x_467 = lean::cnstr_get(x_455, 1);
lean::inc(x_467);
x_468 = lean::cnstr_get(x_455, 2);
lean::inc(x_468);
x_469 = lean::cnstr_get(x_455, 3);
lean::inc(x_469);
if (lean::is_exclusive(x_455)) {
 lean::cnstr_release(x_455, 0);
 lean::cnstr_release(x_455, 1);
 lean::cnstr_release(x_455, 2);
 lean::cnstr_release(x_455, 3);
 x_470 = x_455;
} else {
 lean::dec_ref(x_455);
 x_470 = lean::box(0);
}
lean::inc(x_413);
if (lean::is_scalar(x_470)) {
 x_471 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_471 = x_470;
}
lean::cnstr_set(x_471, 0, x_413);
lean::cnstr_set(x_471, 1, x_463);
lean::cnstr_set(x_471, 2, x_464);
lean::cnstr_set(x_471, 3, x_466);
if (lean::is_exclusive(x_413)) {
 lean::cnstr_release(x_413, 0);
 lean::cnstr_release(x_413, 1);
 lean::cnstr_release(x_413, 2);
 lean::cnstr_release(x_413, 3);
 x_472 = x_413;
} else {
 lean::dec_ref(x_413);
 x_472 = lean::box(0);
}
lean::cnstr_set_uint8(x_471, sizeof(void*)*4, x_441);
if (lean::is_scalar(x_472)) {
 x_473 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_473 = x_472;
}
lean::cnstr_set(x_473, 0, x_469);
lean::cnstr_set(x_473, 1, x_323);
lean::cnstr_set(x_473, 2, x_324);
lean::cnstr_set(x_473, 3, x_325);
lean::cnstr_set_uint8(x_473, sizeof(void*)*4, x_441);
if (lean::is_scalar(x_465)) {
 x_474 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_474 = x_465;
}
lean::cnstr_set(x_474, 0, x_471);
lean::cnstr_set(x_474, 1, x_467);
lean::cnstr_set(x_474, 2, x_468);
lean::cnstr_set(x_474, 3, x_473);
lean::cnstr_set_uint8(x_474, sizeof(void*)*4, x_462);
return x_474;
}
else
{
obj* x_475; obj* x_476; obj* x_477; obj* x_478; obj* x_479; obj* x_480; obj* x_481; obj* x_482; obj* x_483; uint8 x_484; obj* x_485; obj* x_486; 
x_475 = lean::cnstr_get(x_412, 1);
lean::inc(x_475);
x_476 = lean::cnstr_get(x_412, 2);
lean::inc(x_476);
if (lean::is_exclusive(x_412)) {
 lean::cnstr_release(x_412, 0);
 lean::cnstr_release(x_412, 1);
 lean::cnstr_release(x_412, 2);
 lean::cnstr_release(x_412, 3);
 x_477 = x_412;
} else {
 lean::dec_ref(x_412);
 x_477 = lean::box(0);
}
x_478 = lean::cnstr_get(x_413, 0);
lean::inc(x_478);
x_479 = lean::cnstr_get(x_413, 1);
lean::inc(x_479);
x_480 = lean::cnstr_get(x_413, 2);
lean::inc(x_480);
x_481 = lean::cnstr_get(x_413, 3);
lean::inc(x_481);
if (lean::is_exclusive(x_413)) {
 lean::cnstr_release(x_413, 0);
 lean::cnstr_release(x_413, 1);
 lean::cnstr_release(x_413, 2);
 lean::cnstr_release(x_413, 3);
 x_482 = x_413;
} else {
 lean::dec_ref(x_413);
 x_482 = lean::box(0);
}
if (lean::is_scalar(x_482)) {
 x_483 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_483 = x_482;
}
lean::cnstr_set(x_483, 0, x_478);
lean::cnstr_set(x_483, 1, x_479);
lean::cnstr_set(x_483, 2, x_480);
lean::cnstr_set(x_483, 3, x_481);
lean::cnstr_set_uint8(x_483, sizeof(void*)*4, x_462);
x_484 = 0;
if (lean::is_scalar(x_477)) {
 x_485 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_485 = x_477;
}
lean::cnstr_set(x_485, 0, x_483);
lean::cnstr_set(x_485, 1, x_475);
lean::cnstr_set(x_485, 2, x_476);
lean::cnstr_set(x_485, 3, x_455);
lean::cnstr_set_uint8(x_485, sizeof(void*)*4, x_484);
x_486 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_486, 0, x_485);
lean::cnstr_set(x_486, 1, x_323);
lean::cnstr_set(x_486, 2, x_324);
lean::cnstr_set(x_486, 3, x_325);
lean::cnstr_set_uint8(x_486, sizeof(void*)*4, x_462);
return x_486;
}
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_ins___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_ins___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_ins___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBNode_ins___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_RBNode_ins(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_ins___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_ins(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_setBlack___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_1;
}
else
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 1;
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_3);
return x_1;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_5);
lean::inc(x_4);
lean::dec(x_1);
x_8 = 1;
x_9 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_5);
lean::cnstr_set(x_9, 2, x_6);
lean::cnstr_set(x_9, 3, x_7);
lean::cnstr_set_uint8(x_9, sizeof(void*)*4, x_8);
return x_9;
}
}
}
}
obj* l_RBNode_setBlack(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_setBlack___rarg), 1, 0);
return x_3;
}
}
obj* l_RBNode_setBlack___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_setBlack(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_insert___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = l_RBNode_isRed___rarg(x_2);
if (x_5 == 0)
{
obj* x_6; 
x_6 = l_RBNode_ins___main___rarg(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
obj* x_7; obj* x_8; 
x_7 = l_RBNode_ins___main___rarg(x_1, x_2, x_3, x_4);
x_8 = l_RBNode_setBlack___rarg(x_7);
return x_8;
}
}
}
obj* l_RBNode_insert(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_insert___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_insert(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_balance_u2083___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; obj* x_6; 
x_5 = 1;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_4);
lean::cnstr_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_uint8(x_4, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_4, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_4);
if (x_10 == 0)
{
obj* x_11; obj* x_12; uint8 x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_4, 3);
lean::dec(x_11);
x_12 = lean::cnstr_get(x_4, 0);
lean::dec(x_12);
lean::cnstr_set(x_4, 0, x_9);
x_13 = 1;
x_14 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_14, 0, x_9);
lean::cnstr_set(x_14, 1, x_2);
lean::cnstr_set(x_14, 2, x_3);
lean::cnstr_set(x_14, 3, x_4);
lean::cnstr_set_uint8(x_14, sizeof(void*)*4, x_13);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_4, 1);
x_16 = lean::cnstr_get(x_4, 2);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_4);
x_17 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_15);
lean::cnstr_set(x_17, 2, x_16);
lean::cnstr_set(x_17, 3, x_9);
lean::cnstr_set_uint8(x_17, sizeof(void*)*4, x_7);
x_18 = 1;
x_19 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_19, 0, x_9);
lean::cnstr_set(x_19, 1, x_2);
lean::cnstr_set(x_19, 2, x_3);
lean::cnstr_set(x_19, 3, x_17);
lean::cnstr_set_uint8(x_19, sizeof(void*)*4, x_18);
return x_19;
}
}
else
{
uint8 x_20; 
x_20 = lean::cnstr_get_uint8(x_9, sizeof(void*)*4);
if (x_20 == 0)
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_4);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; uint8 x_26; 
x_22 = lean::cnstr_get(x_4, 1);
x_23 = lean::cnstr_get(x_4, 2);
x_24 = lean::cnstr_get(x_4, 3);
lean::dec(x_24);
x_25 = lean::cnstr_get(x_4, 0);
lean::dec(x_25);
x_26 = !lean::is_exclusive(x_9);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; uint8 x_31; obj* x_32; 
x_27 = lean::cnstr_get(x_9, 0);
x_28 = lean::cnstr_get(x_9, 1);
x_29 = lean::cnstr_get(x_9, 2);
x_30 = lean::cnstr_get(x_9, 3);
x_31 = 1;
lean::cnstr_set(x_9, 3, x_8);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 1, x_2);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set_uint8(x_9, sizeof(void*)*4, x_31);
lean::cnstr_set(x_4, 3, x_30);
lean::cnstr_set(x_4, 2, x_29);
lean::cnstr_set(x_4, 1, x_28);
lean::cnstr_set(x_4, 0, x_27);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_31);
x_32 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_32, 0, x_9);
lean::cnstr_set(x_32, 1, x_22);
lean::cnstr_set(x_32, 2, x_23);
lean::cnstr_set(x_32, 3, x_4);
lean::cnstr_set_uint8(x_32, sizeof(void*)*4, x_20);
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; uint8 x_37; obj* x_38; obj* x_39; 
x_33 = lean::cnstr_get(x_9, 0);
x_34 = lean::cnstr_get(x_9, 1);
x_35 = lean::cnstr_get(x_9, 2);
x_36 = lean::cnstr_get(x_9, 3);
lean::inc(x_36);
lean::inc(x_35);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_9);
x_37 = 1;
x_38 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_38, 0, x_8);
lean::cnstr_set(x_38, 1, x_2);
lean::cnstr_set(x_38, 2, x_3);
lean::cnstr_set(x_38, 3, x_8);
lean::cnstr_set_uint8(x_38, sizeof(void*)*4, x_37);
lean::cnstr_set(x_4, 3, x_36);
lean::cnstr_set(x_4, 2, x_35);
lean::cnstr_set(x_4, 1, x_34);
lean::cnstr_set(x_4, 0, x_33);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_37);
x_39 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_22);
lean::cnstr_set(x_39, 2, x_23);
lean::cnstr_set(x_39, 3, x_4);
lean::cnstr_set_uint8(x_39, sizeof(void*)*4, x_20);
return x_39;
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; uint8 x_47; obj* x_48; obj* x_49; obj* x_50; 
x_40 = lean::cnstr_get(x_4, 1);
x_41 = lean::cnstr_get(x_4, 2);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_4);
x_42 = lean::cnstr_get(x_9, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_9, 1);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_9, 2);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_9, 3);
lean::inc(x_45);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 lean::cnstr_release(x_9, 3);
 x_46 = x_9;
} else {
 lean::dec_ref(x_9);
 x_46 = lean::box(0);
}
x_47 = 1;
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_8);
lean::cnstr_set(x_48, 1, x_2);
lean::cnstr_set(x_48, 2, x_3);
lean::cnstr_set(x_48, 3, x_8);
lean::cnstr_set_uint8(x_48, sizeof(void*)*4, x_47);
x_49 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_49, 0, x_42);
lean::cnstr_set(x_49, 1, x_43);
lean::cnstr_set(x_49, 2, x_44);
lean::cnstr_set(x_49, 3, x_45);
lean::cnstr_set_uint8(x_49, sizeof(void*)*4, x_47);
x_50 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_40);
lean::cnstr_set(x_50, 2, x_41);
lean::cnstr_set(x_50, 3, x_49);
lean::cnstr_set_uint8(x_50, sizeof(void*)*4, x_20);
return x_50;
}
}
else
{
uint8 x_51; 
x_51 = !lean::is_exclusive(x_9);
if (x_51 == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_52 = lean::cnstr_get(x_9, 3);
lean::dec(x_52);
x_53 = lean::cnstr_get(x_9, 2);
lean::dec(x_53);
x_54 = lean::cnstr_get(x_9, 1);
lean::dec(x_54);
x_55 = lean::cnstr_get(x_9, 0);
lean::dec(x_55);
lean::cnstr_set(x_9, 3, x_4);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 1, x_2);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_56; 
lean::dec(x_9);
x_56 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_56, 0, x_8);
lean::cnstr_set(x_56, 1, x_2);
lean::cnstr_set(x_56, 2, x_3);
lean::cnstr_set(x_56, 3, x_4);
lean::cnstr_set_uint8(x_56, sizeof(void*)*4, x_20);
return x_56;
}
}
}
}
else
{
uint8 x_57; 
x_57 = lean::cnstr_get_uint8(x_8, sizeof(void*)*4);
if (x_57 == 0)
{
obj* x_58; 
x_58 = lean::cnstr_get(x_4, 3);
lean::inc(x_58);
if (lean::obj_tag(x_58) == 0)
{
uint8 x_59; 
x_59 = !lean::is_exclusive(x_4);
if (x_59 == 0)
{
obj* x_60; obj* x_61; uint8 x_62; 
x_60 = lean::cnstr_get(x_4, 3);
lean::dec(x_60);
x_61 = lean::cnstr_get(x_4, 0);
lean::dec(x_61);
x_62 = !lean::is_exclusive(x_8);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; uint8 x_67; obj* x_68; 
x_63 = lean::cnstr_get(x_8, 0);
x_64 = lean::cnstr_get(x_8, 1);
x_65 = lean::cnstr_get(x_8, 2);
x_66 = lean::cnstr_get(x_8, 3);
x_67 = 1;
lean::cnstr_set(x_8, 3, x_63);
lean::cnstr_set(x_8, 2, x_3);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 0, x_58);
lean::cnstr_set_uint8(x_8, sizeof(void*)*4, x_67);
lean::cnstr_set(x_4, 0, x_66);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_67);
x_68 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_68, 0, x_8);
lean::cnstr_set(x_68, 1, x_64);
lean::cnstr_set(x_68, 2, x_65);
lean::cnstr_set(x_68, 3, x_4);
lean::cnstr_set_uint8(x_68, sizeof(void*)*4, x_57);
return x_68;
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; uint8 x_73; obj* x_74; obj* x_75; 
x_69 = lean::cnstr_get(x_8, 0);
x_70 = lean::cnstr_get(x_8, 1);
x_71 = lean::cnstr_get(x_8, 2);
x_72 = lean::cnstr_get(x_8, 3);
lean::inc(x_72);
lean::inc(x_71);
lean::inc(x_70);
lean::inc(x_69);
lean::dec(x_8);
x_73 = 1;
x_74 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_74, 0, x_58);
lean::cnstr_set(x_74, 1, x_2);
lean::cnstr_set(x_74, 2, x_3);
lean::cnstr_set(x_74, 3, x_69);
lean::cnstr_set_uint8(x_74, sizeof(void*)*4, x_73);
lean::cnstr_set(x_4, 0, x_72);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_73);
x_75 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_70);
lean::cnstr_set(x_75, 2, x_71);
lean::cnstr_set(x_75, 3, x_4);
lean::cnstr_set_uint8(x_75, sizeof(void*)*4, x_57);
return x_75;
}
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; 
x_76 = lean::cnstr_get(x_4, 1);
x_77 = lean::cnstr_get(x_4, 2);
lean::inc(x_77);
lean::inc(x_76);
lean::dec(x_4);
x_78 = lean::cnstr_get(x_8, 0);
lean::inc(x_78);
x_79 = lean::cnstr_get(x_8, 1);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_8, 2);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_8, 3);
lean::inc(x_81);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 lean::cnstr_release(x_8, 3);
 x_82 = x_8;
} else {
 lean::dec_ref(x_8);
 x_82 = lean::box(0);
}
x_83 = 1;
if (lean::is_scalar(x_82)) {
 x_84 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_84 = x_82;
}
lean::cnstr_set(x_84, 0, x_58);
lean::cnstr_set(x_84, 1, x_2);
lean::cnstr_set(x_84, 2, x_3);
lean::cnstr_set(x_84, 3, x_78);
lean::cnstr_set_uint8(x_84, sizeof(void*)*4, x_83);
x_85 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set(x_85, 1, x_76);
lean::cnstr_set(x_85, 2, x_77);
lean::cnstr_set(x_85, 3, x_58);
lean::cnstr_set_uint8(x_85, sizeof(void*)*4, x_83);
x_86 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_86, 0, x_84);
lean::cnstr_set(x_86, 1, x_79);
lean::cnstr_set(x_86, 2, x_80);
lean::cnstr_set(x_86, 3, x_85);
lean::cnstr_set_uint8(x_86, sizeof(void*)*4, x_57);
return x_86;
}
}
else
{
uint8 x_87; 
x_87 = lean::cnstr_get_uint8(x_58, sizeof(void*)*4);
if (x_87 == 0)
{
uint8 x_88; 
x_88 = !lean::is_exclusive(x_4);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; uint8 x_93; 
x_89 = lean::cnstr_get(x_4, 1);
x_90 = lean::cnstr_get(x_4, 2);
x_91 = lean::cnstr_get(x_4, 3);
lean::dec(x_91);
x_92 = lean::cnstr_get(x_4, 0);
lean::dec(x_92);
x_93 = !lean::is_exclusive(x_8);
if (x_93 == 0)
{
uint8 x_94; 
x_94 = !lean::is_exclusive(x_58);
if (x_94 == 0)
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; uint8 x_103; obj* x_104; 
x_95 = lean::cnstr_get(x_8, 0);
x_96 = lean::cnstr_get(x_8, 1);
x_97 = lean::cnstr_get(x_8, 2);
x_98 = lean::cnstr_get(x_8, 3);
x_99 = lean::cnstr_get(x_58, 0);
x_100 = lean::cnstr_get(x_58, 1);
x_101 = lean::cnstr_get(x_58, 2);
x_102 = lean::cnstr_get(x_58, 3);
lean::cnstr_set(x_58, 3, x_98);
lean::cnstr_set(x_58, 2, x_97);
lean::cnstr_set(x_58, 1, x_96);
lean::cnstr_set(x_58, 0, x_95);
x_103 = 1;
lean::cnstr_set(x_8, 3, x_58);
lean::cnstr_set(x_8, 2, x_3);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set_uint8(x_8, sizeof(void*)*4, x_103);
lean::cnstr_set(x_4, 3, x_102);
lean::cnstr_set(x_4, 2, x_101);
lean::cnstr_set(x_4, 1, x_100);
lean::cnstr_set(x_4, 0, x_99);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_103);
x_104 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_104, 0, x_8);
lean::cnstr_set(x_104, 1, x_89);
lean::cnstr_set(x_104, 2, x_90);
lean::cnstr_set(x_104, 3, x_4);
lean::cnstr_set_uint8(x_104, sizeof(void*)*4, x_87);
return x_104;
}
else
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; uint8 x_114; obj* x_115; 
x_105 = lean::cnstr_get(x_8, 0);
x_106 = lean::cnstr_get(x_8, 1);
x_107 = lean::cnstr_get(x_8, 2);
x_108 = lean::cnstr_get(x_8, 3);
x_109 = lean::cnstr_get(x_58, 0);
x_110 = lean::cnstr_get(x_58, 1);
x_111 = lean::cnstr_get(x_58, 2);
x_112 = lean::cnstr_get(x_58, 3);
lean::inc(x_112);
lean::inc(x_111);
lean::inc(x_110);
lean::inc(x_109);
lean::dec(x_58);
x_113 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_113, 0, x_105);
lean::cnstr_set(x_113, 1, x_106);
lean::cnstr_set(x_113, 2, x_107);
lean::cnstr_set(x_113, 3, x_108);
lean::cnstr_set_uint8(x_113, sizeof(void*)*4, x_87);
x_114 = 1;
lean::cnstr_set(x_8, 3, x_113);
lean::cnstr_set(x_8, 2, x_3);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set_uint8(x_8, sizeof(void*)*4, x_114);
lean::cnstr_set(x_4, 3, x_112);
lean::cnstr_set(x_4, 2, x_111);
lean::cnstr_set(x_4, 1, x_110);
lean::cnstr_set(x_4, 0, x_109);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_114);
x_115 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_115, 0, x_8);
lean::cnstr_set(x_115, 1, x_89);
lean::cnstr_set(x_115, 2, x_90);
lean::cnstr_set(x_115, 3, x_4);
lean::cnstr_set_uint8(x_115, sizeof(void*)*4, x_87);
return x_115;
}
}
else
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; uint8 x_126; obj* x_127; obj* x_128; 
x_116 = lean::cnstr_get(x_8, 0);
x_117 = lean::cnstr_get(x_8, 1);
x_118 = lean::cnstr_get(x_8, 2);
x_119 = lean::cnstr_get(x_8, 3);
lean::inc(x_119);
lean::inc(x_118);
lean::inc(x_117);
lean::inc(x_116);
lean::dec(x_8);
x_120 = lean::cnstr_get(x_58, 0);
lean::inc(x_120);
x_121 = lean::cnstr_get(x_58, 1);
lean::inc(x_121);
x_122 = lean::cnstr_get(x_58, 2);
lean::inc(x_122);
x_123 = lean::cnstr_get(x_58, 3);
lean::inc(x_123);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 lean::cnstr_release(x_58, 1);
 lean::cnstr_release(x_58, 2);
 lean::cnstr_release(x_58, 3);
 x_124 = x_58;
} else {
 lean::dec_ref(x_58);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_116);
lean::cnstr_set(x_125, 1, x_117);
lean::cnstr_set(x_125, 2, x_118);
lean::cnstr_set(x_125, 3, x_119);
lean::cnstr_set_uint8(x_125, sizeof(void*)*4, x_87);
x_126 = 1;
x_127 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_127, 0, x_1);
lean::cnstr_set(x_127, 1, x_2);
lean::cnstr_set(x_127, 2, x_3);
lean::cnstr_set(x_127, 3, x_125);
lean::cnstr_set_uint8(x_127, sizeof(void*)*4, x_126);
lean::cnstr_set(x_4, 3, x_123);
lean::cnstr_set(x_4, 2, x_122);
lean::cnstr_set(x_4, 1, x_121);
lean::cnstr_set(x_4, 0, x_120);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_126);
x_128 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_89);
lean::cnstr_set(x_128, 2, x_90);
lean::cnstr_set(x_128, 3, x_4);
lean::cnstr_set_uint8(x_128, sizeof(void*)*4, x_87);
return x_128;
}
}
else
{
obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; uint8 x_142; obj* x_143; obj* x_144; obj* x_145; 
x_129 = lean::cnstr_get(x_4, 1);
x_130 = lean::cnstr_get(x_4, 2);
lean::inc(x_130);
lean::inc(x_129);
lean::dec(x_4);
x_131 = lean::cnstr_get(x_8, 0);
lean::inc(x_131);
x_132 = lean::cnstr_get(x_8, 1);
lean::inc(x_132);
x_133 = lean::cnstr_get(x_8, 2);
lean::inc(x_133);
x_134 = lean::cnstr_get(x_8, 3);
lean::inc(x_134);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 lean::cnstr_release(x_8, 3);
 x_135 = x_8;
} else {
 lean::dec_ref(x_8);
 x_135 = lean::box(0);
}
x_136 = lean::cnstr_get(x_58, 0);
lean::inc(x_136);
x_137 = lean::cnstr_get(x_58, 1);
lean::inc(x_137);
x_138 = lean::cnstr_get(x_58, 2);
lean::inc(x_138);
x_139 = lean::cnstr_get(x_58, 3);
lean::inc(x_139);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 lean::cnstr_release(x_58, 1);
 lean::cnstr_release(x_58, 2);
 lean::cnstr_release(x_58, 3);
 x_140 = x_58;
} else {
 lean::dec_ref(x_58);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_131);
lean::cnstr_set(x_141, 1, x_132);
lean::cnstr_set(x_141, 2, x_133);
lean::cnstr_set(x_141, 3, x_134);
lean::cnstr_set_uint8(x_141, sizeof(void*)*4, x_87);
x_142 = 1;
if (lean::is_scalar(x_135)) {
 x_143 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_143 = x_135;
}
lean::cnstr_set(x_143, 0, x_1);
lean::cnstr_set(x_143, 1, x_2);
lean::cnstr_set(x_143, 2, x_3);
lean::cnstr_set(x_143, 3, x_141);
lean::cnstr_set_uint8(x_143, sizeof(void*)*4, x_142);
x_144 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_144, 0, x_136);
lean::cnstr_set(x_144, 1, x_137);
lean::cnstr_set(x_144, 2, x_138);
lean::cnstr_set(x_144, 3, x_139);
lean::cnstr_set_uint8(x_144, sizeof(void*)*4, x_142);
x_145 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_145, 0, x_143);
lean::cnstr_set(x_145, 1, x_129);
lean::cnstr_set(x_145, 2, x_130);
lean::cnstr_set(x_145, 3, x_144);
lean::cnstr_set_uint8(x_145, sizeof(void*)*4, x_87);
return x_145;
}
}
else
{
uint8 x_146; 
x_146 = !lean::is_exclusive(x_4);
if (x_146 == 0)
{
obj* x_147; obj* x_148; uint8 x_149; 
x_147 = lean::cnstr_get(x_4, 3);
lean::dec(x_147);
x_148 = lean::cnstr_get(x_4, 0);
lean::dec(x_148);
x_149 = !lean::is_exclusive(x_8);
if (x_149 == 0)
{
obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; 
x_150 = lean::cnstr_get(x_8, 0);
x_151 = lean::cnstr_get(x_8, 1);
x_152 = lean::cnstr_get(x_8, 2);
x_153 = lean::cnstr_get(x_8, 3);
lean::cnstr_set(x_8, 3, x_150);
lean::cnstr_set(x_8, 2, x_3);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set_uint8(x_8, sizeof(void*)*4, x_87);
lean::cnstr_set(x_4, 0, x_153);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_87);
x_154 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_154, 0, x_8);
lean::cnstr_set(x_154, 1, x_151);
lean::cnstr_set(x_154, 2, x_152);
lean::cnstr_set(x_154, 3, x_4);
lean::cnstr_set_uint8(x_154, sizeof(void*)*4, x_57);
return x_154;
}
else
{
obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
x_155 = lean::cnstr_get(x_8, 0);
x_156 = lean::cnstr_get(x_8, 1);
x_157 = lean::cnstr_get(x_8, 2);
x_158 = lean::cnstr_get(x_8, 3);
lean::inc(x_158);
lean::inc(x_157);
lean::inc(x_156);
lean::inc(x_155);
lean::dec(x_8);
x_159 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_159, 0, x_1);
lean::cnstr_set(x_159, 1, x_2);
lean::cnstr_set(x_159, 2, x_3);
lean::cnstr_set(x_159, 3, x_155);
lean::cnstr_set_uint8(x_159, sizeof(void*)*4, x_87);
lean::cnstr_set(x_4, 0, x_158);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_87);
x_160 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_160, 0, x_159);
lean::cnstr_set(x_160, 1, x_156);
lean::cnstr_set(x_160, 2, x_157);
lean::cnstr_set(x_160, 3, x_4);
lean::cnstr_set_uint8(x_160, sizeof(void*)*4, x_57);
return x_160;
}
}
else
{
obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; 
x_161 = lean::cnstr_get(x_4, 1);
x_162 = lean::cnstr_get(x_4, 2);
lean::inc(x_162);
lean::inc(x_161);
lean::dec(x_4);
x_163 = lean::cnstr_get(x_8, 0);
lean::inc(x_163);
x_164 = lean::cnstr_get(x_8, 1);
lean::inc(x_164);
x_165 = lean::cnstr_get(x_8, 2);
lean::inc(x_165);
x_166 = lean::cnstr_get(x_8, 3);
lean::inc(x_166);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 lean::cnstr_release(x_8, 3);
 x_167 = x_8;
} else {
 lean::dec_ref(x_8);
 x_167 = lean::box(0);
}
if (lean::is_scalar(x_167)) {
 x_168 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_168 = x_167;
}
lean::cnstr_set(x_168, 0, x_1);
lean::cnstr_set(x_168, 1, x_2);
lean::cnstr_set(x_168, 2, x_3);
lean::cnstr_set(x_168, 3, x_163);
lean::cnstr_set_uint8(x_168, sizeof(void*)*4, x_87);
x_169 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_169, 0, x_166);
lean::cnstr_set(x_169, 1, x_161);
lean::cnstr_set(x_169, 2, x_162);
lean::cnstr_set(x_169, 3, x_58);
lean::cnstr_set_uint8(x_169, sizeof(void*)*4, x_87);
x_170 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_170, 0, x_168);
lean::cnstr_set(x_170, 1, x_164);
lean::cnstr_set(x_170, 2, x_165);
lean::cnstr_set(x_170, 3, x_169);
lean::cnstr_set_uint8(x_170, sizeof(void*)*4, x_57);
return x_170;
}
}
}
}
else
{
obj* x_171; 
x_171 = lean::cnstr_get(x_4, 3);
lean::inc(x_171);
if (lean::obj_tag(x_171) == 0)
{
uint8 x_172; 
x_172 = !lean::is_exclusive(x_8);
if (x_172 == 0)
{
obj* x_173; obj* x_174; obj* x_175; obj* x_176; 
x_173 = lean::cnstr_get(x_8, 3);
lean::dec(x_173);
x_174 = lean::cnstr_get(x_8, 2);
lean::dec(x_174);
x_175 = lean::cnstr_get(x_8, 1);
lean::dec(x_175);
x_176 = lean::cnstr_get(x_8, 0);
lean::dec(x_176);
lean::cnstr_set(x_8, 3, x_4);
lean::cnstr_set(x_8, 2, x_3);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 0, x_171);
return x_8;
}
else
{
obj* x_177; 
lean::dec(x_8);
x_177 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_177, 0, x_171);
lean::cnstr_set(x_177, 1, x_2);
lean::cnstr_set(x_177, 2, x_3);
lean::cnstr_set(x_177, 3, x_4);
lean::cnstr_set_uint8(x_177, sizeof(void*)*4, x_57);
return x_177;
}
}
else
{
uint8 x_178; 
x_178 = lean::cnstr_get_uint8(x_171, sizeof(void*)*4);
if (x_178 == 0)
{
uint8 x_179; 
x_179 = !lean::is_exclusive(x_4);
if (x_179 == 0)
{
obj* x_180; obj* x_181; uint8 x_182; 
x_180 = lean::cnstr_get(x_4, 3);
lean::dec(x_180);
x_181 = lean::cnstr_get(x_4, 0);
lean::dec(x_181);
x_182 = !lean::is_exclusive(x_171);
if (x_182 == 0)
{
obj* x_183; obj* x_184; obj* x_185; obj* x_186; uint8 x_187; 
x_183 = lean::cnstr_get(x_171, 0);
x_184 = lean::cnstr_get(x_171, 1);
x_185 = lean::cnstr_get(x_171, 2);
x_186 = lean::cnstr_get(x_171, 3);
lean::inc(x_8);
lean::cnstr_set(x_171, 3, x_8);
lean::cnstr_set(x_171, 2, x_3);
lean::cnstr_set(x_171, 1, x_2);
lean::cnstr_set(x_171, 0, x_1);
x_187 = !lean::is_exclusive(x_8);
if (x_187 == 0)
{
obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
x_188 = lean::cnstr_get(x_8, 3);
lean::dec(x_188);
x_189 = lean::cnstr_get(x_8, 2);
lean::dec(x_189);
x_190 = lean::cnstr_get(x_8, 1);
lean::dec(x_190);
x_191 = lean::cnstr_get(x_8, 0);
lean::dec(x_191);
lean::cnstr_set_uint8(x_171, sizeof(void*)*4, x_57);
lean::cnstr_set(x_8, 3, x_186);
lean::cnstr_set(x_8, 2, x_185);
lean::cnstr_set(x_8, 1, x_184);
lean::cnstr_set(x_8, 0, x_183);
lean::cnstr_set(x_4, 3, x_8);
lean::cnstr_set(x_4, 0, x_171);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_178);
return x_4;
}
else
{
obj* x_192; 
lean::dec(x_8);
lean::cnstr_set_uint8(x_171, sizeof(void*)*4, x_57);
x_192 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_192, 0, x_183);
lean::cnstr_set(x_192, 1, x_184);
lean::cnstr_set(x_192, 2, x_185);
lean::cnstr_set(x_192, 3, x_186);
lean::cnstr_set_uint8(x_192, sizeof(void*)*4, x_57);
lean::cnstr_set(x_4, 3, x_192);
lean::cnstr_set(x_4, 0, x_171);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_178);
return x_4;
}
}
else
{
obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; 
x_193 = lean::cnstr_get(x_171, 0);
x_194 = lean::cnstr_get(x_171, 1);
x_195 = lean::cnstr_get(x_171, 2);
x_196 = lean::cnstr_get(x_171, 3);
lean::inc(x_196);
lean::inc(x_195);
lean::inc(x_194);
lean::inc(x_193);
lean::dec(x_171);
lean::inc(x_8);
x_197 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_197, 0, x_1);
lean::cnstr_set(x_197, 1, x_2);
lean::cnstr_set(x_197, 2, x_3);
lean::cnstr_set(x_197, 3, x_8);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 lean::cnstr_release(x_8, 3);
 x_198 = x_8;
} else {
 lean::dec_ref(x_8);
 x_198 = lean::box(0);
}
lean::cnstr_set_uint8(x_197, sizeof(void*)*4, x_57);
if (lean::is_scalar(x_198)) {
 x_199 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_199 = x_198;
}
lean::cnstr_set(x_199, 0, x_193);
lean::cnstr_set(x_199, 1, x_194);
lean::cnstr_set(x_199, 2, x_195);
lean::cnstr_set(x_199, 3, x_196);
lean::cnstr_set_uint8(x_199, sizeof(void*)*4, x_57);
lean::cnstr_set(x_4, 3, x_199);
lean::cnstr_set(x_4, 0, x_197);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_178);
return x_4;
}
}
else
{
obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
x_200 = lean::cnstr_get(x_4, 1);
x_201 = lean::cnstr_get(x_4, 2);
lean::inc(x_201);
lean::inc(x_200);
lean::dec(x_4);
x_202 = lean::cnstr_get(x_171, 0);
lean::inc(x_202);
x_203 = lean::cnstr_get(x_171, 1);
lean::inc(x_203);
x_204 = lean::cnstr_get(x_171, 2);
lean::inc(x_204);
x_205 = lean::cnstr_get(x_171, 3);
lean::inc(x_205);
if (lean::is_exclusive(x_171)) {
 lean::cnstr_release(x_171, 0);
 lean::cnstr_release(x_171, 1);
 lean::cnstr_release(x_171, 2);
 lean::cnstr_release(x_171, 3);
 x_206 = x_171;
} else {
 lean::dec_ref(x_171);
 x_206 = lean::box(0);
}
lean::inc(x_8);
if (lean::is_scalar(x_206)) {
 x_207 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_207 = x_206;
}
lean::cnstr_set(x_207, 0, x_1);
lean::cnstr_set(x_207, 1, x_2);
lean::cnstr_set(x_207, 2, x_3);
lean::cnstr_set(x_207, 3, x_8);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 lean::cnstr_release(x_8, 3);
 x_208 = x_8;
} else {
 lean::dec_ref(x_8);
 x_208 = lean::box(0);
}
lean::cnstr_set_uint8(x_207, sizeof(void*)*4, x_57);
if (lean::is_scalar(x_208)) {
 x_209 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_209 = x_208;
}
lean::cnstr_set(x_209, 0, x_202);
lean::cnstr_set(x_209, 1, x_203);
lean::cnstr_set(x_209, 2, x_204);
lean::cnstr_set(x_209, 3, x_205);
lean::cnstr_set_uint8(x_209, sizeof(void*)*4, x_57);
x_210 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_210, 0, x_207);
lean::cnstr_set(x_210, 1, x_200);
lean::cnstr_set(x_210, 2, x_201);
lean::cnstr_set(x_210, 3, x_209);
lean::cnstr_set_uint8(x_210, sizeof(void*)*4, x_178);
return x_210;
}
}
else
{
uint8 x_211; 
x_211 = !lean::is_exclusive(x_4);
if (x_211 == 0)
{
obj* x_212; obj* x_213; uint8 x_214; 
x_212 = lean::cnstr_get(x_4, 3);
lean::dec(x_212);
x_213 = lean::cnstr_get(x_4, 0);
lean::dec(x_213);
x_214 = !lean::is_exclusive(x_8);
if (x_214 == 0)
{
obj* x_215; 
lean::cnstr_set_uint8(x_8, sizeof(void*)*4, x_178);
x_215 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_215, 0, x_1);
lean::cnstr_set(x_215, 1, x_2);
lean::cnstr_set(x_215, 2, x_3);
lean::cnstr_set(x_215, 3, x_4);
lean::cnstr_set_uint8(x_215, sizeof(void*)*4, x_178);
return x_215;
}
else
{
obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; 
x_216 = lean::cnstr_get(x_8, 0);
x_217 = lean::cnstr_get(x_8, 1);
x_218 = lean::cnstr_get(x_8, 2);
x_219 = lean::cnstr_get(x_8, 3);
lean::inc(x_219);
lean::inc(x_218);
lean::inc(x_217);
lean::inc(x_216);
lean::dec(x_8);
x_220 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_220, 0, x_216);
lean::cnstr_set(x_220, 1, x_217);
lean::cnstr_set(x_220, 2, x_218);
lean::cnstr_set(x_220, 3, x_219);
lean::cnstr_set_uint8(x_220, sizeof(void*)*4, x_178);
lean::cnstr_set(x_4, 0, x_220);
x_221 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_221, 0, x_1);
lean::cnstr_set(x_221, 1, x_2);
lean::cnstr_set(x_221, 2, x_3);
lean::cnstr_set(x_221, 3, x_4);
lean::cnstr_set_uint8(x_221, sizeof(void*)*4, x_178);
return x_221;
}
}
else
{
obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; 
x_222 = lean::cnstr_get(x_4, 1);
x_223 = lean::cnstr_get(x_4, 2);
lean::inc(x_223);
lean::inc(x_222);
lean::dec(x_4);
x_224 = lean::cnstr_get(x_8, 0);
lean::inc(x_224);
x_225 = lean::cnstr_get(x_8, 1);
lean::inc(x_225);
x_226 = lean::cnstr_get(x_8, 2);
lean::inc(x_226);
x_227 = lean::cnstr_get(x_8, 3);
lean::inc(x_227);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 lean::cnstr_release(x_8, 3);
 x_228 = x_8;
} else {
 lean::dec_ref(x_8);
 x_228 = lean::box(0);
}
if (lean::is_scalar(x_228)) {
 x_229 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_229 = x_228;
}
lean::cnstr_set(x_229, 0, x_224);
lean::cnstr_set(x_229, 1, x_225);
lean::cnstr_set(x_229, 2, x_226);
lean::cnstr_set(x_229, 3, x_227);
lean::cnstr_set_uint8(x_229, sizeof(void*)*4, x_178);
x_230 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_230, 0, x_229);
lean::cnstr_set(x_230, 1, x_222);
lean::cnstr_set(x_230, 2, x_223);
lean::cnstr_set(x_230, 3, x_171);
lean::cnstr_set_uint8(x_230, sizeof(void*)*4, x_7);
x_231 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_231, 0, x_1);
lean::cnstr_set(x_231, 1, x_2);
lean::cnstr_set(x_231, 2, x_3);
lean::cnstr_set(x_231, 3, x_230);
lean::cnstr_set_uint8(x_231, sizeof(void*)*4, x_178);
return x_231;
}
}
}
}
}
}
else
{
obj* x_232; 
x_232 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_232, 0, x_1);
lean::cnstr_set(x_232, 1, x_2);
lean::cnstr_set(x_232, 2, x_3);
lean::cnstr_set(x_232, 3, x_4);
lean::cnstr_set_uint8(x_232, sizeof(void*)*4, x_7);
return x_232;
}
}
}
else
{
uint8 x_233; 
x_233 = lean::cnstr_get_uint8(x_1, sizeof(void*)*4);
if (x_233 == 0)
{
obj* x_234; 
x_234 = lean::cnstr_get(x_1, 0);
lean::inc(x_234);
if (lean::obj_tag(x_234) == 0)
{
obj* x_235; 
x_235 = lean::cnstr_get(x_1, 3);
lean::inc(x_235);
if (lean::obj_tag(x_235) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
uint8 x_236; 
x_236 = !lean::is_exclusive(x_1);
if (x_236 == 0)
{
obj* x_237; obj* x_238; uint8 x_239; obj* x_240; 
x_237 = lean::cnstr_get(x_1, 3);
lean::dec(x_237);
x_238 = lean::cnstr_get(x_1, 0);
lean::dec(x_238);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 0, x_4);
x_239 = 1;
x_240 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_240, 0, x_1);
lean::cnstr_set(x_240, 1, x_2);
lean::cnstr_set(x_240, 2, x_3);
lean::cnstr_set(x_240, 3, x_4);
lean::cnstr_set_uint8(x_240, sizeof(void*)*4, x_239);
return x_240;
}
else
{
obj* x_241; obj* x_242; obj* x_243; uint8 x_244; obj* x_245; 
x_241 = lean::cnstr_get(x_1, 1);
x_242 = lean::cnstr_get(x_1, 2);
lean::inc(x_242);
lean::inc(x_241);
lean::dec(x_1);
x_243 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_243, 0, x_4);
lean::cnstr_set(x_243, 1, x_241);
lean::cnstr_set(x_243, 2, x_242);
lean::cnstr_set(x_243, 3, x_4);
lean::cnstr_set_uint8(x_243, sizeof(void*)*4, x_233);
x_244 = 1;
x_245 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_245, 0, x_243);
lean::cnstr_set(x_245, 1, x_2);
lean::cnstr_set(x_245, 2, x_3);
lean::cnstr_set(x_245, 3, x_4);
lean::cnstr_set_uint8(x_245, sizeof(void*)*4, x_244);
return x_245;
}
}
else
{
uint8 x_246; 
x_246 = lean::cnstr_get_uint8(x_4, sizeof(void*)*4);
if (x_246 == 0)
{
obj* x_247; 
x_247 = lean::cnstr_get(x_4, 0);
lean::inc(x_247);
if (lean::obj_tag(x_247) == 0)
{
obj* x_248; 
x_248 = lean::cnstr_get(x_4, 3);
lean::inc(x_248);
if (lean::obj_tag(x_248) == 0)
{
uint8 x_249; 
x_249 = !lean::is_exclusive(x_1);
if (x_249 == 0)
{
obj* x_250; obj* x_251; obj* x_252; obj* x_253; uint8 x_254; 
x_250 = lean::cnstr_get(x_1, 1);
x_251 = lean::cnstr_get(x_1, 2);
x_252 = lean::cnstr_get(x_1, 3);
lean::dec(x_252);
x_253 = lean::cnstr_get(x_1, 0);
lean::dec(x_253);
x_254 = !lean::is_exclusive(x_4);
if (x_254 == 0)
{
obj* x_255; obj* x_256; obj* x_257; obj* x_258; uint8 x_259; obj* x_260; 
x_255 = lean::cnstr_get(x_4, 1);
x_256 = lean::cnstr_get(x_4, 2);
x_257 = lean::cnstr_get(x_4, 3);
lean::dec(x_257);
x_258 = lean::cnstr_get(x_4, 0);
lean::dec(x_258);
lean::cnstr_set(x_4, 2, x_251);
lean::cnstr_set(x_4, 1, x_250);
lean::cnstr_set(x_4, 0, x_248);
lean::cnstr_set(x_1, 3, x_248);
lean::cnstr_set(x_1, 2, x_256);
lean::cnstr_set(x_1, 1, x_255);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_246);
x_259 = 1;
x_260 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_260, 0, x_4);
lean::cnstr_set(x_260, 1, x_2);
lean::cnstr_set(x_260, 2, x_3);
lean::cnstr_set(x_260, 3, x_1);
lean::cnstr_set_uint8(x_260, sizeof(void*)*4, x_259);
return x_260;
}
else
{
obj* x_261; obj* x_262; obj* x_263; uint8 x_264; obj* x_265; 
x_261 = lean::cnstr_get(x_4, 1);
x_262 = lean::cnstr_get(x_4, 2);
lean::inc(x_262);
lean::inc(x_261);
lean::dec(x_4);
x_263 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_263, 0, x_248);
lean::cnstr_set(x_263, 1, x_250);
lean::cnstr_set(x_263, 2, x_251);
lean::cnstr_set(x_263, 3, x_248);
lean::cnstr_set_uint8(x_263, sizeof(void*)*4, x_246);
lean::cnstr_set(x_1, 3, x_248);
lean::cnstr_set(x_1, 2, x_262);
lean::cnstr_set(x_1, 1, x_261);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_246);
x_264 = 1;
x_265 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_265, 0, x_263);
lean::cnstr_set(x_265, 1, x_2);
lean::cnstr_set(x_265, 2, x_3);
lean::cnstr_set(x_265, 3, x_1);
lean::cnstr_set_uint8(x_265, sizeof(void*)*4, x_264);
return x_265;
}
}
else
{
obj* x_266; obj* x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; uint8 x_273; obj* x_274; 
x_266 = lean::cnstr_get(x_1, 1);
x_267 = lean::cnstr_get(x_1, 2);
lean::inc(x_267);
lean::inc(x_266);
lean::dec(x_1);
x_268 = lean::cnstr_get(x_4, 1);
lean::inc(x_268);
x_269 = lean::cnstr_get(x_4, 2);
lean::inc(x_269);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_270 = x_4;
} else {
 lean::dec_ref(x_4);
 x_270 = lean::box(0);
}
if (lean::is_scalar(x_270)) {
 x_271 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_271 = x_270;
}
lean::cnstr_set(x_271, 0, x_248);
lean::cnstr_set(x_271, 1, x_266);
lean::cnstr_set(x_271, 2, x_267);
lean::cnstr_set(x_271, 3, x_248);
lean::cnstr_set_uint8(x_271, sizeof(void*)*4, x_246);
x_272 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_272, 0, x_248);
lean::cnstr_set(x_272, 1, x_268);
lean::cnstr_set(x_272, 2, x_269);
lean::cnstr_set(x_272, 3, x_248);
lean::cnstr_set_uint8(x_272, sizeof(void*)*4, x_246);
x_273 = 1;
x_274 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_274, 0, x_271);
lean::cnstr_set(x_274, 1, x_2);
lean::cnstr_set(x_274, 2, x_3);
lean::cnstr_set(x_274, 3, x_272);
lean::cnstr_set_uint8(x_274, sizeof(void*)*4, x_273);
return x_274;
}
}
else
{
uint8 x_275; 
x_275 = lean::cnstr_get_uint8(x_248, sizeof(void*)*4);
if (x_275 == 0)
{
uint8 x_276; 
x_276 = !lean::is_exclusive(x_1);
if (x_276 == 0)
{
obj* x_277; obj* x_278; obj* x_279; obj* x_280; uint8 x_281; 
x_277 = lean::cnstr_get(x_1, 1);
x_278 = lean::cnstr_get(x_1, 2);
x_279 = lean::cnstr_get(x_1, 3);
lean::dec(x_279);
x_280 = lean::cnstr_get(x_1, 0);
lean::dec(x_280);
x_281 = !lean::is_exclusive(x_4);
if (x_281 == 0)
{
obj* x_282; obj* x_283; obj* x_284; obj* x_285; uint8 x_286; 
x_282 = lean::cnstr_get(x_4, 1);
x_283 = lean::cnstr_get(x_4, 2);
x_284 = lean::cnstr_get(x_4, 3);
lean::dec(x_284);
x_285 = lean::cnstr_get(x_4, 0);
lean::dec(x_285);
x_286 = !lean::is_exclusive(x_248);
if (x_286 == 0)
{
obj* x_287; obj* x_288; obj* x_289; obj* x_290; uint8 x_291; obj* x_292; 
x_287 = lean::cnstr_get(x_248, 0);
x_288 = lean::cnstr_get(x_248, 1);
x_289 = lean::cnstr_get(x_248, 2);
x_290 = lean::cnstr_get(x_248, 3);
lean::cnstr_set(x_248, 3, x_247);
lean::cnstr_set(x_248, 2, x_278);
lean::cnstr_set(x_248, 1, x_277);
lean::cnstr_set(x_248, 0, x_247);
x_291 = 1;
lean::cnstr_set(x_4, 3, x_247);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_248);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_291);
lean::cnstr_set(x_1, 3, x_290);
lean::cnstr_set(x_1, 2, x_289);
lean::cnstr_set(x_1, 1, x_288);
lean::cnstr_set(x_1, 0, x_287);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_291);
x_292 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_292, 0, x_4);
lean::cnstr_set(x_292, 1, x_282);
lean::cnstr_set(x_292, 2, x_283);
lean::cnstr_set(x_292, 3, x_1);
lean::cnstr_set_uint8(x_292, sizeof(void*)*4, x_275);
return x_292;
}
else
{
obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; uint8 x_298; obj* x_299; 
x_293 = lean::cnstr_get(x_248, 0);
x_294 = lean::cnstr_get(x_248, 1);
x_295 = lean::cnstr_get(x_248, 2);
x_296 = lean::cnstr_get(x_248, 3);
lean::inc(x_296);
lean::inc(x_295);
lean::inc(x_294);
lean::inc(x_293);
lean::dec(x_248);
x_297 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_297, 0, x_247);
lean::cnstr_set(x_297, 1, x_277);
lean::cnstr_set(x_297, 2, x_278);
lean::cnstr_set(x_297, 3, x_247);
lean::cnstr_set_uint8(x_297, sizeof(void*)*4, x_275);
x_298 = 1;
lean::cnstr_set(x_4, 3, x_247);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_297);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_298);
lean::cnstr_set(x_1, 3, x_296);
lean::cnstr_set(x_1, 2, x_295);
lean::cnstr_set(x_1, 1, x_294);
lean::cnstr_set(x_1, 0, x_293);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_298);
x_299 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_299, 0, x_4);
lean::cnstr_set(x_299, 1, x_282);
lean::cnstr_set(x_299, 2, x_283);
lean::cnstr_set(x_299, 3, x_1);
lean::cnstr_set_uint8(x_299, sizeof(void*)*4, x_275);
return x_299;
}
}
else
{
obj* x_300; obj* x_301; obj* x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_306; obj* x_307; uint8 x_308; obj* x_309; obj* x_310; 
x_300 = lean::cnstr_get(x_4, 1);
x_301 = lean::cnstr_get(x_4, 2);
lean::inc(x_301);
lean::inc(x_300);
lean::dec(x_4);
x_302 = lean::cnstr_get(x_248, 0);
lean::inc(x_302);
x_303 = lean::cnstr_get(x_248, 1);
lean::inc(x_303);
x_304 = lean::cnstr_get(x_248, 2);
lean::inc(x_304);
x_305 = lean::cnstr_get(x_248, 3);
lean::inc(x_305);
if (lean::is_exclusive(x_248)) {
 lean::cnstr_release(x_248, 0);
 lean::cnstr_release(x_248, 1);
 lean::cnstr_release(x_248, 2);
 lean::cnstr_release(x_248, 3);
 x_306 = x_248;
} else {
 lean::dec_ref(x_248);
 x_306 = lean::box(0);
}
if (lean::is_scalar(x_306)) {
 x_307 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_307 = x_306;
}
lean::cnstr_set(x_307, 0, x_247);
lean::cnstr_set(x_307, 1, x_277);
lean::cnstr_set(x_307, 2, x_278);
lean::cnstr_set(x_307, 3, x_247);
lean::cnstr_set_uint8(x_307, sizeof(void*)*4, x_275);
x_308 = 1;
x_309 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_309, 0, x_307);
lean::cnstr_set(x_309, 1, x_2);
lean::cnstr_set(x_309, 2, x_3);
lean::cnstr_set(x_309, 3, x_247);
lean::cnstr_set_uint8(x_309, sizeof(void*)*4, x_308);
lean::cnstr_set(x_1, 3, x_305);
lean::cnstr_set(x_1, 2, x_304);
lean::cnstr_set(x_1, 1, x_303);
lean::cnstr_set(x_1, 0, x_302);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_308);
x_310 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_310, 0, x_309);
lean::cnstr_set(x_310, 1, x_300);
lean::cnstr_set(x_310, 2, x_301);
lean::cnstr_set(x_310, 3, x_1);
lean::cnstr_set_uint8(x_310, sizeof(void*)*4, x_275);
return x_310;
}
}
else
{
obj* x_311; obj* x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; uint8 x_322; obj* x_323; obj* x_324; obj* x_325; 
x_311 = lean::cnstr_get(x_1, 1);
x_312 = lean::cnstr_get(x_1, 2);
lean::inc(x_312);
lean::inc(x_311);
lean::dec(x_1);
x_313 = lean::cnstr_get(x_4, 1);
lean::inc(x_313);
x_314 = lean::cnstr_get(x_4, 2);
lean::inc(x_314);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_315 = x_4;
} else {
 lean::dec_ref(x_4);
 x_315 = lean::box(0);
}
x_316 = lean::cnstr_get(x_248, 0);
lean::inc(x_316);
x_317 = lean::cnstr_get(x_248, 1);
lean::inc(x_317);
x_318 = lean::cnstr_get(x_248, 2);
lean::inc(x_318);
x_319 = lean::cnstr_get(x_248, 3);
lean::inc(x_319);
if (lean::is_exclusive(x_248)) {
 lean::cnstr_release(x_248, 0);
 lean::cnstr_release(x_248, 1);
 lean::cnstr_release(x_248, 2);
 lean::cnstr_release(x_248, 3);
 x_320 = x_248;
} else {
 lean::dec_ref(x_248);
 x_320 = lean::box(0);
}
if (lean::is_scalar(x_320)) {
 x_321 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_321 = x_320;
}
lean::cnstr_set(x_321, 0, x_247);
lean::cnstr_set(x_321, 1, x_311);
lean::cnstr_set(x_321, 2, x_312);
lean::cnstr_set(x_321, 3, x_247);
lean::cnstr_set_uint8(x_321, sizeof(void*)*4, x_275);
x_322 = 1;
if (lean::is_scalar(x_315)) {
 x_323 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_323 = x_315;
}
lean::cnstr_set(x_323, 0, x_321);
lean::cnstr_set(x_323, 1, x_2);
lean::cnstr_set(x_323, 2, x_3);
lean::cnstr_set(x_323, 3, x_247);
lean::cnstr_set_uint8(x_323, sizeof(void*)*4, x_322);
x_324 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_324, 0, x_316);
lean::cnstr_set(x_324, 1, x_317);
lean::cnstr_set(x_324, 2, x_318);
lean::cnstr_set(x_324, 3, x_319);
lean::cnstr_set_uint8(x_324, sizeof(void*)*4, x_322);
x_325 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_325, 0, x_323);
lean::cnstr_set(x_325, 1, x_313);
lean::cnstr_set(x_325, 2, x_314);
lean::cnstr_set(x_325, 3, x_324);
lean::cnstr_set_uint8(x_325, sizeof(void*)*4, x_275);
return x_325;
}
}
else
{
uint8 x_326; 
x_326 = !lean::is_exclusive(x_248);
if (x_326 == 0)
{
obj* x_327; obj* x_328; obj* x_329; obj* x_330; uint8 x_331; 
x_327 = lean::cnstr_get(x_248, 3);
lean::dec(x_327);
x_328 = lean::cnstr_get(x_248, 2);
lean::dec(x_328);
x_329 = lean::cnstr_get(x_248, 1);
lean::dec(x_329);
x_330 = lean::cnstr_get(x_248, 0);
lean::dec(x_330);
x_331 = !lean::is_exclusive(x_1);
if (x_331 == 0)
{
obj* x_332; obj* x_333; obj* x_334; obj* x_335; 
x_332 = lean::cnstr_get(x_1, 1);
x_333 = lean::cnstr_get(x_1, 2);
x_334 = lean::cnstr_get(x_1, 3);
lean::dec(x_334);
x_335 = lean::cnstr_get(x_1, 0);
lean::dec(x_335);
lean::cnstr_set(x_248, 3, x_247);
lean::cnstr_set(x_248, 2, x_333);
lean::cnstr_set(x_248, 1, x_332);
lean::cnstr_set(x_248, 0, x_247);
lean::cnstr_set_uint8(x_248, sizeof(void*)*4, x_246);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_248);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_275);
return x_1;
}
else
{
obj* x_336; obj* x_337; obj* x_338; 
x_336 = lean::cnstr_get(x_1, 1);
x_337 = lean::cnstr_get(x_1, 2);
lean::inc(x_337);
lean::inc(x_336);
lean::dec(x_1);
lean::cnstr_set(x_248, 3, x_247);
lean::cnstr_set(x_248, 2, x_337);
lean::cnstr_set(x_248, 1, x_336);
lean::cnstr_set(x_248, 0, x_247);
lean::cnstr_set_uint8(x_248, sizeof(void*)*4, x_246);
x_338 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_338, 0, x_248);
lean::cnstr_set(x_338, 1, x_2);
lean::cnstr_set(x_338, 2, x_3);
lean::cnstr_set(x_338, 3, x_4);
lean::cnstr_set_uint8(x_338, sizeof(void*)*4, x_275);
return x_338;
}
}
else
{
obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; 
lean::dec(x_248);
x_339 = lean::cnstr_get(x_1, 1);
lean::inc(x_339);
x_340 = lean::cnstr_get(x_1, 2);
lean::inc(x_340);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_341 = x_1;
} else {
 lean::dec_ref(x_1);
 x_341 = lean::box(0);
}
x_342 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_342, 0, x_247);
lean::cnstr_set(x_342, 1, x_339);
lean::cnstr_set(x_342, 2, x_340);
lean::cnstr_set(x_342, 3, x_247);
lean::cnstr_set_uint8(x_342, sizeof(void*)*4, x_246);
if (lean::is_scalar(x_341)) {
 x_343 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_343 = x_341;
}
lean::cnstr_set(x_343, 0, x_342);
lean::cnstr_set(x_343, 1, x_2);
lean::cnstr_set(x_343, 2, x_3);
lean::cnstr_set(x_343, 3, x_4);
lean::cnstr_set_uint8(x_343, sizeof(void*)*4, x_275);
return x_343;
}
}
}
}
else
{
uint8 x_344; 
x_344 = lean::cnstr_get_uint8(x_247, sizeof(void*)*4);
if (x_344 == 0)
{
obj* x_345; 
x_345 = lean::cnstr_get(x_4, 3);
lean::inc(x_345);
if (lean::obj_tag(x_345) == 0)
{
uint8 x_346; 
x_346 = !lean::is_exclusive(x_1);
if (x_346 == 0)
{
obj* x_347; obj* x_348; obj* x_349; obj* x_350; uint8 x_351; 
x_347 = lean::cnstr_get(x_1, 1);
x_348 = lean::cnstr_get(x_1, 2);
x_349 = lean::cnstr_get(x_1, 3);
lean::dec(x_349);
x_350 = lean::cnstr_get(x_1, 0);
lean::dec(x_350);
x_351 = !lean::is_exclusive(x_4);
if (x_351 == 0)
{
obj* x_352; obj* x_353; obj* x_354; obj* x_355; uint8 x_356; 
x_352 = lean::cnstr_get(x_4, 1);
x_353 = lean::cnstr_get(x_4, 2);
x_354 = lean::cnstr_get(x_4, 3);
lean::dec(x_354);
x_355 = lean::cnstr_get(x_4, 0);
lean::dec(x_355);
x_356 = !lean::is_exclusive(x_247);
if (x_356 == 0)
{
obj* x_357; obj* x_358; obj* x_359; obj* x_360; uint8 x_361; obj* x_362; 
x_357 = lean::cnstr_get(x_247, 0);
x_358 = lean::cnstr_get(x_247, 1);
x_359 = lean::cnstr_get(x_247, 2);
x_360 = lean::cnstr_get(x_247, 3);
lean::cnstr_set(x_247, 3, x_345);
lean::cnstr_set(x_247, 2, x_348);
lean::cnstr_set(x_247, 1, x_347);
lean::cnstr_set(x_247, 0, x_345);
x_361 = 1;
lean::cnstr_set(x_4, 3, x_357);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_361);
lean::cnstr_set(x_1, 3, x_345);
lean::cnstr_set(x_1, 2, x_353);
lean::cnstr_set(x_1, 1, x_352);
lean::cnstr_set(x_1, 0, x_360);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_361);
x_362 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_362, 0, x_4);
lean::cnstr_set(x_362, 1, x_358);
lean::cnstr_set(x_362, 2, x_359);
lean::cnstr_set(x_362, 3, x_1);
lean::cnstr_set_uint8(x_362, sizeof(void*)*4, x_344);
return x_362;
}
else
{
obj* x_363; obj* x_364; obj* x_365; obj* x_366; obj* x_367; uint8 x_368; obj* x_369; 
x_363 = lean::cnstr_get(x_247, 0);
x_364 = lean::cnstr_get(x_247, 1);
x_365 = lean::cnstr_get(x_247, 2);
x_366 = lean::cnstr_get(x_247, 3);
lean::inc(x_366);
lean::inc(x_365);
lean::inc(x_364);
lean::inc(x_363);
lean::dec(x_247);
x_367 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_367, 0, x_345);
lean::cnstr_set(x_367, 1, x_347);
lean::cnstr_set(x_367, 2, x_348);
lean::cnstr_set(x_367, 3, x_345);
lean::cnstr_set_uint8(x_367, sizeof(void*)*4, x_344);
x_368 = 1;
lean::cnstr_set(x_4, 3, x_363);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_367);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_368);
lean::cnstr_set(x_1, 3, x_345);
lean::cnstr_set(x_1, 2, x_353);
lean::cnstr_set(x_1, 1, x_352);
lean::cnstr_set(x_1, 0, x_366);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_368);
x_369 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_369, 0, x_4);
lean::cnstr_set(x_369, 1, x_364);
lean::cnstr_set(x_369, 2, x_365);
lean::cnstr_set(x_369, 3, x_1);
lean::cnstr_set_uint8(x_369, sizeof(void*)*4, x_344);
return x_369;
}
}
else
{
obj* x_370; obj* x_371; obj* x_372; obj* x_373; obj* x_374; obj* x_375; obj* x_376; obj* x_377; uint8 x_378; obj* x_379; obj* x_380; 
x_370 = lean::cnstr_get(x_4, 1);
x_371 = lean::cnstr_get(x_4, 2);
lean::inc(x_371);
lean::inc(x_370);
lean::dec(x_4);
x_372 = lean::cnstr_get(x_247, 0);
lean::inc(x_372);
x_373 = lean::cnstr_get(x_247, 1);
lean::inc(x_373);
x_374 = lean::cnstr_get(x_247, 2);
lean::inc(x_374);
x_375 = lean::cnstr_get(x_247, 3);
lean::inc(x_375);
if (lean::is_exclusive(x_247)) {
 lean::cnstr_release(x_247, 0);
 lean::cnstr_release(x_247, 1);
 lean::cnstr_release(x_247, 2);
 lean::cnstr_release(x_247, 3);
 x_376 = x_247;
} else {
 lean::dec_ref(x_247);
 x_376 = lean::box(0);
}
if (lean::is_scalar(x_376)) {
 x_377 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_377 = x_376;
}
lean::cnstr_set(x_377, 0, x_345);
lean::cnstr_set(x_377, 1, x_347);
lean::cnstr_set(x_377, 2, x_348);
lean::cnstr_set(x_377, 3, x_345);
lean::cnstr_set_uint8(x_377, sizeof(void*)*4, x_344);
x_378 = 1;
x_379 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_379, 0, x_377);
lean::cnstr_set(x_379, 1, x_2);
lean::cnstr_set(x_379, 2, x_3);
lean::cnstr_set(x_379, 3, x_372);
lean::cnstr_set_uint8(x_379, sizeof(void*)*4, x_378);
lean::cnstr_set(x_1, 3, x_345);
lean::cnstr_set(x_1, 2, x_371);
lean::cnstr_set(x_1, 1, x_370);
lean::cnstr_set(x_1, 0, x_375);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_378);
x_380 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_380, 0, x_379);
lean::cnstr_set(x_380, 1, x_373);
lean::cnstr_set(x_380, 2, x_374);
lean::cnstr_set(x_380, 3, x_1);
lean::cnstr_set_uint8(x_380, sizeof(void*)*4, x_344);
return x_380;
}
}
else
{
obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; obj* x_391; uint8 x_392; obj* x_393; obj* x_394; obj* x_395; 
x_381 = lean::cnstr_get(x_1, 1);
x_382 = lean::cnstr_get(x_1, 2);
lean::inc(x_382);
lean::inc(x_381);
lean::dec(x_1);
x_383 = lean::cnstr_get(x_4, 1);
lean::inc(x_383);
x_384 = lean::cnstr_get(x_4, 2);
lean::inc(x_384);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_385 = x_4;
} else {
 lean::dec_ref(x_4);
 x_385 = lean::box(0);
}
x_386 = lean::cnstr_get(x_247, 0);
lean::inc(x_386);
x_387 = lean::cnstr_get(x_247, 1);
lean::inc(x_387);
x_388 = lean::cnstr_get(x_247, 2);
lean::inc(x_388);
x_389 = lean::cnstr_get(x_247, 3);
lean::inc(x_389);
if (lean::is_exclusive(x_247)) {
 lean::cnstr_release(x_247, 0);
 lean::cnstr_release(x_247, 1);
 lean::cnstr_release(x_247, 2);
 lean::cnstr_release(x_247, 3);
 x_390 = x_247;
} else {
 lean::dec_ref(x_247);
 x_390 = lean::box(0);
}
if (lean::is_scalar(x_390)) {
 x_391 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_391 = x_390;
}
lean::cnstr_set(x_391, 0, x_345);
lean::cnstr_set(x_391, 1, x_381);
lean::cnstr_set(x_391, 2, x_382);
lean::cnstr_set(x_391, 3, x_345);
lean::cnstr_set_uint8(x_391, sizeof(void*)*4, x_344);
x_392 = 1;
if (lean::is_scalar(x_385)) {
 x_393 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_393 = x_385;
}
lean::cnstr_set(x_393, 0, x_391);
lean::cnstr_set(x_393, 1, x_2);
lean::cnstr_set(x_393, 2, x_3);
lean::cnstr_set(x_393, 3, x_386);
lean::cnstr_set_uint8(x_393, sizeof(void*)*4, x_392);
x_394 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_394, 0, x_389);
lean::cnstr_set(x_394, 1, x_383);
lean::cnstr_set(x_394, 2, x_384);
lean::cnstr_set(x_394, 3, x_345);
lean::cnstr_set_uint8(x_394, sizeof(void*)*4, x_392);
x_395 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_395, 0, x_393);
lean::cnstr_set(x_395, 1, x_387);
lean::cnstr_set(x_395, 2, x_388);
lean::cnstr_set(x_395, 3, x_394);
lean::cnstr_set_uint8(x_395, sizeof(void*)*4, x_344);
return x_395;
}
}
else
{
uint8 x_396; 
x_396 = lean::cnstr_get_uint8(x_345, sizeof(void*)*4);
if (x_396 == 0)
{
uint8 x_397; 
x_397 = !lean::is_exclusive(x_1);
if (x_397 == 0)
{
obj* x_398; obj* x_399; obj* x_400; obj* x_401; uint8 x_402; 
x_398 = lean::cnstr_get(x_1, 1);
x_399 = lean::cnstr_get(x_1, 2);
x_400 = lean::cnstr_get(x_1, 3);
lean::dec(x_400);
x_401 = lean::cnstr_get(x_1, 0);
lean::dec(x_401);
x_402 = !lean::is_exclusive(x_4);
if (x_402 == 0)
{
obj* x_403; obj* x_404; obj* x_405; obj* x_406; uint8 x_407; 
x_403 = lean::cnstr_get(x_4, 1);
x_404 = lean::cnstr_get(x_4, 2);
x_405 = lean::cnstr_get(x_4, 3);
lean::dec(x_405);
x_406 = lean::cnstr_get(x_4, 0);
lean::dec(x_406);
x_407 = !lean::is_exclusive(x_247);
if (x_407 == 0)
{
uint8 x_408; 
x_408 = !lean::is_exclusive(x_345);
if (x_408 == 0)
{
obj* x_409; obj* x_410; obj* x_411; obj* x_412; uint8 x_413; obj* x_414; 
x_409 = lean::cnstr_get(x_345, 0);
x_410 = lean::cnstr_get(x_345, 1);
x_411 = lean::cnstr_get(x_345, 2);
x_412 = lean::cnstr_get(x_345, 3);
lean::cnstr_set(x_345, 3, x_235);
lean::cnstr_set(x_345, 2, x_399);
lean::cnstr_set(x_345, 1, x_398);
lean::cnstr_set(x_345, 0, x_235);
lean::cnstr_set_uint8(x_247, sizeof(void*)*4, x_396);
x_413 = 1;
lean::cnstr_set(x_4, 3, x_247);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_345);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_413);
lean::cnstr_set(x_1, 3, x_412);
lean::cnstr_set(x_1, 2, x_411);
lean::cnstr_set(x_1, 1, x_410);
lean::cnstr_set(x_1, 0, x_409);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_413);
x_414 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_414, 0, x_4);
lean::cnstr_set(x_414, 1, x_403);
lean::cnstr_set(x_414, 2, x_404);
lean::cnstr_set(x_414, 3, x_1);
lean::cnstr_set_uint8(x_414, sizeof(void*)*4, x_396);
return x_414;
}
else
{
obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; uint8 x_420; obj* x_421; 
x_415 = lean::cnstr_get(x_345, 0);
x_416 = lean::cnstr_get(x_345, 1);
x_417 = lean::cnstr_get(x_345, 2);
x_418 = lean::cnstr_get(x_345, 3);
lean::inc(x_418);
lean::inc(x_417);
lean::inc(x_416);
lean::inc(x_415);
lean::dec(x_345);
x_419 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_419, 0, x_235);
lean::cnstr_set(x_419, 1, x_398);
lean::cnstr_set(x_419, 2, x_399);
lean::cnstr_set(x_419, 3, x_235);
lean::cnstr_set_uint8(x_419, sizeof(void*)*4, x_396);
lean::cnstr_set_uint8(x_247, sizeof(void*)*4, x_396);
x_420 = 1;
lean::cnstr_set(x_4, 3, x_247);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_419);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_420);
lean::cnstr_set(x_1, 3, x_418);
lean::cnstr_set(x_1, 2, x_417);
lean::cnstr_set(x_1, 1, x_416);
lean::cnstr_set(x_1, 0, x_415);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_420);
x_421 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_421, 0, x_4);
lean::cnstr_set(x_421, 1, x_403);
lean::cnstr_set(x_421, 2, x_404);
lean::cnstr_set(x_421, 3, x_1);
lean::cnstr_set_uint8(x_421, sizeof(void*)*4, x_396);
return x_421;
}
}
else
{
obj* x_422; obj* x_423; obj* x_424; obj* x_425; obj* x_426; obj* x_427; obj* x_428; obj* x_429; obj* x_430; obj* x_431; obj* x_432; uint8 x_433; obj* x_434; 
x_422 = lean::cnstr_get(x_247, 0);
x_423 = lean::cnstr_get(x_247, 1);
x_424 = lean::cnstr_get(x_247, 2);
x_425 = lean::cnstr_get(x_247, 3);
lean::inc(x_425);
lean::inc(x_424);
lean::inc(x_423);
lean::inc(x_422);
lean::dec(x_247);
x_426 = lean::cnstr_get(x_345, 0);
lean::inc(x_426);
x_427 = lean::cnstr_get(x_345, 1);
lean::inc(x_427);
x_428 = lean::cnstr_get(x_345, 2);
lean::inc(x_428);
x_429 = lean::cnstr_get(x_345, 3);
lean::inc(x_429);
if (lean::is_exclusive(x_345)) {
 lean::cnstr_release(x_345, 0);
 lean::cnstr_release(x_345, 1);
 lean::cnstr_release(x_345, 2);
 lean::cnstr_release(x_345, 3);
 x_430 = x_345;
} else {
 lean::dec_ref(x_345);
 x_430 = lean::box(0);
}
if (lean::is_scalar(x_430)) {
 x_431 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_431 = x_430;
}
lean::cnstr_set(x_431, 0, x_235);
lean::cnstr_set(x_431, 1, x_398);
lean::cnstr_set(x_431, 2, x_399);
lean::cnstr_set(x_431, 3, x_235);
lean::cnstr_set_uint8(x_431, sizeof(void*)*4, x_396);
x_432 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_432, 0, x_422);
lean::cnstr_set(x_432, 1, x_423);
lean::cnstr_set(x_432, 2, x_424);
lean::cnstr_set(x_432, 3, x_425);
lean::cnstr_set_uint8(x_432, sizeof(void*)*4, x_396);
x_433 = 1;
lean::cnstr_set(x_4, 3, x_432);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_431);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_433);
lean::cnstr_set(x_1, 3, x_429);
lean::cnstr_set(x_1, 2, x_428);
lean::cnstr_set(x_1, 1, x_427);
lean::cnstr_set(x_1, 0, x_426);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_433);
x_434 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_434, 0, x_4);
lean::cnstr_set(x_434, 1, x_403);
lean::cnstr_set(x_434, 2, x_404);
lean::cnstr_set(x_434, 3, x_1);
lean::cnstr_set_uint8(x_434, sizeof(void*)*4, x_396);
return x_434;
}
}
else
{
obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_441; obj* x_442; obj* x_443; obj* x_444; obj* x_445; obj* x_446; obj* x_447; obj* x_448; uint8 x_449; obj* x_450; obj* x_451; 
x_435 = lean::cnstr_get(x_4, 1);
x_436 = lean::cnstr_get(x_4, 2);
lean::inc(x_436);
lean::inc(x_435);
lean::dec(x_4);
x_437 = lean::cnstr_get(x_247, 0);
lean::inc(x_437);
x_438 = lean::cnstr_get(x_247, 1);
lean::inc(x_438);
x_439 = lean::cnstr_get(x_247, 2);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_247, 3);
lean::inc(x_440);
if (lean::is_exclusive(x_247)) {
 lean::cnstr_release(x_247, 0);
 lean::cnstr_release(x_247, 1);
 lean::cnstr_release(x_247, 2);
 lean::cnstr_release(x_247, 3);
 x_441 = x_247;
} else {
 lean::dec_ref(x_247);
 x_441 = lean::box(0);
}
x_442 = lean::cnstr_get(x_345, 0);
lean::inc(x_442);
x_443 = lean::cnstr_get(x_345, 1);
lean::inc(x_443);
x_444 = lean::cnstr_get(x_345, 2);
lean::inc(x_444);
x_445 = lean::cnstr_get(x_345, 3);
lean::inc(x_445);
if (lean::is_exclusive(x_345)) {
 lean::cnstr_release(x_345, 0);
 lean::cnstr_release(x_345, 1);
 lean::cnstr_release(x_345, 2);
 lean::cnstr_release(x_345, 3);
 x_446 = x_345;
} else {
 lean::dec_ref(x_345);
 x_446 = lean::box(0);
}
if (lean::is_scalar(x_446)) {
 x_447 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_447 = x_446;
}
lean::cnstr_set(x_447, 0, x_235);
lean::cnstr_set(x_447, 1, x_398);
lean::cnstr_set(x_447, 2, x_399);
lean::cnstr_set(x_447, 3, x_235);
lean::cnstr_set_uint8(x_447, sizeof(void*)*4, x_396);
if (lean::is_scalar(x_441)) {
 x_448 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_448 = x_441;
}
lean::cnstr_set(x_448, 0, x_437);
lean::cnstr_set(x_448, 1, x_438);
lean::cnstr_set(x_448, 2, x_439);
lean::cnstr_set(x_448, 3, x_440);
lean::cnstr_set_uint8(x_448, sizeof(void*)*4, x_396);
x_449 = 1;
x_450 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_450, 0, x_447);
lean::cnstr_set(x_450, 1, x_2);
lean::cnstr_set(x_450, 2, x_3);
lean::cnstr_set(x_450, 3, x_448);
lean::cnstr_set_uint8(x_450, sizeof(void*)*4, x_449);
lean::cnstr_set(x_1, 3, x_445);
lean::cnstr_set(x_1, 2, x_444);
lean::cnstr_set(x_1, 1, x_443);
lean::cnstr_set(x_1, 0, x_442);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_449);
x_451 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_451, 0, x_450);
lean::cnstr_set(x_451, 1, x_435);
lean::cnstr_set(x_451, 2, x_436);
lean::cnstr_set(x_451, 3, x_1);
lean::cnstr_set_uint8(x_451, sizeof(void*)*4, x_396);
return x_451;
}
}
else
{
obj* x_452; obj* x_453; obj* x_454; obj* x_455; obj* x_456; obj* x_457; obj* x_458; obj* x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; obj* x_466; obj* x_467; obj* x_468; uint8 x_469; obj* x_470; obj* x_471; obj* x_472; 
x_452 = lean::cnstr_get(x_1, 1);
x_453 = lean::cnstr_get(x_1, 2);
lean::inc(x_453);
lean::inc(x_452);
lean::dec(x_1);
x_454 = lean::cnstr_get(x_4, 1);
lean::inc(x_454);
x_455 = lean::cnstr_get(x_4, 2);
lean::inc(x_455);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_456 = x_4;
} else {
 lean::dec_ref(x_4);
 x_456 = lean::box(0);
}
x_457 = lean::cnstr_get(x_247, 0);
lean::inc(x_457);
x_458 = lean::cnstr_get(x_247, 1);
lean::inc(x_458);
x_459 = lean::cnstr_get(x_247, 2);
lean::inc(x_459);
x_460 = lean::cnstr_get(x_247, 3);
lean::inc(x_460);
if (lean::is_exclusive(x_247)) {
 lean::cnstr_release(x_247, 0);
 lean::cnstr_release(x_247, 1);
 lean::cnstr_release(x_247, 2);
 lean::cnstr_release(x_247, 3);
 x_461 = x_247;
} else {
 lean::dec_ref(x_247);
 x_461 = lean::box(0);
}
x_462 = lean::cnstr_get(x_345, 0);
lean::inc(x_462);
x_463 = lean::cnstr_get(x_345, 1);
lean::inc(x_463);
x_464 = lean::cnstr_get(x_345, 2);
lean::inc(x_464);
x_465 = lean::cnstr_get(x_345, 3);
lean::inc(x_465);
if (lean::is_exclusive(x_345)) {
 lean::cnstr_release(x_345, 0);
 lean::cnstr_release(x_345, 1);
 lean::cnstr_release(x_345, 2);
 lean::cnstr_release(x_345, 3);
 x_466 = x_345;
} else {
 lean::dec_ref(x_345);
 x_466 = lean::box(0);
}
if (lean::is_scalar(x_466)) {
 x_467 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_467 = x_466;
}
lean::cnstr_set(x_467, 0, x_235);
lean::cnstr_set(x_467, 1, x_452);
lean::cnstr_set(x_467, 2, x_453);
lean::cnstr_set(x_467, 3, x_235);
lean::cnstr_set_uint8(x_467, sizeof(void*)*4, x_396);
if (lean::is_scalar(x_461)) {
 x_468 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_468 = x_461;
}
lean::cnstr_set(x_468, 0, x_457);
lean::cnstr_set(x_468, 1, x_458);
lean::cnstr_set(x_468, 2, x_459);
lean::cnstr_set(x_468, 3, x_460);
lean::cnstr_set_uint8(x_468, sizeof(void*)*4, x_396);
x_469 = 1;
if (lean::is_scalar(x_456)) {
 x_470 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_470 = x_456;
}
lean::cnstr_set(x_470, 0, x_467);
lean::cnstr_set(x_470, 1, x_2);
lean::cnstr_set(x_470, 2, x_3);
lean::cnstr_set(x_470, 3, x_468);
lean::cnstr_set_uint8(x_470, sizeof(void*)*4, x_469);
x_471 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_471, 0, x_462);
lean::cnstr_set(x_471, 1, x_463);
lean::cnstr_set(x_471, 2, x_464);
lean::cnstr_set(x_471, 3, x_465);
lean::cnstr_set_uint8(x_471, sizeof(void*)*4, x_469);
x_472 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_472, 0, x_470);
lean::cnstr_set(x_472, 1, x_454);
lean::cnstr_set(x_472, 2, x_455);
lean::cnstr_set(x_472, 3, x_471);
lean::cnstr_set_uint8(x_472, sizeof(void*)*4, x_396);
return x_472;
}
}
else
{
uint8 x_473; 
x_473 = !lean::is_exclusive(x_1);
if (x_473 == 0)
{
obj* x_474; obj* x_475; obj* x_476; obj* x_477; uint8 x_478; 
x_474 = lean::cnstr_get(x_1, 1);
x_475 = lean::cnstr_get(x_1, 2);
x_476 = lean::cnstr_get(x_1, 3);
lean::dec(x_476);
x_477 = lean::cnstr_get(x_1, 0);
lean::dec(x_477);
x_478 = !lean::is_exclusive(x_4);
if (x_478 == 0)
{
obj* x_479; obj* x_480; obj* x_481; obj* x_482; uint8 x_483; 
x_479 = lean::cnstr_get(x_4, 1);
x_480 = lean::cnstr_get(x_4, 2);
x_481 = lean::cnstr_get(x_4, 3);
lean::dec(x_481);
x_482 = lean::cnstr_get(x_4, 0);
lean::dec(x_482);
x_483 = !lean::is_exclusive(x_247);
if (x_483 == 0)
{
obj* x_484; obj* x_485; obj* x_486; obj* x_487; obj* x_488; 
x_484 = lean::cnstr_get(x_247, 0);
x_485 = lean::cnstr_get(x_247, 1);
x_486 = lean::cnstr_get(x_247, 2);
x_487 = lean::cnstr_get(x_247, 3);
lean::cnstr_set(x_247, 3, x_235);
lean::cnstr_set(x_247, 2, x_475);
lean::cnstr_set(x_247, 1, x_474);
lean::cnstr_set(x_247, 0, x_235);
lean::cnstr_set(x_4, 3, x_484);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_396);
lean::cnstr_set(x_1, 3, x_345);
lean::cnstr_set(x_1, 2, x_480);
lean::cnstr_set(x_1, 1, x_479);
lean::cnstr_set(x_1, 0, x_487);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_396);
x_488 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_488, 0, x_4);
lean::cnstr_set(x_488, 1, x_485);
lean::cnstr_set(x_488, 2, x_486);
lean::cnstr_set(x_488, 3, x_1);
lean::cnstr_set_uint8(x_488, sizeof(void*)*4, x_344);
return x_488;
}
else
{
obj* x_489; obj* x_490; obj* x_491; obj* x_492; obj* x_493; obj* x_494; 
x_489 = lean::cnstr_get(x_247, 0);
x_490 = lean::cnstr_get(x_247, 1);
x_491 = lean::cnstr_get(x_247, 2);
x_492 = lean::cnstr_get(x_247, 3);
lean::inc(x_492);
lean::inc(x_491);
lean::inc(x_490);
lean::inc(x_489);
lean::dec(x_247);
x_493 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_493, 0, x_235);
lean::cnstr_set(x_493, 1, x_474);
lean::cnstr_set(x_493, 2, x_475);
lean::cnstr_set(x_493, 3, x_235);
lean::cnstr_set_uint8(x_493, sizeof(void*)*4, x_344);
lean::cnstr_set(x_4, 3, x_489);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_493);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_396);
lean::cnstr_set(x_1, 3, x_345);
lean::cnstr_set(x_1, 2, x_480);
lean::cnstr_set(x_1, 1, x_479);
lean::cnstr_set(x_1, 0, x_492);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_396);
x_494 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_494, 0, x_4);
lean::cnstr_set(x_494, 1, x_490);
lean::cnstr_set(x_494, 2, x_491);
lean::cnstr_set(x_494, 3, x_1);
lean::cnstr_set_uint8(x_494, sizeof(void*)*4, x_344);
return x_494;
}
}
else
{
obj* x_495; obj* x_496; obj* x_497; obj* x_498; obj* x_499; obj* x_500; obj* x_501; obj* x_502; obj* x_503; obj* x_504; 
x_495 = lean::cnstr_get(x_4, 1);
x_496 = lean::cnstr_get(x_4, 2);
lean::inc(x_496);
lean::inc(x_495);
lean::dec(x_4);
x_497 = lean::cnstr_get(x_247, 0);
lean::inc(x_497);
x_498 = lean::cnstr_get(x_247, 1);
lean::inc(x_498);
x_499 = lean::cnstr_get(x_247, 2);
lean::inc(x_499);
x_500 = lean::cnstr_get(x_247, 3);
lean::inc(x_500);
if (lean::is_exclusive(x_247)) {
 lean::cnstr_release(x_247, 0);
 lean::cnstr_release(x_247, 1);
 lean::cnstr_release(x_247, 2);
 lean::cnstr_release(x_247, 3);
 x_501 = x_247;
} else {
 lean::dec_ref(x_247);
 x_501 = lean::box(0);
}
if (lean::is_scalar(x_501)) {
 x_502 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_502 = x_501;
}
lean::cnstr_set(x_502, 0, x_235);
lean::cnstr_set(x_502, 1, x_474);
lean::cnstr_set(x_502, 2, x_475);
lean::cnstr_set(x_502, 3, x_235);
lean::cnstr_set_uint8(x_502, sizeof(void*)*4, x_344);
x_503 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_503, 0, x_502);
lean::cnstr_set(x_503, 1, x_2);
lean::cnstr_set(x_503, 2, x_3);
lean::cnstr_set(x_503, 3, x_497);
lean::cnstr_set_uint8(x_503, sizeof(void*)*4, x_396);
lean::cnstr_set(x_1, 3, x_345);
lean::cnstr_set(x_1, 2, x_496);
lean::cnstr_set(x_1, 1, x_495);
lean::cnstr_set(x_1, 0, x_500);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_396);
x_504 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_504, 0, x_503);
lean::cnstr_set(x_504, 1, x_498);
lean::cnstr_set(x_504, 2, x_499);
lean::cnstr_set(x_504, 3, x_1);
lean::cnstr_set_uint8(x_504, sizeof(void*)*4, x_344);
return x_504;
}
}
else
{
obj* x_505; obj* x_506; obj* x_507; obj* x_508; obj* x_509; obj* x_510; obj* x_511; obj* x_512; obj* x_513; obj* x_514; obj* x_515; obj* x_516; obj* x_517; obj* x_518; 
x_505 = lean::cnstr_get(x_1, 1);
x_506 = lean::cnstr_get(x_1, 2);
lean::inc(x_506);
lean::inc(x_505);
lean::dec(x_1);
x_507 = lean::cnstr_get(x_4, 1);
lean::inc(x_507);
x_508 = lean::cnstr_get(x_4, 2);
lean::inc(x_508);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_509 = x_4;
} else {
 lean::dec_ref(x_4);
 x_509 = lean::box(0);
}
x_510 = lean::cnstr_get(x_247, 0);
lean::inc(x_510);
x_511 = lean::cnstr_get(x_247, 1);
lean::inc(x_511);
x_512 = lean::cnstr_get(x_247, 2);
lean::inc(x_512);
x_513 = lean::cnstr_get(x_247, 3);
lean::inc(x_513);
if (lean::is_exclusive(x_247)) {
 lean::cnstr_release(x_247, 0);
 lean::cnstr_release(x_247, 1);
 lean::cnstr_release(x_247, 2);
 lean::cnstr_release(x_247, 3);
 x_514 = x_247;
} else {
 lean::dec_ref(x_247);
 x_514 = lean::box(0);
}
if (lean::is_scalar(x_514)) {
 x_515 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_515 = x_514;
}
lean::cnstr_set(x_515, 0, x_235);
lean::cnstr_set(x_515, 1, x_505);
lean::cnstr_set(x_515, 2, x_506);
lean::cnstr_set(x_515, 3, x_235);
lean::cnstr_set_uint8(x_515, sizeof(void*)*4, x_344);
if (lean::is_scalar(x_509)) {
 x_516 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_516 = x_509;
}
lean::cnstr_set(x_516, 0, x_515);
lean::cnstr_set(x_516, 1, x_2);
lean::cnstr_set(x_516, 2, x_3);
lean::cnstr_set(x_516, 3, x_510);
lean::cnstr_set_uint8(x_516, sizeof(void*)*4, x_396);
x_517 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_517, 0, x_513);
lean::cnstr_set(x_517, 1, x_507);
lean::cnstr_set(x_517, 2, x_508);
lean::cnstr_set(x_517, 3, x_345);
lean::cnstr_set_uint8(x_517, sizeof(void*)*4, x_396);
x_518 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_518, 0, x_516);
lean::cnstr_set(x_518, 1, x_511);
lean::cnstr_set(x_518, 2, x_512);
lean::cnstr_set(x_518, 3, x_517);
lean::cnstr_set_uint8(x_518, sizeof(void*)*4, x_344);
return x_518;
}
}
}
}
else
{
obj* x_519; 
x_519 = lean::cnstr_get(x_4, 3);
lean::inc(x_519);
if (lean::obj_tag(x_519) == 0)
{
uint8 x_520; 
x_520 = !lean::is_exclusive(x_247);
if (x_520 == 0)
{
obj* x_521; obj* x_522; obj* x_523; obj* x_524; uint8 x_525; 
x_521 = lean::cnstr_get(x_247, 3);
lean::dec(x_521);
x_522 = lean::cnstr_get(x_247, 2);
lean::dec(x_522);
x_523 = lean::cnstr_get(x_247, 1);
lean::dec(x_523);
x_524 = lean::cnstr_get(x_247, 0);
lean::dec(x_524);
x_525 = !lean::is_exclusive(x_1);
if (x_525 == 0)
{
obj* x_526; obj* x_527; obj* x_528; obj* x_529; 
x_526 = lean::cnstr_get(x_1, 1);
x_527 = lean::cnstr_get(x_1, 2);
x_528 = lean::cnstr_get(x_1, 3);
lean::dec(x_528);
x_529 = lean::cnstr_get(x_1, 0);
lean::dec(x_529);
lean::cnstr_set(x_247, 3, x_519);
lean::cnstr_set(x_247, 2, x_527);
lean::cnstr_set(x_247, 1, x_526);
lean::cnstr_set(x_247, 0, x_519);
lean::cnstr_set_uint8(x_247, sizeof(void*)*4, x_246);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_247);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_344);
return x_1;
}
else
{
obj* x_530; obj* x_531; obj* x_532; 
x_530 = lean::cnstr_get(x_1, 1);
x_531 = lean::cnstr_get(x_1, 2);
lean::inc(x_531);
lean::inc(x_530);
lean::dec(x_1);
lean::cnstr_set(x_247, 3, x_519);
lean::cnstr_set(x_247, 2, x_531);
lean::cnstr_set(x_247, 1, x_530);
lean::cnstr_set(x_247, 0, x_519);
lean::cnstr_set_uint8(x_247, sizeof(void*)*4, x_246);
x_532 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_532, 0, x_247);
lean::cnstr_set(x_532, 1, x_2);
lean::cnstr_set(x_532, 2, x_3);
lean::cnstr_set(x_532, 3, x_4);
lean::cnstr_set_uint8(x_532, sizeof(void*)*4, x_344);
return x_532;
}
}
else
{
obj* x_533; obj* x_534; obj* x_535; obj* x_536; obj* x_537; 
lean::dec(x_247);
x_533 = lean::cnstr_get(x_1, 1);
lean::inc(x_533);
x_534 = lean::cnstr_get(x_1, 2);
lean::inc(x_534);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_535 = x_1;
} else {
 lean::dec_ref(x_1);
 x_535 = lean::box(0);
}
x_536 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_536, 0, x_519);
lean::cnstr_set(x_536, 1, x_533);
lean::cnstr_set(x_536, 2, x_534);
lean::cnstr_set(x_536, 3, x_519);
lean::cnstr_set_uint8(x_536, sizeof(void*)*4, x_246);
if (lean::is_scalar(x_535)) {
 x_537 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_537 = x_535;
}
lean::cnstr_set(x_537, 0, x_536);
lean::cnstr_set(x_537, 1, x_2);
lean::cnstr_set(x_537, 2, x_3);
lean::cnstr_set(x_537, 3, x_4);
lean::cnstr_set_uint8(x_537, sizeof(void*)*4, x_344);
return x_537;
}
}
else
{
uint8 x_538; 
x_538 = lean::cnstr_get_uint8(x_519, sizeof(void*)*4);
if (x_538 == 0)
{
uint8 x_539; 
x_539 = !lean::is_exclusive(x_1);
if (x_539 == 0)
{
obj* x_540; obj* x_541; obj* x_542; obj* x_543; uint8 x_544; 
x_540 = lean::cnstr_get(x_1, 1);
x_541 = lean::cnstr_get(x_1, 2);
x_542 = lean::cnstr_get(x_1, 3);
lean::dec(x_542);
x_543 = lean::cnstr_get(x_1, 0);
lean::dec(x_543);
x_544 = !lean::is_exclusive(x_4);
if (x_544 == 0)
{
obj* x_545; obj* x_546; obj* x_547; obj* x_548; uint8 x_549; 
x_545 = lean::cnstr_get(x_4, 1);
x_546 = lean::cnstr_get(x_4, 2);
x_547 = lean::cnstr_get(x_4, 3);
lean::dec(x_547);
x_548 = lean::cnstr_get(x_4, 0);
lean::dec(x_548);
x_549 = !lean::is_exclusive(x_519);
if (x_549 == 0)
{
obj* x_550; obj* x_551; obj* x_552; obj* x_553; obj* x_554; 
x_550 = lean::cnstr_get(x_519, 0);
x_551 = lean::cnstr_get(x_519, 1);
x_552 = lean::cnstr_get(x_519, 2);
x_553 = lean::cnstr_get(x_519, 3);
lean::cnstr_set(x_519, 3, x_235);
lean::cnstr_set(x_519, 2, x_541);
lean::cnstr_set(x_519, 1, x_540);
lean::cnstr_set(x_519, 0, x_235);
lean::cnstr_set(x_4, 3, x_247);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_519);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_344);
lean::cnstr_set(x_1, 3, x_553);
lean::cnstr_set(x_1, 2, x_552);
lean::cnstr_set(x_1, 1, x_551);
lean::cnstr_set(x_1, 0, x_550);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_344);
x_554 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_554, 0, x_4);
lean::cnstr_set(x_554, 1, x_545);
lean::cnstr_set(x_554, 2, x_546);
lean::cnstr_set(x_554, 3, x_1);
lean::cnstr_set_uint8(x_554, sizeof(void*)*4, x_538);
return x_554;
}
else
{
obj* x_555; obj* x_556; obj* x_557; obj* x_558; obj* x_559; obj* x_560; 
x_555 = lean::cnstr_get(x_519, 0);
x_556 = lean::cnstr_get(x_519, 1);
x_557 = lean::cnstr_get(x_519, 2);
x_558 = lean::cnstr_get(x_519, 3);
lean::inc(x_558);
lean::inc(x_557);
lean::inc(x_556);
lean::inc(x_555);
lean::dec(x_519);
x_559 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_559, 0, x_235);
lean::cnstr_set(x_559, 1, x_540);
lean::cnstr_set(x_559, 2, x_541);
lean::cnstr_set(x_559, 3, x_235);
lean::cnstr_set_uint8(x_559, sizeof(void*)*4, x_538);
lean::cnstr_set(x_4, 3, x_247);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_559);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_344);
lean::cnstr_set(x_1, 3, x_558);
lean::cnstr_set(x_1, 2, x_557);
lean::cnstr_set(x_1, 1, x_556);
lean::cnstr_set(x_1, 0, x_555);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_344);
x_560 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_560, 0, x_4);
lean::cnstr_set(x_560, 1, x_545);
lean::cnstr_set(x_560, 2, x_546);
lean::cnstr_set(x_560, 3, x_1);
lean::cnstr_set_uint8(x_560, sizeof(void*)*4, x_538);
return x_560;
}
}
else
{
obj* x_561; obj* x_562; obj* x_563; obj* x_564; obj* x_565; obj* x_566; obj* x_567; obj* x_568; obj* x_569; obj* x_570; 
x_561 = lean::cnstr_get(x_4, 1);
x_562 = lean::cnstr_get(x_4, 2);
lean::inc(x_562);
lean::inc(x_561);
lean::dec(x_4);
x_563 = lean::cnstr_get(x_519, 0);
lean::inc(x_563);
x_564 = lean::cnstr_get(x_519, 1);
lean::inc(x_564);
x_565 = lean::cnstr_get(x_519, 2);
lean::inc(x_565);
x_566 = lean::cnstr_get(x_519, 3);
lean::inc(x_566);
if (lean::is_exclusive(x_519)) {
 lean::cnstr_release(x_519, 0);
 lean::cnstr_release(x_519, 1);
 lean::cnstr_release(x_519, 2);
 lean::cnstr_release(x_519, 3);
 x_567 = x_519;
} else {
 lean::dec_ref(x_519);
 x_567 = lean::box(0);
}
if (lean::is_scalar(x_567)) {
 x_568 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_568 = x_567;
}
lean::cnstr_set(x_568, 0, x_235);
lean::cnstr_set(x_568, 1, x_540);
lean::cnstr_set(x_568, 2, x_541);
lean::cnstr_set(x_568, 3, x_235);
lean::cnstr_set_uint8(x_568, sizeof(void*)*4, x_538);
x_569 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_569, 0, x_568);
lean::cnstr_set(x_569, 1, x_2);
lean::cnstr_set(x_569, 2, x_3);
lean::cnstr_set(x_569, 3, x_247);
lean::cnstr_set_uint8(x_569, sizeof(void*)*4, x_344);
lean::cnstr_set(x_1, 3, x_566);
lean::cnstr_set(x_1, 2, x_565);
lean::cnstr_set(x_1, 1, x_564);
lean::cnstr_set(x_1, 0, x_563);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_344);
x_570 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_570, 0, x_569);
lean::cnstr_set(x_570, 1, x_561);
lean::cnstr_set(x_570, 2, x_562);
lean::cnstr_set(x_570, 3, x_1);
lean::cnstr_set_uint8(x_570, sizeof(void*)*4, x_538);
return x_570;
}
}
else
{
obj* x_571; obj* x_572; obj* x_573; obj* x_574; obj* x_575; obj* x_576; obj* x_577; obj* x_578; obj* x_579; obj* x_580; obj* x_581; obj* x_582; obj* x_583; obj* x_584; 
x_571 = lean::cnstr_get(x_1, 1);
x_572 = lean::cnstr_get(x_1, 2);
lean::inc(x_572);
lean::inc(x_571);
lean::dec(x_1);
x_573 = lean::cnstr_get(x_4, 1);
lean::inc(x_573);
x_574 = lean::cnstr_get(x_4, 2);
lean::inc(x_574);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_575 = x_4;
} else {
 lean::dec_ref(x_4);
 x_575 = lean::box(0);
}
x_576 = lean::cnstr_get(x_519, 0);
lean::inc(x_576);
x_577 = lean::cnstr_get(x_519, 1);
lean::inc(x_577);
x_578 = lean::cnstr_get(x_519, 2);
lean::inc(x_578);
x_579 = lean::cnstr_get(x_519, 3);
lean::inc(x_579);
if (lean::is_exclusive(x_519)) {
 lean::cnstr_release(x_519, 0);
 lean::cnstr_release(x_519, 1);
 lean::cnstr_release(x_519, 2);
 lean::cnstr_release(x_519, 3);
 x_580 = x_519;
} else {
 lean::dec_ref(x_519);
 x_580 = lean::box(0);
}
if (lean::is_scalar(x_580)) {
 x_581 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_581 = x_580;
}
lean::cnstr_set(x_581, 0, x_235);
lean::cnstr_set(x_581, 1, x_571);
lean::cnstr_set(x_581, 2, x_572);
lean::cnstr_set(x_581, 3, x_235);
lean::cnstr_set_uint8(x_581, sizeof(void*)*4, x_538);
if (lean::is_scalar(x_575)) {
 x_582 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_582 = x_575;
}
lean::cnstr_set(x_582, 0, x_581);
lean::cnstr_set(x_582, 1, x_2);
lean::cnstr_set(x_582, 2, x_3);
lean::cnstr_set(x_582, 3, x_247);
lean::cnstr_set_uint8(x_582, sizeof(void*)*4, x_344);
x_583 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_583, 0, x_576);
lean::cnstr_set(x_583, 1, x_577);
lean::cnstr_set(x_583, 2, x_578);
lean::cnstr_set(x_583, 3, x_579);
lean::cnstr_set_uint8(x_583, sizeof(void*)*4, x_344);
x_584 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_584, 0, x_582);
lean::cnstr_set(x_584, 1, x_573);
lean::cnstr_set(x_584, 2, x_574);
lean::cnstr_set(x_584, 3, x_583);
lean::cnstr_set_uint8(x_584, sizeof(void*)*4, x_538);
return x_584;
}
}
else
{
uint8 x_585; 
x_585 = !lean::is_exclusive(x_1);
if (x_585 == 0)
{
obj* x_586; obj* x_587; obj* x_588; obj* x_589; uint8 x_590; 
x_586 = lean::cnstr_get(x_1, 1);
x_587 = lean::cnstr_get(x_1, 2);
x_588 = lean::cnstr_get(x_1, 3);
lean::dec(x_588);
x_589 = lean::cnstr_get(x_1, 0);
lean::dec(x_589);
x_590 = !lean::is_exclusive(x_4);
if (x_590 == 0)
{
obj* x_591; obj* x_592; obj* x_593; obj* x_594; uint8 x_595; 
x_591 = lean::cnstr_get(x_4, 1);
x_592 = lean::cnstr_get(x_4, 2);
x_593 = lean::cnstr_get(x_4, 3);
lean::dec(x_593);
x_594 = lean::cnstr_get(x_4, 0);
lean::dec(x_594);
x_595 = !lean::is_exclusive(x_247);
if (x_595 == 0)
{
obj* x_596; obj* x_597; obj* x_598; obj* x_599; obj* x_600; 
x_596 = lean::cnstr_get(x_247, 0);
x_597 = lean::cnstr_get(x_247, 1);
x_598 = lean::cnstr_get(x_247, 2);
x_599 = lean::cnstr_get(x_247, 3);
lean::cnstr_set(x_247, 3, x_235);
lean::cnstr_set(x_247, 2, x_587);
lean::cnstr_set(x_247, 1, x_586);
lean::cnstr_set(x_247, 0, x_235);
lean::cnstr_set_uint8(x_247, sizeof(void*)*4, x_246);
lean::cnstr_set(x_4, 3, x_599);
lean::cnstr_set(x_4, 2, x_598);
lean::cnstr_set(x_4, 1, x_597);
lean::cnstr_set(x_4, 0, x_596);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_538);
lean::cnstr_set(x_1, 3, x_519);
lean::cnstr_set(x_1, 2, x_592);
lean::cnstr_set(x_1, 1, x_591);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_246);
x_600 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_600, 0, x_247);
lean::cnstr_set(x_600, 1, x_2);
lean::cnstr_set(x_600, 2, x_3);
lean::cnstr_set(x_600, 3, x_1);
lean::cnstr_set_uint8(x_600, sizeof(void*)*4, x_538);
return x_600;
}
else
{
obj* x_601; obj* x_602; obj* x_603; obj* x_604; obj* x_605; obj* x_606; 
x_601 = lean::cnstr_get(x_247, 0);
x_602 = lean::cnstr_get(x_247, 1);
x_603 = lean::cnstr_get(x_247, 2);
x_604 = lean::cnstr_get(x_247, 3);
lean::inc(x_604);
lean::inc(x_603);
lean::inc(x_602);
lean::inc(x_601);
lean::dec(x_247);
x_605 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_605, 0, x_235);
lean::cnstr_set(x_605, 1, x_586);
lean::cnstr_set(x_605, 2, x_587);
lean::cnstr_set(x_605, 3, x_235);
lean::cnstr_set_uint8(x_605, sizeof(void*)*4, x_246);
lean::cnstr_set(x_4, 3, x_604);
lean::cnstr_set(x_4, 2, x_603);
lean::cnstr_set(x_4, 1, x_602);
lean::cnstr_set(x_4, 0, x_601);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_538);
lean::cnstr_set(x_1, 3, x_519);
lean::cnstr_set(x_1, 2, x_592);
lean::cnstr_set(x_1, 1, x_591);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_246);
x_606 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_606, 0, x_605);
lean::cnstr_set(x_606, 1, x_2);
lean::cnstr_set(x_606, 2, x_3);
lean::cnstr_set(x_606, 3, x_1);
lean::cnstr_set_uint8(x_606, sizeof(void*)*4, x_538);
return x_606;
}
}
else
{
obj* x_607; obj* x_608; obj* x_609; obj* x_610; obj* x_611; obj* x_612; obj* x_613; obj* x_614; obj* x_615; obj* x_616; 
x_607 = lean::cnstr_get(x_4, 1);
x_608 = lean::cnstr_get(x_4, 2);
lean::inc(x_608);
lean::inc(x_607);
lean::dec(x_4);
x_609 = lean::cnstr_get(x_247, 0);
lean::inc(x_609);
x_610 = lean::cnstr_get(x_247, 1);
lean::inc(x_610);
x_611 = lean::cnstr_get(x_247, 2);
lean::inc(x_611);
x_612 = lean::cnstr_get(x_247, 3);
lean::inc(x_612);
if (lean::is_exclusive(x_247)) {
 lean::cnstr_release(x_247, 0);
 lean::cnstr_release(x_247, 1);
 lean::cnstr_release(x_247, 2);
 lean::cnstr_release(x_247, 3);
 x_613 = x_247;
} else {
 lean::dec_ref(x_247);
 x_613 = lean::box(0);
}
if (lean::is_scalar(x_613)) {
 x_614 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_614 = x_613;
}
lean::cnstr_set(x_614, 0, x_235);
lean::cnstr_set(x_614, 1, x_586);
lean::cnstr_set(x_614, 2, x_587);
lean::cnstr_set(x_614, 3, x_235);
lean::cnstr_set_uint8(x_614, sizeof(void*)*4, x_246);
x_615 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_615, 0, x_609);
lean::cnstr_set(x_615, 1, x_610);
lean::cnstr_set(x_615, 2, x_611);
lean::cnstr_set(x_615, 3, x_612);
lean::cnstr_set_uint8(x_615, sizeof(void*)*4, x_538);
lean::cnstr_set(x_1, 3, x_519);
lean::cnstr_set(x_1, 2, x_608);
lean::cnstr_set(x_1, 1, x_607);
lean::cnstr_set(x_1, 0, x_615);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_246);
x_616 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_616, 0, x_614);
lean::cnstr_set(x_616, 1, x_2);
lean::cnstr_set(x_616, 2, x_3);
lean::cnstr_set(x_616, 3, x_1);
lean::cnstr_set_uint8(x_616, sizeof(void*)*4, x_538);
return x_616;
}
}
else
{
obj* x_617; obj* x_618; obj* x_619; obj* x_620; obj* x_621; obj* x_622; obj* x_623; obj* x_624; obj* x_625; obj* x_626; obj* x_627; obj* x_628; obj* x_629; obj* x_630; 
x_617 = lean::cnstr_get(x_1, 1);
x_618 = lean::cnstr_get(x_1, 2);
lean::inc(x_618);
lean::inc(x_617);
lean::dec(x_1);
x_619 = lean::cnstr_get(x_4, 1);
lean::inc(x_619);
x_620 = lean::cnstr_get(x_4, 2);
lean::inc(x_620);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_621 = x_4;
} else {
 lean::dec_ref(x_4);
 x_621 = lean::box(0);
}
x_622 = lean::cnstr_get(x_247, 0);
lean::inc(x_622);
x_623 = lean::cnstr_get(x_247, 1);
lean::inc(x_623);
x_624 = lean::cnstr_get(x_247, 2);
lean::inc(x_624);
x_625 = lean::cnstr_get(x_247, 3);
lean::inc(x_625);
if (lean::is_exclusive(x_247)) {
 lean::cnstr_release(x_247, 0);
 lean::cnstr_release(x_247, 1);
 lean::cnstr_release(x_247, 2);
 lean::cnstr_release(x_247, 3);
 x_626 = x_247;
} else {
 lean::dec_ref(x_247);
 x_626 = lean::box(0);
}
if (lean::is_scalar(x_626)) {
 x_627 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_627 = x_626;
}
lean::cnstr_set(x_627, 0, x_235);
lean::cnstr_set(x_627, 1, x_617);
lean::cnstr_set(x_627, 2, x_618);
lean::cnstr_set(x_627, 3, x_235);
lean::cnstr_set_uint8(x_627, sizeof(void*)*4, x_246);
if (lean::is_scalar(x_621)) {
 x_628 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_628 = x_621;
}
lean::cnstr_set(x_628, 0, x_622);
lean::cnstr_set(x_628, 1, x_623);
lean::cnstr_set(x_628, 2, x_624);
lean::cnstr_set(x_628, 3, x_625);
lean::cnstr_set_uint8(x_628, sizeof(void*)*4, x_538);
x_629 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_629, 0, x_628);
lean::cnstr_set(x_629, 1, x_619);
lean::cnstr_set(x_629, 2, x_620);
lean::cnstr_set(x_629, 3, x_519);
lean::cnstr_set_uint8(x_629, sizeof(void*)*4, x_246);
x_630 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_630, 0, x_627);
lean::cnstr_set(x_630, 1, x_2);
lean::cnstr_set(x_630, 2, x_3);
lean::cnstr_set(x_630, 3, x_629);
lean::cnstr_set_uint8(x_630, sizeof(void*)*4, x_538);
return x_630;
}
}
}
}
}
}
else
{
uint8 x_631; 
x_631 = !lean::is_exclusive(x_1);
if (x_631 == 0)
{
obj* x_632; obj* x_633; obj* x_634; 
x_632 = lean::cnstr_get(x_1, 3);
lean::dec(x_632);
x_633 = lean::cnstr_get(x_1, 0);
lean::dec(x_633);
lean::cnstr_set(x_1, 0, x_235);
x_634 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_634, 0, x_1);
lean::cnstr_set(x_634, 1, x_2);
lean::cnstr_set(x_634, 2, x_3);
lean::cnstr_set(x_634, 3, x_4);
lean::cnstr_set_uint8(x_634, sizeof(void*)*4, x_246);
return x_634;
}
else
{
obj* x_635; obj* x_636; obj* x_637; obj* x_638; 
x_635 = lean::cnstr_get(x_1, 1);
x_636 = lean::cnstr_get(x_1, 2);
lean::inc(x_636);
lean::inc(x_635);
lean::dec(x_1);
x_637 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_637, 0, x_235);
lean::cnstr_set(x_637, 1, x_635);
lean::cnstr_set(x_637, 2, x_636);
lean::cnstr_set(x_637, 3, x_235);
lean::cnstr_set_uint8(x_637, sizeof(void*)*4, x_233);
x_638 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_638, 0, x_637);
lean::cnstr_set(x_638, 1, x_2);
lean::cnstr_set(x_638, 2, x_3);
lean::cnstr_set(x_638, 3, x_4);
lean::cnstr_set_uint8(x_638, sizeof(void*)*4, x_246);
return x_638;
}
}
}
}
else
{
uint8 x_639; 
x_639 = lean::cnstr_get_uint8(x_235, sizeof(void*)*4);
if (x_639 == 0)
{
uint8 x_640; 
x_640 = !lean::is_exclusive(x_1);
if (x_640 == 0)
{
obj* x_641; obj* x_642; obj* x_643; obj* x_644; uint8 x_645; 
x_641 = lean::cnstr_get(x_1, 1);
x_642 = lean::cnstr_get(x_1, 2);
x_643 = lean::cnstr_get(x_1, 3);
lean::dec(x_643);
x_644 = lean::cnstr_get(x_1, 0);
lean::dec(x_644);
x_645 = !lean::is_exclusive(x_235);
if (x_645 == 0)
{
obj* x_646; obj* x_647; obj* x_648; obj* x_649; uint8 x_650; obj* x_651; 
x_646 = lean::cnstr_get(x_235, 0);
x_647 = lean::cnstr_get(x_235, 1);
x_648 = lean::cnstr_get(x_235, 2);
x_649 = lean::cnstr_get(x_235, 3);
x_650 = 1;
lean::cnstr_set(x_235, 3, x_646);
lean::cnstr_set(x_235, 2, x_642);
lean::cnstr_set(x_235, 1, x_641);
lean::cnstr_set(x_235, 0, x_234);
lean::cnstr_set_uint8(x_235, sizeof(void*)*4, x_650);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_649);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_650);
x_651 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_651, 0, x_235);
lean::cnstr_set(x_651, 1, x_647);
lean::cnstr_set(x_651, 2, x_648);
lean::cnstr_set(x_651, 3, x_1);
lean::cnstr_set_uint8(x_651, sizeof(void*)*4, x_639);
return x_651;
}
else
{
obj* x_652; obj* x_653; obj* x_654; obj* x_655; uint8 x_656; obj* x_657; obj* x_658; 
x_652 = lean::cnstr_get(x_235, 0);
x_653 = lean::cnstr_get(x_235, 1);
x_654 = lean::cnstr_get(x_235, 2);
x_655 = lean::cnstr_get(x_235, 3);
lean::inc(x_655);
lean::inc(x_654);
lean::inc(x_653);
lean::inc(x_652);
lean::dec(x_235);
x_656 = 1;
x_657 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_657, 0, x_234);
lean::cnstr_set(x_657, 1, x_641);
lean::cnstr_set(x_657, 2, x_642);
lean::cnstr_set(x_657, 3, x_652);
lean::cnstr_set_uint8(x_657, sizeof(void*)*4, x_656);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_655);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_656);
x_658 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_658, 0, x_657);
lean::cnstr_set(x_658, 1, x_653);
lean::cnstr_set(x_658, 2, x_654);
lean::cnstr_set(x_658, 3, x_1);
lean::cnstr_set_uint8(x_658, sizeof(void*)*4, x_639);
return x_658;
}
}
else
{
obj* x_659; obj* x_660; obj* x_661; obj* x_662; obj* x_663; obj* x_664; obj* x_665; uint8 x_666; obj* x_667; obj* x_668; obj* x_669; 
x_659 = lean::cnstr_get(x_1, 1);
x_660 = lean::cnstr_get(x_1, 2);
lean::inc(x_660);
lean::inc(x_659);
lean::dec(x_1);
x_661 = lean::cnstr_get(x_235, 0);
lean::inc(x_661);
x_662 = lean::cnstr_get(x_235, 1);
lean::inc(x_662);
x_663 = lean::cnstr_get(x_235, 2);
lean::inc(x_663);
x_664 = lean::cnstr_get(x_235, 3);
lean::inc(x_664);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_665 = x_235;
} else {
 lean::dec_ref(x_235);
 x_665 = lean::box(0);
}
x_666 = 1;
if (lean::is_scalar(x_665)) {
 x_667 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_667 = x_665;
}
lean::cnstr_set(x_667, 0, x_234);
lean::cnstr_set(x_667, 1, x_659);
lean::cnstr_set(x_667, 2, x_660);
lean::cnstr_set(x_667, 3, x_661);
lean::cnstr_set_uint8(x_667, sizeof(void*)*4, x_666);
x_668 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_668, 0, x_664);
lean::cnstr_set(x_668, 1, x_2);
lean::cnstr_set(x_668, 2, x_3);
lean::cnstr_set(x_668, 3, x_4);
lean::cnstr_set_uint8(x_668, sizeof(void*)*4, x_666);
x_669 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_669, 0, x_667);
lean::cnstr_set(x_669, 1, x_662);
lean::cnstr_set(x_669, 2, x_663);
lean::cnstr_set(x_669, 3, x_668);
lean::cnstr_set_uint8(x_669, sizeof(void*)*4, x_639);
return x_669;
}
}
else
{
if (lean::obj_tag(x_4) == 0)
{
uint8 x_670; 
x_670 = !lean::is_exclusive(x_1);
if (x_670 == 0)
{
obj* x_671; obj* x_672; obj* x_673; 
x_671 = lean::cnstr_get(x_1, 3);
lean::dec(x_671);
x_672 = lean::cnstr_get(x_1, 0);
lean::dec(x_672);
lean::cnstr_set(x_1, 0, x_4);
x_673 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_673, 0, x_1);
lean::cnstr_set(x_673, 1, x_2);
lean::cnstr_set(x_673, 2, x_3);
lean::cnstr_set(x_673, 3, x_4);
lean::cnstr_set_uint8(x_673, sizeof(void*)*4, x_639);
return x_673;
}
else
{
obj* x_674; obj* x_675; obj* x_676; obj* x_677; 
x_674 = lean::cnstr_get(x_1, 1);
x_675 = lean::cnstr_get(x_1, 2);
lean::inc(x_675);
lean::inc(x_674);
lean::dec(x_1);
x_676 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_676, 0, x_4);
lean::cnstr_set(x_676, 1, x_674);
lean::cnstr_set(x_676, 2, x_675);
lean::cnstr_set(x_676, 3, x_235);
lean::cnstr_set_uint8(x_676, sizeof(void*)*4, x_233);
x_677 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_677, 0, x_676);
lean::cnstr_set(x_677, 1, x_2);
lean::cnstr_set(x_677, 2, x_3);
lean::cnstr_set(x_677, 3, x_4);
lean::cnstr_set_uint8(x_677, sizeof(void*)*4, x_639);
return x_677;
}
}
else
{
uint8 x_678; 
x_678 = lean::cnstr_get_uint8(x_4, sizeof(void*)*4);
if (x_678 == 0)
{
obj* x_679; 
x_679 = lean::cnstr_get(x_4, 0);
lean::inc(x_679);
if (lean::obj_tag(x_679) == 0)
{
obj* x_680; 
x_680 = lean::cnstr_get(x_4, 3);
lean::inc(x_680);
if (lean::obj_tag(x_680) == 0)
{
uint8 x_681; 
x_681 = !lean::is_exclusive(x_1);
if (x_681 == 0)
{
obj* x_682; obj* x_683; obj* x_684; obj* x_685; uint8 x_686; 
x_682 = lean::cnstr_get(x_1, 1);
x_683 = lean::cnstr_get(x_1, 2);
x_684 = lean::cnstr_get(x_1, 3);
lean::dec(x_684);
x_685 = lean::cnstr_get(x_1, 0);
lean::dec(x_685);
x_686 = !lean::is_exclusive(x_4);
if (x_686 == 0)
{
obj* x_687; obj* x_688; obj* x_689; obj* x_690; uint8 x_691; 
x_687 = lean::cnstr_get(x_4, 1);
x_688 = lean::cnstr_get(x_4, 2);
x_689 = lean::cnstr_get(x_4, 3);
lean::dec(x_689);
x_690 = lean::cnstr_get(x_4, 0);
lean::dec(x_690);
lean::inc(x_235);
lean::cnstr_set(x_4, 3, x_235);
lean::cnstr_set(x_4, 2, x_683);
lean::cnstr_set(x_4, 1, x_682);
lean::cnstr_set(x_4, 0, x_680);
x_691 = !lean::is_exclusive(x_235);
if (x_691 == 0)
{
obj* x_692; obj* x_693; obj* x_694; obj* x_695; 
x_692 = lean::cnstr_get(x_235, 3);
lean::dec(x_692);
x_693 = lean::cnstr_get(x_235, 2);
lean::dec(x_693);
x_694 = lean::cnstr_get(x_235, 1);
lean::dec(x_694);
x_695 = lean::cnstr_get(x_235, 0);
lean::dec(x_695);
lean::cnstr_set(x_235, 3, x_680);
lean::cnstr_set(x_235, 2, x_688);
lean::cnstr_set(x_235, 1, x_687);
lean::cnstr_set(x_235, 0, x_680);
lean::cnstr_set_uint8(x_235, sizeof(void*)*4, x_678);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_639);
return x_1;
}
else
{
obj* x_696; 
lean::dec(x_235);
x_696 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_696, 0, x_680);
lean::cnstr_set(x_696, 1, x_687);
lean::cnstr_set(x_696, 2, x_688);
lean::cnstr_set(x_696, 3, x_680);
lean::cnstr_set_uint8(x_696, sizeof(void*)*4, x_678);
lean::cnstr_set(x_1, 3, x_696);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_639);
return x_1;
}
}
else
{
obj* x_697; obj* x_698; obj* x_699; obj* x_700; obj* x_701; 
x_697 = lean::cnstr_get(x_4, 1);
x_698 = lean::cnstr_get(x_4, 2);
lean::inc(x_698);
lean::inc(x_697);
lean::dec(x_4);
lean::inc(x_235);
x_699 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_699, 0, x_680);
lean::cnstr_set(x_699, 1, x_682);
lean::cnstr_set(x_699, 2, x_683);
lean::cnstr_set(x_699, 3, x_235);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_700 = x_235;
} else {
 lean::dec_ref(x_235);
 x_700 = lean::box(0);
}
lean::cnstr_set_uint8(x_699, sizeof(void*)*4, x_678);
if (lean::is_scalar(x_700)) {
 x_701 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_701 = x_700;
}
lean::cnstr_set(x_701, 0, x_680);
lean::cnstr_set(x_701, 1, x_697);
lean::cnstr_set(x_701, 2, x_698);
lean::cnstr_set(x_701, 3, x_680);
lean::cnstr_set_uint8(x_701, sizeof(void*)*4, x_678);
lean::cnstr_set(x_1, 3, x_701);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_699);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_639);
return x_1;
}
}
else
{
obj* x_702; obj* x_703; obj* x_704; obj* x_705; obj* x_706; obj* x_707; obj* x_708; obj* x_709; obj* x_710; 
x_702 = lean::cnstr_get(x_1, 1);
x_703 = lean::cnstr_get(x_1, 2);
lean::inc(x_703);
lean::inc(x_702);
lean::dec(x_1);
x_704 = lean::cnstr_get(x_4, 1);
lean::inc(x_704);
x_705 = lean::cnstr_get(x_4, 2);
lean::inc(x_705);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_706 = x_4;
} else {
 lean::dec_ref(x_4);
 x_706 = lean::box(0);
}
lean::inc(x_235);
if (lean::is_scalar(x_706)) {
 x_707 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_707 = x_706;
}
lean::cnstr_set(x_707, 0, x_680);
lean::cnstr_set(x_707, 1, x_702);
lean::cnstr_set(x_707, 2, x_703);
lean::cnstr_set(x_707, 3, x_235);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_708 = x_235;
} else {
 lean::dec_ref(x_235);
 x_708 = lean::box(0);
}
lean::cnstr_set_uint8(x_707, sizeof(void*)*4, x_678);
if (lean::is_scalar(x_708)) {
 x_709 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_709 = x_708;
}
lean::cnstr_set(x_709, 0, x_680);
lean::cnstr_set(x_709, 1, x_704);
lean::cnstr_set(x_709, 2, x_705);
lean::cnstr_set(x_709, 3, x_680);
lean::cnstr_set_uint8(x_709, sizeof(void*)*4, x_678);
x_710 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_710, 0, x_707);
lean::cnstr_set(x_710, 1, x_2);
lean::cnstr_set(x_710, 2, x_3);
lean::cnstr_set(x_710, 3, x_709);
lean::cnstr_set_uint8(x_710, sizeof(void*)*4, x_639);
return x_710;
}
}
else
{
uint8 x_711; 
x_711 = lean::cnstr_get_uint8(x_680, sizeof(void*)*4);
if (x_711 == 0)
{
uint8 x_712; 
x_712 = !lean::is_exclusive(x_1);
if (x_712 == 0)
{
obj* x_713; obj* x_714; obj* x_715; obj* x_716; uint8 x_717; 
x_713 = lean::cnstr_get(x_1, 1);
x_714 = lean::cnstr_get(x_1, 2);
x_715 = lean::cnstr_get(x_1, 3);
lean::dec(x_715);
x_716 = lean::cnstr_get(x_1, 0);
lean::dec(x_716);
x_717 = !lean::is_exclusive(x_4);
if (x_717 == 0)
{
obj* x_718; obj* x_719; obj* x_720; obj* x_721; uint8 x_722; 
x_718 = lean::cnstr_get(x_4, 1);
x_719 = lean::cnstr_get(x_4, 2);
x_720 = lean::cnstr_get(x_4, 3);
lean::dec(x_720);
x_721 = lean::cnstr_get(x_4, 0);
lean::dec(x_721);
x_722 = !lean::is_exclusive(x_680);
if (x_722 == 0)
{
obj* x_723; obj* x_724; obj* x_725; obj* x_726; uint8 x_727; 
x_723 = lean::cnstr_get(x_680, 0);
x_724 = lean::cnstr_get(x_680, 1);
x_725 = lean::cnstr_get(x_680, 2);
x_726 = lean::cnstr_get(x_680, 3);
lean::inc(x_235);
lean::cnstr_set(x_680, 3, x_235);
lean::cnstr_set(x_680, 2, x_714);
lean::cnstr_set(x_680, 1, x_713);
lean::cnstr_set(x_680, 0, x_679);
x_727 = !lean::is_exclusive(x_235);
if (x_727 == 0)
{
obj* x_728; obj* x_729; obj* x_730; obj* x_731; 
x_728 = lean::cnstr_get(x_235, 3);
lean::dec(x_728);
x_729 = lean::cnstr_get(x_235, 2);
lean::dec(x_729);
x_730 = lean::cnstr_get(x_235, 1);
lean::dec(x_730);
x_731 = lean::cnstr_get(x_235, 0);
lean::dec(x_731);
lean::cnstr_set(x_4, 3, x_679);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_680);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_639);
lean::cnstr_set(x_235, 3, x_726);
lean::cnstr_set(x_235, 2, x_725);
lean::cnstr_set(x_235, 1, x_724);
lean::cnstr_set(x_235, 0, x_723);
lean::cnstr_set(x_1, 2, x_719);
lean::cnstr_set(x_1, 1, x_718);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_711);
return x_1;
}
else
{
obj* x_732; 
lean::dec(x_235);
lean::cnstr_set(x_4, 3, x_679);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_680);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_639);
x_732 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_732, 0, x_723);
lean::cnstr_set(x_732, 1, x_724);
lean::cnstr_set(x_732, 2, x_725);
lean::cnstr_set(x_732, 3, x_726);
lean::cnstr_set_uint8(x_732, sizeof(void*)*4, x_639);
lean::cnstr_set(x_1, 3, x_732);
lean::cnstr_set(x_1, 2, x_719);
lean::cnstr_set(x_1, 1, x_718);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_711);
return x_1;
}
}
else
{
obj* x_733; obj* x_734; obj* x_735; obj* x_736; obj* x_737; obj* x_738; obj* x_739; 
x_733 = lean::cnstr_get(x_680, 0);
x_734 = lean::cnstr_get(x_680, 1);
x_735 = lean::cnstr_get(x_680, 2);
x_736 = lean::cnstr_get(x_680, 3);
lean::inc(x_736);
lean::inc(x_735);
lean::inc(x_734);
lean::inc(x_733);
lean::dec(x_680);
lean::inc(x_235);
x_737 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_737, 0, x_679);
lean::cnstr_set(x_737, 1, x_713);
lean::cnstr_set(x_737, 2, x_714);
lean::cnstr_set(x_737, 3, x_235);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_738 = x_235;
} else {
 lean::dec_ref(x_235);
 x_738 = lean::box(0);
}
lean::cnstr_set_uint8(x_737, sizeof(void*)*4, x_711);
lean::cnstr_set(x_4, 3, x_679);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_737);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_639);
if (lean::is_scalar(x_738)) {
 x_739 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_739 = x_738;
}
lean::cnstr_set(x_739, 0, x_733);
lean::cnstr_set(x_739, 1, x_734);
lean::cnstr_set(x_739, 2, x_735);
lean::cnstr_set(x_739, 3, x_736);
lean::cnstr_set_uint8(x_739, sizeof(void*)*4, x_639);
lean::cnstr_set(x_1, 3, x_739);
lean::cnstr_set(x_1, 2, x_719);
lean::cnstr_set(x_1, 1, x_718);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_711);
return x_1;
}
}
else
{
obj* x_740; obj* x_741; obj* x_742; obj* x_743; obj* x_744; obj* x_745; obj* x_746; obj* x_747; obj* x_748; obj* x_749; obj* x_750; 
x_740 = lean::cnstr_get(x_4, 1);
x_741 = lean::cnstr_get(x_4, 2);
lean::inc(x_741);
lean::inc(x_740);
lean::dec(x_4);
x_742 = lean::cnstr_get(x_680, 0);
lean::inc(x_742);
x_743 = lean::cnstr_get(x_680, 1);
lean::inc(x_743);
x_744 = lean::cnstr_get(x_680, 2);
lean::inc(x_744);
x_745 = lean::cnstr_get(x_680, 3);
lean::inc(x_745);
if (lean::is_exclusive(x_680)) {
 lean::cnstr_release(x_680, 0);
 lean::cnstr_release(x_680, 1);
 lean::cnstr_release(x_680, 2);
 lean::cnstr_release(x_680, 3);
 x_746 = x_680;
} else {
 lean::dec_ref(x_680);
 x_746 = lean::box(0);
}
lean::inc(x_235);
if (lean::is_scalar(x_746)) {
 x_747 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_747 = x_746;
}
lean::cnstr_set(x_747, 0, x_679);
lean::cnstr_set(x_747, 1, x_713);
lean::cnstr_set(x_747, 2, x_714);
lean::cnstr_set(x_747, 3, x_235);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_748 = x_235;
} else {
 lean::dec_ref(x_235);
 x_748 = lean::box(0);
}
lean::cnstr_set_uint8(x_747, sizeof(void*)*4, x_711);
x_749 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_749, 0, x_747);
lean::cnstr_set(x_749, 1, x_2);
lean::cnstr_set(x_749, 2, x_3);
lean::cnstr_set(x_749, 3, x_679);
lean::cnstr_set_uint8(x_749, sizeof(void*)*4, x_639);
if (lean::is_scalar(x_748)) {
 x_750 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_750 = x_748;
}
lean::cnstr_set(x_750, 0, x_742);
lean::cnstr_set(x_750, 1, x_743);
lean::cnstr_set(x_750, 2, x_744);
lean::cnstr_set(x_750, 3, x_745);
lean::cnstr_set_uint8(x_750, sizeof(void*)*4, x_639);
lean::cnstr_set(x_1, 3, x_750);
lean::cnstr_set(x_1, 2, x_741);
lean::cnstr_set(x_1, 1, x_740);
lean::cnstr_set(x_1, 0, x_749);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_711);
return x_1;
}
}
else
{
obj* x_751; obj* x_752; obj* x_753; obj* x_754; obj* x_755; obj* x_756; obj* x_757; obj* x_758; obj* x_759; obj* x_760; obj* x_761; obj* x_762; obj* x_763; obj* x_764; obj* x_765; 
x_751 = lean::cnstr_get(x_1, 1);
x_752 = lean::cnstr_get(x_1, 2);
lean::inc(x_752);
lean::inc(x_751);
lean::dec(x_1);
x_753 = lean::cnstr_get(x_4, 1);
lean::inc(x_753);
x_754 = lean::cnstr_get(x_4, 2);
lean::inc(x_754);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_755 = x_4;
} else {
 lean::dec_ref(x_4);
 x_755 = lean::box(0);
}
x_756 = lean::cnstr_get(x_680, 0);
lean::inc(x_756);
x_757 = lean::cnstr_get(x_680, 1);
lean::inc(x_757);
x_758 = lean::cnstr_get(x_680, 2);
lean::inc(x_758);
x_759 = lean::cnstr_get(x_680, 3);
lean::inc(x_759);
if (lean::is_exclusive(x_680)) {
 lean::cnstr_release(x_680, 0);
 lean::cnstr_release(x_680, 1);
 lean::cnstr_release(x_680, 2);
 lean::cnstr_release(x_680, 3);
 x_760 = x_680;
} else {
 lean::dec_ref(x_680);
 x_760 = lean::box(0);
}
lean::inc(x_235);
if (lean::is_scalar(x_760)) {
 x_761 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_761 = x_760;
}
lean::cnstr_set(x_761, 0, x_679);
lean::cnstr_set(x_761, 1, x_751);
lean::cnstr_set(x_761, 2, x_752);
lean::cnstr_set(x_761, 3, x_235);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_762 = x_235;
} else {
 lean::dec_ref(x_235);
 x_762 = lean::box(0);
}
lean::cnstr_set_uint8(x_761, sizeof(void*)*4, x_711);
if (lean::is_scalar(x_755)) {
 x_763 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_763 = x_755;
}
lean::cnstr_set(x_763, 0, x_761);
lean::cnstr_set(x_763, 1, x_2);
lean::cnstr_set(x_763, 2, x_3);
lean::cnstr_set(x_763, 3, x_679);
lean::cnstr_set_uint8(x_763, sizeof(void*)*4, x_639);
if (lean::is_scalar(x_762)) {
 x_764 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_764 = x_762;
}
lean::cnstr_set(x_764, 0, x_756);
lean::cnstr_set(x_764, 1, x_757);
lean::cnstr_set(x_764, 2, x_758);
lean::cnstr_set(x_764, 3, x_759);
lean::cnstr_set_uint8(x_764, sizeof(void*)*4, x_639);
x_765 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_765, 0, x_763);
lean::cnstr_set(x_765, 1, x_753);
lean::cnstr_set(x_765, 2, x_754);
lean::cnstr_set(x_765, 3, x_764);
lean::cnstr_set_uint8(x_765, sizeof(void*)*4, x_711);
return x_765;
}
}
else
{
uint8 x_766; 
x_766 = !lean::is_exclusive(x_680);
if (x_766 == 0)
{
obj* x_767; obj* x_768; obj* x_769; obj* x_770; uint8 x_771; 
x_767 = lean::cnstr_get(x_680, 3);
lean::dec(x_767);
x_768 = lean::cnstr_get(x_680, 2);
lean::dec(x_768);
x_769 = lean::cnstr_get(x_680, 1);
lean::dec(x_769);
x_770 = lean::cnstr_get(x_680, 0);
lean::dec(x_770);
x_771 = !lean::is_exclusive(x_1);
if (x_771 == 0)
{
obj* x_772; obj* x_773; obj* x_774; obj* x_775; uint8 x_776; 
x_772 = lean::cnstr_get(x_1, 1);
x_773 = lean::cnstr_get(x_1, 2);
x_774 = lean::cnstr_get(x_1, 3);
lean::dec(x_774);
x_775 = lean::cnstr_get(x_1, 0);
lean::dec(x_775);
x_776 = !lean::is_exclusive(x_235);
if (x_776 == 0)
{
obj* x_777; obj* x_778; obj* x_779; obj* x_780; 
x_777 = lean::cnstr_get(x_235, 0);
x_778 = lean::cnstr_get(x_235, 1);
x_779 = lean::cnstr_get(x_235, 2);
x_780 = lean::cnstr_get(x_235, 3);
lean::cnstr_set(x_680, 3, x_780);
lean::cnstr_set(x_680, 2, x_779);
lean::cnstr_set(x_680, 1, x_778);
lean::cnstr_set(x_680, 0, x_777);
lean::cnstr_set(x_235, 3, x_680);
lean::cnstr_set(x_235, 2, x_773);
lean::cnstr_set(x_235, 1, x_772);
lean::cnstr_set(x_235, 0, x_679);
lean::cnstr_set_uint8(x_235, sizeof(void*)*4, x_678);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_235);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_711);
return x_1;
}
else
{
obj* x_781; obj* x_782; obj* x_783; obj* x_784; obj* x_785; 
x_781 = lean::cnstr_get(x_235, 0);
x_782 = lean::cnstr_get(x_235, 1);
x_783 = lean::cnstr_get(x_235, 2);
x_784 = lean::cnstr_get(x_235, 3);
lean::inc(x_784);
lean::inc(x_783);
lean::inc(x_782);
lean::inc(x_781);
lean::dec(x_235);
lean::cnstr_set(x_680, 3, x_784);
lean::cnstr_set(x_680, 2, x_783);
lean::cnstr_set(x_680, 1, x_782);
lean::cnstr_set(x_680, 0, x_781);
x_785 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_785, 0, x_679);
lean::cnstr_set(x_785, 1, x_772);
lean::cnstr_set(x_785, 2, x_773);
lean::cnstr_set(x_785, 3, x_680);
lean::cnstr_set_uint8(x_785, sizeof(void*)*4, x_678);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_785);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_711);
return x_1;
}
}
else
{
obj* x_786; obj* x_787; obj* x_788; obj* x_789; obj* x_790; obj* x_791; obj* x_792; obj* x_793; obj* x_794; 
x_786 = lean::cnstr_get(x_1, 1);
x_787 = lean::cnstr_get(x_1, 2);
lean::inc(x_787);
lean::inc(x_786);
lean::dec(x_1);
x_788 = lean::cnstr_get(x_235, 0);
lean::inc(x_788);
x_789 = lean::cnstr_get(x_235, 1);
lean::inc(x_789);
x_790 = lean::cnstr_get(x_235, 2);
lean::inc(x_790);
x_791 = lean::cnstr_get(x_235, 3);
lean::inc(x_791);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_792 = x_235;
} else {
 lean::dec_ref(x_235);
 x_792 = lean::box(0);
}
lean::cnstr_set(x_680, 3, x_791);
lean::cnstr_set(x_680, 2, x_790);
lean::cnstr_set(x_680, 1, x_789);
lean::cnstr_set(x_680, 0, x_788);
if (lean::is_scalar(x_792)) {
 x_793 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_793 = x_792;
}
lean::cnstr_set(x_793, 0, x_679);
lean::cnstr_set(x_793, 1, x_786);
lean::cnstr_set(x_793, 2, x_787);
lean::cnstr_set(x_793, 3, x_680);
lean::cnstr_set_uint8(x_793, sizeof(void*)*4, x_678);
x_794 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_794, 0, x_793);
lean::cnstr_set(x_794, 1, x_2);
lean::cnstr_set(x_794, 2, x_3);
lean::cnstr_set(x_794, 3, x_4);
lean::cnstr_set_uint8(x_794, sizeof(void*)*4, x_711);
return x_794;
}
}
else
{
obj* x_795; obj* x_796; obj* x_797; obj* x_798; obj* x_799; obj* x_800; obj* x_801; obj* x_802; obj* x_803; obj* x_804; obj* x_805; 
lean::dec(x_680);
x_795 = lean::cnstr_get(x_1, 1);
lean::inc(x_795);
x_796 = lean::cnstr_get(x_1, 2);
lean::inc(x_796);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_797 = x_1;
} else {
 lean::dec_ref(x_1);
 x_797 = lean::box(0);
}
x_798 = lean::cnstr_get(x_235, 0);
lean::inc(x_798);
x_799 = lean::cnstr_get(x_235, 1);
lean::inc(x_799);
x_800 = lean::cnstr_get(x_235, 2);
lean::inc(x_800);
x_801 = lean::cnstr_get(x_235, 3);
lean::inc(x_801);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_802 = x_235;
} else {
 lean::dec_ref(x_235);
 x_802 = lean::box(0);
}
x_803 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_803, 0, x_798);
lean::cnstr_set(x_803, 1, x_799);
lean::cnstr_set(x_803, 2, x_800);
lean::cnstr_set(x_803, 3, x_801);
lean::cnstr_set_uint8(x_803, sizeof(void*)*4, x_711);
if (lean::is_scalar(x_802)) {
 x_804 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_804 = x_802;
}
lean::cnstr_set(x_804, 0, x_679);
lean::cnstr_set(x_804, 1, x_795);
lean::cnstr_set(x_804, 2, x_796);
lean::cnstr_set(x_804, 3, x_803);
lean::cnstr_set_uint8(x_804, sizeof(void*)*4, x_678);
if (lean::is_scalar(x_797)) {
 x_805 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_805 = x_797;
}
lean::cnstr_set(x_805, 0, x_804);
lean::cnstr_set(x_805, 1, x_2);
lean::cnstr_set(x_805, 2, x_3);
lean::cnstr_set(x_805, 3, x_4);
lean::cnstr_set_uint8(x_805, sizeof(void*)*4, x_711);
return x_805;
}
}
}
}
else
{
uint8 x_806; 
x_806 = lean::cnstr_get_uint8(x_679, sizeof(void*)*4);
if (x_806 == 0)
{
obj* x_807; 
x_807 = lean::cnstr_get(x_4, 3);
lean::inc(x_807);
if (lean::obj_tag(x_807) == 0)
{
uint8 x_808; 
x_808 = !lean::is_exclusive(x_1);
if (x_808 == 0)
{
obj* x_809; obj* x_810; obj* x_811; obj* x_812; uint8 x_813; 
x_809 = lean::cnstr_get(x_1, 1);
x_810 = lean::cnstr_get(x_1, 2);
x_811 = lean::cnstr_get(x_1, 3);
lean::dec(x_811);
x_812 = lean::cnstr_get(x_1, 0);
lean::dec(x_812);
x_813 = !lean::is_exclusive(x_4);
if (x_813 == 0)
{
obj* x_814; obj* x_815; obj* x_816; obj* x_817; uint8 x_818; 
x_814 = lean::cnstr_get(x_4, 1);
x_815 = lean::cnstr_get(x_4, 2);
x_816 = lean::cnstr_get(x_4, 3);
lean::dec(x_816);
x_817 = lean::cnstr_get(x_4, 0);
lean::dec(x_817);
x_818 = !lean::is_exclusive(x_679);
if (x_818 == 0)
{
obj* x_819; obj* x_820; obj* x_821; obj* x_822; uint8 x_823; 
x_819 = lean::cnstr_get(x_679, 0);
x_820 = lean::cnstr_get(x_679, 1);
x_821 = lean::cnstr_get(x_679, 2);
x_822 = lean::cnstr_get(x_679, 3);
lean::inc(x_235);
lean::cnstr_set(x_679, 3, x_235);
lean::cnstr_set(x_679, 2, x_810);
lean::cnstr_set(x_679, 1, x_809);
lean::cnstr_set(x_679, 0, x_807);
x_823 = !lean::is_exclusive(x_235);
if (x_823 == 0)
{
obj* x_824; obj* x_825; obj* x_826; obj* x_827; 
x_824 = lean::cnstr_get(x_235, 3);
lean::dec(x_824);
x_825 = lean::cnstr_get(x_235, 2);
lean::dec(x_825);
x_826 = lean::cnstr_get(x_235, 1);
lean::dec(x_826);
x_827 = lean::cnstr_get(x_235, 0);
lean::dec(x_827);
lean::cnstr_set(x_4, 3, x_819);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_639);
lean::cnstr_set(x_235, 3, x_807);
lean::cnstr_set(x_235, 2, x_815);
lean::cnstr_set(x_235, 1, x_814);
lean::cnstr_set(x_235, 0, x_822);
lean::cnstr_set(x_1, 2, x_821);
lean::cnstr_set(x_1, 1, x_820);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_806);
return x_1;
}
else
{
obj* x_828; 
lean::dec(x_235);
lean::cnstr_set(x_4, 3, x_819);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_639);
x_828 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_828, 0, x_822);
lean::cnstr_set(x_828, 1, x_814);
lean::cnstr_set(x_828, 2, x_815);
lean::cnstr_set(x_828, 3, x_807);
lean::cnstr_set_uint8(x_828, sizeof(void*)*4, x_639);
lean::cnstr_set(x_1, 3, x_828);
lean::cnstr_set(x_1, 2, x_821);
lean::cnstr_set(x_1, 1, x_820);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_806);
return x_1;
}
}
else
{
obj* x_829; obj* x_830; obj* x_831; obj* x_832; obj* x_833; obj* x_834; obj* x_835; 
x_829 = lean::cnstr_get(x_679, 0);
x_830 = lean::cnstr_get(x_679, 1);
x_831 = lean::cnstr_get(x_679, 2);
x_832 = lean::cnstr_get(x_679, 3);
lean::inc(x_832);
lean::inc(x_831);
lean::inc(x_830);
lean::inc(x_829);
lean::dec(x_679);
lean::inc(x_235);
x_833 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_833, 0, x_807);
lean::cnstr_set(x_833, 1, x_809);
lean::cnstr_set(x_833, 2, x_810);
lean::cnstr_set(x_833, 3, x_235);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_834 = x_235;
} else {
 lean::dec_ref(x_235);
 x_834 = lean::box(0);
}
lean::cnstr_set_uint8(x_833, sizeof(void*)*4, x_806);
lean::cnstr_set(x_4, 3, x_829);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_833);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_639);
if (lean::is_scalar(x_834)) {
 x_835 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_835 = x_834;
}
lean::cnstr_set(x_835, 0, x_832);
lean::cnstr_set(x_835, 1, x_814);
lean::cnstr_set(x_835, 2, x_815);
lean::cnstr_set(x_835, 3, x_807);
lean::cnstr_set_uint8(x_835, sizeof(void*)*4, x_639);
lean::cnstr_set(x_1, 3, x_835);
lean::cnstr_set(x_1, 2, x_831);
lean::cnstr_set(x_1, 1, x_830);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_806);
return x_1;
}
}
else
{
obj* x_836; obj* x_837; obj* x_838; obj* x_839; obj* x_840; obj* x_841; obj* x_842; obj* x_843; obj* x_844; obj* x_845; obj* x_846; 
x_836 = lean::cnstr_get(x_4, 1);
x_837 = lean::cnstr_get(x_4, 2);
lean::inc(x_837);
lean::inc(x_836);
lean::dec(x_4);
x_838 = lean::cnstr_get(x_679, 0);
lean::inc(x_838);
x_839 = lean::cnstr_get(x_679, 1);
lean::inc(x_839);
x_840 = lean::cnstr_get(x_679, 2);
lean::inc(x_840);
x_841 = lean::cnstr_get(x_679, 3);
lean::inc(x_841);
if (lean::is_exclusive(x_679)) {
 lean::cnstr_release(x_679, 0);
 lean::cnstr_release(x_679, 1);
 lean::cnstr_release(x_679, 2);
 lean::cnstr_release(x_679, 3);
 x_842 = x_679;
} else {
 lean::dec_ref(x_679);
 x_842 = lean::box(0);
}
lean::inc(x_235);
if (lean::is_scalar(x_842)) {
 x_843 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_843 = x_842;
}
lean::cnstr_set(x_843, 0, x_807);
lean::cnstr_set(x_843, 1, x_809);
lean::cnstr_set(x_843, 2, x_810);
lean::cnstr_set(x_843, 3, x_235);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_844 = x_235;
} else {
 lean::dec_ref(x_235);
 x_844 = lean::box(0);
}
lean::cnstr_set_uint8(x_843, sizeof(void*)*4, x_806);
x_845 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_845, 0, x_843);
lean::cnstr_set(x_845, 1, x_2);
lean::cnstr_set(x_845, 2, x_3);
lean::cnstr_set(x_845, 3, x_838);
lean::cnstr_set_uint8(x_845, sizeof(void*)*4, x_639);
if (lean::is_scalar(x_844)) {
 x_846 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_846 = x_844;
}
lean::cnstr_set(x_846, 0, x_841);
lean::cnstr_set(x_846, 1, x_836);
lean::cnstr_set(x_846, 2, x_837);
lean::cnstr_set(x_846, 3, x_807);
lean::cnstr_set_uint8(x_846, sizeof(void*)*4, x_639);
lean::cnstr_set(x_1, 3, x_846);
lean::cnstr_set(x_1, 2, x_840);
lean::cnstr_set(x_1, 1, x_839);
lean::cnstr_set(x_1, 0, x_845);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_806);
return x_1;
}
}
else
{
obj* x_847; obj* x_848; obj* x_849; obj* x_850; obj* x_851; obj* x_852; obj* x_853; obj* x_854; obj* x_855; obj* x_856; obj* x_857; obj* x_858; obj* x_859; obj* x_860; obj* x_861; 
x_847 = lean::cnstr_get(x_1, 1);
x_848 = lean::cnstr_get(x_1, 2);
lean::inc(x_848);
lean::inc(x_847);
lean::dec(x_1);
x_849 = lean::cnstr_get(x_4, 1);
lean::inc(x_849);
x_850 = lean::cnstr_get(x_4, 2);
lean::inc(x_850);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_851 = x_4;
} else {
 lean::dec_ref(x_4);
 x_851 = lean::box(0);
}
x_852 = lean::cnstr_get(x_679, 0);
lean::inc(x_852);
x_853 = lean::cnstr_get(x_679, 1);
lean::inc(x_853);
x_854 = lean::cnstr_get(x_679, 2);
lean::inc(x_854);
x_855 = lean::cnstr_get(x_679, 3);
lean::inc(x_855);
if (lean::is_exclusive(x_679)) {
 lean::cnstr_release(x_679, 0);
 lean::cnstr_release(x_679, 1);
 lean::cnstr_release(x_679, 2);
 lean::cnstr_release(x_679, 3);
 x_856 = x_679;
} else {
 lean::dec_ref(x_679);
 x_856 = lean::box(0);
}
lean::inc(x_235);
if (lean::is_scalar(x_856)) {
 x_857 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_857 = x_856;
}
lean::cnstr_set(x_857, 0, x_807);
lean::cnstr_set(x_857, 1, x_847);
lean::cnstr_set(x_857, 2, x_848);
lean::cnstr_set(x_857, 3, x_235);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_858 = x_235;
} else {
 lean::dec_ref(x_235);
 x_858 = lean::box(0);
}
lean::cnstr_set_uint8(x_857, sizeof(void*)*4, x_806);
if (lean::is_scalar(x_851)) {
 x_859 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_859 = x_851;
}
lean::cnstr_set(x_859, 0, x_857);
lean::cnstr_set(x_859, 1, x_2);
lean::cnstr_set(x_859, 2, x_3);
lean::cnstr_set(x_859, 3, x_852);
lean::cnstr_set_uint8(x_859, sizeof(void*)*4, x_639);
if (lean::is_scalar(x_858)) {
 x_860 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_860 = x_858;
}
lean::cnstr_set(x_860, 0, x_855);
lean::cnstr_set(x_860, 1, x_849);
lean::cnstr_set(x_860, 2, x_850);
lean::cnstr_set(x_860, 3, x_807);
lean::cnstr_set_uint8(x_860, sizeof(void*)*4, x_639);
x_861 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_861, 0, x_859);
lean::cnstr_set(x_861, 1, x_853);
lean::cnstr_set(x_861, 2, x_854);
lean::cnstr_set(x_861, 3, x_860);
lean::cnstr_set_uint8(x_861, sizeof(void*)*4, x_806);
return x_861;
}
}
else
{
uint8 x_862; 
x_862 = lean::cnstr_get_uint8(x_807, sizeof(void*)*4);
if (x_862 == 0)
{
uint8 x_863; 
x_863 = !lean::is_exclusive(x_1);
if (x_863 == 0)
{
obj* x_864; obj* x_865; obj* x_866; obj* x_867; uint8 x_868; 
x_864 = lean::cnstr_get(x_1, 1);
x_865 = lean::cnstr_get(x_1, 2);
x_866 = lean::cnstr_get(x_1, 3);
lean::dec(x_866);
x_867 = lean::cnstr_get(x_1, 0);
lean::dec(x_867);
x_868 = !lean::is_exclusive(x_4);
if (x_868 == 0)
{
obj* x_869; obj* x_870; obj* x_871; obj* x_872; uint8 x_873; 
x_869 = lean::cnstr_get(x_4, 1);
x_870 = lean::cnstr_get(x_4, 2);
x_871 = lean::cnstr_get(x_4, 3);
lean::dec(x_871);
x_872 = lean::cnstr_get(x_4, 0);
lean::dec(x_872);
x_873 = !lean::is_exclusive(x_679);
if (x_873 == 0)
{
uint8 x_874; 
x_874 = !lean::is_exclusive(x_807);
if (x_874 == 0)
{
obj* x_875; obj* x_876; obj* x_877; obj* x_878; uint8 x_879; 
x_875 = lean::cnstr_get(x_807, 0);
x_876 = lean::cnstr_get(x_807, 1);
x_877 = lean::cnstr_get(x_807, 2);
x_878 = lean::cnstr_get(x_807, 3);
lean::inc(x_235);
lean::cnstr_set(x_807, 3, x_235);
lean::cnstr_set(x_807, 2, x_865);
lean::cnstr_set(x_807, 1, x_864);
lean::cnstr_set(x_807, 0, x_234);
x_879 = !lean::is_exclusive(x_235);
if (x_879 == 0)
{
obj* x_880; obj* x_881; obj* x_882; obj* x_883; 
x_880 = lean::cnstr_get(x_235, 3);
lean::dec(x_880);
x_881 = lean::cnstr_get(x_235, 2);
lean::dec(x_881);
x_882 = lean::cnstr_get(x_235, 1);
lean::dec(x_882);
x_883 = lean::cnstr_get(x_235, 0);
lean::dec(x_883);
lean::cnstr_set_uint8(x_679, sizeof(void*)*4, x_862);
lean::cnstr_set(x_4, 3, x_679);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_807);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_639);
lean::cnstr_set(x_235, 3, x_878);
lean::cnstr_set(x_235, 2, x_877);
lean::cnstr_set(x_235, 1, x_876);
lean::cnstr_set(x_235, 0, x_875);
lean::cnstr_set(x_1, 2, x_870);
lean::cnstr_set(x_1, 1, x_869);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_862);
return x_1;
}
else
{
obj* x_884; 
lean::dec(x_235);
lean::cnstr_set_uint8(x_679, sizeof(void*)*4, x_862);
lean::cnstr_set(x_4, 3, x_679);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_807);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_639);
x_884 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_884, 0, x_875);
lean::cnstr_set(x_884, 1, x_876);
lean::cnstr_set(x_884, 2, x_877);
lean::cnstr_set(x_884, 3, x_878);
lean::cnstr_set_uint8(x_884, sizeof(void*)*4, x_639);
lean::cnstr_set(x_1, 3, x_884);
lean::cnstr_set(x_1, 2, x_870);
lean::cnstr_set(x_1, 1, x_869);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_862);
return x_1;
}
}
else
{
obj* x_885; obj* x_886; obj* x_887; obj* x_888; obj* x_889; obj* x_890; obj* x_891; 
x_885 = lean::cnstr_get(x_807, 0);
x_886 = lean::cnstr_get(x_807, 1);
x_887 = lean::cnstr_get(x_807, 2);
x_888 = lean::cnstr_get(x_807, 3);
lean::inc(x_888);
lean::inc(x_887);
lean::inc(x_886);
lean::inc(x_885);
lean::dec(x_807);
lean::inc(x_235);
x_889 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_889, 0, x_234);
lean::cnstr_set(x_889, 1, x_864);
lean::cnstr_set(x_889, 2, x_865);
lean::cnstr_set(x_889, 3, x_235);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_890 = x_235;
} else {
 lean::dec_ref(x_235);
 x_890 = lean::box(0);
}
lean::cnstr_set_uint8(x_889, sizeof(void*)*4, x_862);
lean::cnstr_set_uint8(x_679, sizeof(void*)*4, x_862);
lean::cnstr_set(x_4, 3, x_679);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_889);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_639);
if (lean::is_scalar(x_890)) {
 x_891 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_891 = x_890;
}
lean::cnstr_set(x_891, 0, x_885);
lean::cnstr_set(x_891, 1, x_886);
lean::cnstr_set(x_891, 2, x_887);
lean::cnstr_set(x_891, 3, x_888);
lean::cnstr_set_uint8(x_891, sizeof(void*)*4, x_639);
lean::cnstr_set(x_1, 3, x_891);
lean::cnstr_set(x_1, 2, x_870);
lean::cnstr_set(x_1, 1, x_869);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_862);
return x_1;
}
}
else
{
obj* x_892; obj* x_893; obj* x_894; obj* x_895; obj* x_896; obj* x_897; obj* x_898; obj* x_899; obj* x_900; obj* x_901; obj* x_902; obj* x_903; obj* x_904; 
x_892 = lean::cnstr_get(x_679, 0);
x_893 = lean::cnstr_get(x_679, 1);
x_894 = lean::cnstr_get(x_679, 2);
x_895 = lean::cnstr_get(x_679, 3);
lean::inc(x_895);
lean::inc(x_894);
lean::inc(x_893);
lean::inc(x_892);
lean::dec(x_679);
x_896 = lean::cnstr_get(x_807, 0);
lean::inc(x_896);
x_897 = lean::cnstr_get(x_807, 1);
lean::inc(x_897);
x_898 = lean::cnstr_get(x_807, 2);
lean::inc(x_898);
x_899 = lean::cnstr_get(x_807, 3);
lean::inc(x_899);
if (lean::is_exclusive(x_807)) {
 lean::cnstr_release(x_807, 0);
 lean::cnstr_release(x_807, 1);
 lean::cnstr_release(x_807, 2);
 lean::cnstr_release(x_807, 3);
 x_900 = x_807;
} else {
 lean::dec_ref(x_807);
 x_900 = lean::box(0);
}
lean::inc(x_235);
if (lean::is_scalar(x_900)) {
 x_901 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_901 = x_900;
}
lean::cnstr_set(x_901, 0, x_234);
lean::cnstr_set(x_901, 1, x_864);
lean::cnstr_set(x_901, 2, x_865);
lean::cnstr_set(x_901, 3, x_235);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_902 = x_235;
} else {
 lean::dec_ref(x_235);
 x_902 = lean::box(0);
}
lean::cnstr_set_uint8(x_901, sizeof(void*)*4, x_862);
x_903 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_903, 0, x_892);
lean::cnstr_set(x_903, 1, x_893);
lean::cnstr_set(x_903, 2, x_894);
lean::cnstr_set(x_903, 3, x_895);
lean::cnstr_set_uint8(x_903, sizeof(void*)*4, x_862);
lean::cnstr_set(x_4, 3, x_903);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_901);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_639);
if (lean::is_scalar(x_902)) {
 x_904 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_904 = x_902;
}
lean::cnstr_set(x_904, 0, x_896);
lean::cnstr_set(x_904, 1, x_897);
lean::cnstr_set(x_904, 2, x_898);
lean::cnstr_set(x_904, 3, x_899);
lean::cnstr_set_uint8(x_904, sizeof(void*)*4, x_639);
lean::cnstr_set(x_1, 3, x_904);
lean::cnstr_set(x_1, 2, x_870);
lean::cnstr_set(x_1, 1, x_869);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_862);
return x_1;
}
}
else
{
obj* x_905; obj* x_906; obj* x_907; obj* x_908; obj* x_909; obj* x_910; obj* x_911; obj* x_912; obj* x_913; obj* x_914; obj* x_915; obj* x_916; obj* x_917; obj* x_918; obj* x_919; obj* x_920; obj* x_921; 
x_905 = lean::cnstr_get(x_4, 1);
x_906 = lean::cnstr_get(x_4, 2);
lean::inc(x_906);
lean::inc(x_905);
lean::dec(x_4);
x_907 = lean::cnstr_get(x_679, 0);
lean::inc(x_907);
x_908 = lean::cnstr_get(x_679, 1);
lean::inc(x_908);
x_909 = lean::cnstr_get(x_679, 2);
lean::inc(x_909);
x_910 = lean::cnstr_get(x_679, 3);
lean::inc(x_910);
if (lean::is_exclusive(x_679)) {
 lean::cnstr_release(x_679, 0);
 lean::cnstr_release(x_679, 1);
 lean::cnstr_release(x_679, 2);
 lean::cnstr_release(x_679, 3);
 x_911 = x_679;
} else {
 lean::dec_ref(x_679);
 x_911 = lean::box(0);
}
x_912 = lean::cnstr_get(x_807, 0);
lean::inc(x_912);
x_913 = lean::cnstr_get(x_807, 1);
lean::inc(x_913);
x_914 = lean::cnstr_get(x_807, 2);
lean::inc(x_914);
x_915 = lean::cnstr_get(x_807, 3);
lean::inc(x_915);
if (lean::is_exclusive(x_807)) {
 lean::cnstr_release(x_807, 0);
 lean::cnstr_release(x_807, 1);
 lean::cnstr_release(x_807, 2);
 lean::cnstr_release(x_807, 3);
 x_916 = x_807;
} else {
 lean::dec_ref(x_807);
 x_916 = lean::box(0);
}
lean::inc(x_235);
if (lean::is_scalar(x_916)) {
 x_917 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_917 = x_916;
}
lean::cnstr_set(x_917, 0, x_234);
lean::cnstr_set(x_917, 1, x_864);
lean::cnstr_set(x_917, 2, x_865);
lean::cnstr_set(x_917, 3, x_235);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_918 = x_235;
} else {
 lean::dec_ref(x_235);
 x_918 = lean::box(0);
}
lean::cnstr_set_uint8(x_917, sizeof(void*)*4, x_862);
if (lean::is_scalar(x_911)) {
 x_919 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_919 = x_911;
}
lean::cnstr_set(x_919, 0, x_907);
lean::cnstr_set(x_919, 1, x_908);
lean::cnstr_set(x_919, 2, x_909);
lean::cnstr_set(x_919, 3, x_910);
lean::cnstr_set_uint8(x_919, sizeof(void*)*4, x_862);
x_920 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_920, 0, x_917);
lean::cnstr_set(x_920, 1, x_2);
lean::cnstr_set(x_920, 2, x_3);
lean::cnstr_set(x_920, 3, x_919);
lean::cnstr_set_uint8(x_920, sizeof(void*)*4, x_639);
if (lean::is_scalar(x_918)) {
 x_921 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_921 = x_918;
}
lean::cnstr_set(x_921, 0, x_912);
lean::cnstr_set(x_921, 1, x_913);
lean::cnstr_set(x_921, 2, x_914);
lean::cnstr_set(x_921, 3, x_915);
lean::cnstr_set_uint8(x_921, sizeof(void*)*4, x_639);
lean::cnstr_set(x_1, 3, x_921);
lean::cnstr_set(x_1, 2, x_906);
lean::cnstr_set(x_1, 1, x_905);
lean::cnstr_set(x_1, 0, x_920);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_862);
return x_1;
}
}
else
{
obj* x_922; obj* x_923; obj* x_924; obj* x_925; obj* x_926; obj* x_927; obj* x_928; obj* x_929; obj* x_930; obj* x_931; obj* x_932; obj* x_933; obj* x_934; obj* x_935; obj* x_936; obj* x_937; obj* x_938; obj* x_939; obj* x_940; obj* x_941; obj* x_942; 
x_922 = lean::cnstr_get(x_1, 1);
x_923 = lean::cnstr_get(x_1, 2);
lean::inc(x_923);
lean::inc(x_922);
lean::dec(x_1);
x_924 = lean::cnstr_get(x_4, 1);
lean::inc(x_924);
x_925 = lean::cnstr_get(x_4, 2);
lean::inc(x_925);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_926 = x_4;
} else {
 lean::dec_ref(x_4);
 x_926 = lean::box(0);
}
x_927 = lean::cnstr_get(x_679, 0);
lean::inc(x_927);
x_928 = lean::cnstr_get(x_679, 1);
lean::inc(x_928);
x_929 = lean::cnstr_get(x_679, 2);
lean::inc(x_929);
x_930 = lean::cnstr_get(x_679, 3);
lean::inc(x_930);
if (lean::is_exclusive(x_679)) {
 lean::cnstr_release(x_679, 0);
 lean::cnstr_release(x_679, 1);
 lean::cnstr_release(x_679, 2);
 lean::cnstr_release(x_679, 3);
 x_931 = x_679;
} else {
 lean::dec_ref(x_679);
 x_931 = lean::box(0);
}
x_932 = lean::cnstr_get(x_807, 0);
lean::inc(x_932);
x_933 = lean::cnstr_get(x_807, 1);
lean::inc(x_933);
x_934 = lean::cnstr_get(x_807, 2);
lean::inc(x_934);
x_935 = lean::cnstr_get(x_807, 3);
lean::inc(x_935);
if (lean::is_exclusive(x_807)) {
 lean::cnstr_release(x_807, 0);
 lean::cnstr_release(x_807, 1);
 lean::cnstr_release(x_807, 2);
 lean::cnstr_release(x_807, 3);
 x_936 = x_807;
} else {
 lean::dec_ref(x_807);
 x_936 = lean::box(0);
}
lean::inc(x_235);
if (lean::is_scalar(x_936)) {
 x_937 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_937 = x_936;
}
lean::cnstr_set(x_937, 0, x_234);
lean::cnstr_set(x_937, 1, x_922);
lean::cnstr_set(x_937, 2, x_923);
lean::cnstr_set(x_937, 3, x_235);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_938 = x_235;
} else {
 lean::dec_ref(x_235);
 x_938 = lean::box(0);
}
lean::cnstr_set_uint8(x_937, sizeof(void*)*4, x_862);
if (lean::is_scalar(x_931)) {
 x_939 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_939 = x_931;
}
lean::cnstr_set(x_939, 0, x_927);
lean::cnstr_set(x_939, 1, x_928);
lean::cnstr_set(x_939, 2, x_929);
lean::cnstr_set(x_939, 3, x_930);
lean::cnstr_set_uint8(x_939, sizeof(void*)*4, x_862);
if (lean::is_scalar(x_926)) {
 x_940 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_940 = x_926;
}
lean::cnstr_set(x_940, 0, x_937);
lean::cnstr_set(x_940, 1, x_2);
lean::cnstr_set(x_940, 2, x_3);
lean::cnstr_set(x_940, 3, x_939);
lean::cnstr_set_uint8(x_940, sizeof(void*)*4, x_639);
if (lean::is_scalar(x_938)) {
 x_941 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_941 = x_938;
}
lean::cnstr_set(x_941, 0, x_932);
lean::cnstr_set(x_941, 1, x_933);
lean::cnstr_set(x_941, 2, x_934);
lean::cnstr_set(x_941, 3, x_935);
lean::cnstr_set_uint8(x_941, sizeof(void*)*4, x_639);
x_942 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_942, 0, x_940);
lean::cnstr_set(x_942, 1, x_924);
lean::cnstr_set(x_942, 2, x_925);
lean::cnstr_set(x_942, 3, x_941);
lean::cnstr_set_uint8(x_942, sizeof(void*)*4, x_862);
return x_942;
}
}
else
{
uint8 x_943; 
x_943 = !lean::is_exclusive(x_1);
if (x_943 == 0)
{
obj* x_944; obj* x_945; obj* x_946; obj* x_947; uint8 x_948; 
x_944 = lean::cnstr_get(x_1, 1);
x_945 = lean::cnstr_get(x_1, 2);
x_946 = lean::cnstr_get(x_1, 3);
lean::dec(x_946);
x_947 = lean::cnstr_get(x_1, 0);
lean::dec(x_947);
x_948 = !lean::is_exclusive(x_235);
if (x_948 == 0)
{
uint8 x_949; 
x_949 = !lean::is_exclusive(x_4);
if (x_949 == 0)
{
obj* x_950; obj* x_951; obj* x_952; obj* x_953; obj* x_954; obj* x_955; obj* x_956; obj* x_957; uint8 x_958; 
x_950 = lean::cnstr_get(x_235, 0);
x_951 = lean::cnstr_get(x_235, 1);
x_952 = lean::cnstr_get(x_235, 2);
x_953 = lean::cnstr_get(x_235, 3);
x_954 = lean::cnstr_get(x_4, 1);
x_955 = lean::cnstr_get(x_4, 2);
x_956 = lean::cnstr_get(x_4, 3);
lean::dec(x_956);
x_957 = lean::cnstr_get(x_4, 0);
lean::dec(x_957);
x_958 = !lean::is_exclusive(x_679);
if (x_958 == 0)
{
obj* x_959; obj* x_960; obj* x_961; obj* x_962; obj* x_963; 
x_959 = lean::cnstr_get(x_679, 0);
x_960 = lean::cnstr_get(x_679, 1);
x_961 = lean::cnstr_get(x_679, 2);
x_962 = lean::cnstr_get(x_679, 3);
lean::cnstr_set(x_679, 3, x_953);
lean::cnstr_set(x_679, 2, x_952);
lean::cnstr_set(x_679, 1, x_951);
lean::cnstr_set(x_679, 0, x_950);
lean::cnstr_set_uint8(x_679, sizeof(void*)*4, x_862);
lean::cnstr_set(x_4, 3, x_679);
lean::cnstr_set(x_4, 2, x_945);
lean::cnstr_set(x_4, 1, x_944);
lean::cnstr_set(x_4, 0, x_234);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_806);
lean::cnstr_set(x_235, 3, x_959);
lean::cnstr_set(x_235, 2, x_3);
lean::cnstr_set(x_235, 1, x_2);
lean::cnstr_set(x_235, 0, x_4);
lean::cnstr_set_uint8(x_235, sizeof(void*)*4, x_862);
lean::cnstr_set(x_1, 3, x_807);
lean::cnstr_set(x_1, 2, x_955);
lean::cnstr_set(x_1, 1, x_954);
lean::cnstr_set(x_1, 0, x_962);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_862);
x_963 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_963, 0, x_235);
lean::cnstr_set(x_963, 1, x_960);
lean::cnstr_set(x_963, 2, x_961);
lean::cnstr_set(x_963, 3, x_1);
lean::cnstr_set_uint8(x_963, sizeof(void*)*4, x_806);
return x_963;
}
else
{
obj* x_964; obj* x_965; obj* x_966; obj* x_967; obj* x_968; obj* x_969; 
x_964 = lean::cnstr_get(x_679, 0);
x_965 = lean::cnstr_get(x_679, 1);
x_966 = lean::cnstr_get(x_679, 2);
x_967 = lean::cnstr_get(x_679, 3);
lean::inc(x_967);
lean::inc(x_966);
lean::inc(x_965);
lean::inc(x_964);
lean::dec(x_679);
x_968 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_968, 0, x_950);
lean::cnstr_set(x_968, 1, x_951);
lean::cnstr_set(x_968, 2, x_952);
lean::cnstr_set(x_968, 3, x_953);
lean::cnstr_set_uint8(x_968, sizeof(void*)*4, x_862);
lean::cnstr_set(x_4, 3, x_968);
lean::cnstr_set(x_4, 2, x_945);
lean::cnstr_set(x_4, 1, x_944);
lean::cnstr_set(x_4, 0, x_234);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_806);
lean::cnstr_set(x_235, 3, x_964);
lean::cnstr_set(x_235, 2, x_3);
lean::cnstr_set(x_235, 1, x_2);
lean::cnstr_set(x_235, 0, x_4);
lean::cnstr_set_uint8(x_235, sizeof(void*)*4, x_862);
lean::cnstr_set(x_1, 3, x_807);
lean::cnstr_set(x_1, 2, x_955);
lean::cnstr_set(x_1, 1, x_954);
lean::cnstr_set(x_1, 0, x_967);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_862);
x_969 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_969, 0, x_235);
lean::cnstr_set(x_969, 1, x_965);
lean::cnstr_set(x_969, 2, x_966);
lean::cnstr_set(x_969, 3, x_1);
lean::cnstr_set_uint8(x_969, sizeof(void*)*4, x_806);
return x_969;
}
}
else
{
obj* x_970; obj* x_971; obj* x_972; obj* x_973; obj* x_974; obj* x_975; obj* x_976; obj* x_977; obj* x_978; obj* x_979; obj* x_980; obj* x_981; obj* x_982; obj* x_983; 
x_970 = lean::cnstr_get(x_235, 0);
x_971 = lean::cnstr_get(x_235, 1);
x_972 = lean::cnstr_get(x_235, 2);
x_973 = lean::cnstr_get(x_235, 3);
x_974 = lean::cnstr_get(x_4, 1);
x_975 = lean::cnstr_get(x_4, 2);
lean::inc(x_975);
lean::inc(x_974);
lean::dec(x_4);
x_976 = lean::cnstr_get(x_679, 0);
lean::inc(x_976);
x_977 = lean::cnstr_get(x_679, 1);
lean::inc(x_977);
x_978 = lean::cnstr_get(x_679, 2);
lean::inc(x_978);
x_979 = lean::cnstr_get(x_679, 3);
lean::inc(x_979);
if (lean::is_exclusive(x_679)) {
 lean::cnstr_release(x_679, 0);
 lean::cnstr_release(x_679, 1);
 lean::cnstr_release(x_679, 2);
 lean::cnstr_release(x_679, 3);
 x_980 = x_679;
} else {
 lean::dec_ref(x_679);
 x_980 = lean::box(0);
}
if (lean::is_scalar(x_980)) {
 x_981 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_981 = x_980;
}
lean::cnstr_set(x_981, 0, x_970);
lean::cnstr_set(x_981, 1, x_971);
lean::cnstr_set(x_981, 2, x_972);
lean::cnstr_set(x_981, 3, x_973);
lean::cnstr_set_uint8(x_981, sizeof(void*)*4, x_862);
x_982 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_982, 0, x_234);
lean::cnstr_set(x_982, 1, x_944);
lean::cnstr_set(x_982, 2, x_945);
lean::cnstr_set(x_982, 3, x_981);
lean::cnstr_set_uint8(x_982, sizeof(void*)*4, x_806);
lean::cnstr_set(x_235, 3, x_976);
lean::cnstr_set(x_235, 2, x_3);
lean::cnstr_set(x_235, 1, x_2);
lean::cnstr_set(x_235, 0, x_982);
lean::cnstr_set_uint8(x_235, sizeof(void*)*4, x_862);
lean::cnstr_set(x_1, 3, x_807);
lean::cnstr_set(x_1, 2, x_975);
lean::cnstr_set(x_1, 1, x_974);
lean::cnstr_set(x_1, 0, x_979);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_862);
x_983 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_983, 0, x_235);
lean::cnstr_set(x_983, 1, x_977);
lean::cnstr_set(x_983, 2, x_978);
lean::cnstr_set(x_983, 3, x_1);
lean::cnstr_set_uint8(x_983, sizeof(void*)*4, x_806);
return x_983;
}
}
else
{
obj* x_984; obj* x_985; obj* x_986; obj* x_987; obj* x_988; obj* x_989; obj* x_990; obj* x_991; obj* x_992; obj* x_993; obj* x_994; obj* x_995; obj* x_996; obj* x_997; obj* x_998; obj* x_999; 
x_984 = lean::cnstr_get(x_235, 0);
x_985 = lean::cnstr_get(x_235, 1);
x_986 = lean::cnstr_get(x_235, 2);
x_987 = lean::cnstr_get(x_235, 3);
lean::inc(x_987);
lean::inc(x_986);
lean::inc(x_985);
lean::inc(x_984);
lean::dec(x_235);
x_988 = lean::cnstr_get(x_4, 1);
lean::inc(x_988);
x_989 = lean::cnstr_get(x_4, 2);
lean::inc(x_989);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_990 = x_4;
} else {
 lean::dec_ref(x_4);
 x_990 = lean::box(0);
}
x_991 = lean::cnstr_get(x_679, 0);
lean::inc(x_991);
x_992 = lean::cnstr_get(x_679, 1);
lean::inc(x_992);
x_993 = lean::cnstr_get(x_679, 2);
lean::inc(x_993);
x_994 = lean::cnstr_get(x_679, 3);
lean::inc(x_994);
if (lean::is_exclusive(x_679)) {
 lean::cnstr_release(x_679, 0);
 lean::cnstr_release(x_679, 1);
 lean::cnstr_release(x_679, 2);
 lean::cnstr_release(x_679, 3);
 x_995 = x_679;
} else {
 lean::dec_ref(x_679);
 x_995 = lean::box(0);
}
if (lean::is_scalar(x_995)) {
 x_996 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_996 = x_995;
}
lean::cnstr_set(x_996, 0, x_984);
lean::cnstr_set(x_996, 1, x_985);
lean::cnstr_set(x_996, 2, x_986);
lean::cnstr_set(x_996, 3, x_987);
lean::cnstr_set_uint8(x_996, sizeof(void*)*4, x_862);
if (lean::is_scalar(x_990)) {
 x_997 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_997 = x_990;
}
lean::cnstr_set(x_997, 0, x_234);
lean::cnstr_set(x_997, 1, x_944);
lean::cnstr_set(x_997, 2, x_945);
lean::cnstr_set(x_997, 3, x_996);
lean::cnstr_set_uint8(x_997, sizeof(void*)*4, x_806);
x_998 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_998, 0, x_997);
lean::cnstr_set(x_998, 1, x_2);
lean::cnstr_set(x_998, 2, x_3);
lean::cnstr_set(x_998, 3, x_991);
lean::cnstr_set_uint8(x_998, sizeof(void*)*4, x_862);
lean::cnstr_set(x_1, 3, x_807);
lean::cnstr_set(x_1, 2, x_989);
lean::cnstr_set(x_1, 1, x_988);
lean::cnstr_set(x_1, 0, x_994);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_862);
x_999 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_999, 0, x_998);
lean::cnstr_set(x_999, 1, x_992);
lean::cnstr_set(x_999, 2, x_993);
lean::cnstr_set(x_999, 3, x_1);
lean::cnstr_set_uint8(x_999, sizeof(void*)*4, x_806);
return x_999;
}
}
else
{
obj* x_1000; obj* x_1001; obj* x_1002; obj* x_1003; obj* x_1004; obj* x_1005; obj* x_1006; obj* x_1007; obj* x_1008; obj* x_1009; obj* x_1010; obj* x_1011; obj* x_1012; obj* x_1013; obj* x_1014; obj* x_1015; obj* x_1016; obj* x_1017; obj* x_1018; obj* x_1019; 
x_1000 = lean::cnstr_get(x_1, 1);
x_1001 = lean::cnstr_get(x_1, 2);
lean::inc(x_1001);
lean::inc(x_1000);
lean::dec(x_1);
x_1002 = lean::cnstr_get(x_235, 0);
lean::inc(x_1002);
x_1003 = lean::cnstr_get(x_235, 1);
lean::inc(x_1003);
x_1004 = lean::cnstr_get(x_235, 2);
lean::inc(x_1004);
x_1005 = lean::cnstr_get(x_235, 3);
lean::inc(x_1005);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_1006 = x_235;
} else {
 lean::dec_ref(x_235);
 x_1006 = lean::box(0);
}
x_1007 = lean::cnstr_get(x_4, 1);
lean::inc(x_1007);
x_1008 = lean::cnstr_get(x_4, 2);
lean::inc(x_1008);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1009 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1009 = lean::box(0);
}
x_1010 = lean::cnstr_get(x_679, 0);
lean::inc(x_1010);
x_1011 = lean::cnstr_get(x_679, 1);
lean::inc(x_1011);
x_1012 = lean::cnstr_get(x_679, 2);
lean::inc(x_1012);
x_1013 = lean::cnstr_get(x_679, 3);
lean::inc(x_1013);
if (lean::is_exclusive(x_679)) {
 lean::cnstr_release(x_679, 0);
 lean::cnstr_release(x_679, 1);
 lean::cnstr_release(x_679, 2);
 lean::cnstr_release(x_679, 3);
 x_1014 = x_679;
} else {
 lean::dec_ref(x_679);
 x_1014 = lean::box(0);
}
if (lean::is_scalar(x_1014)) {
 x_1015 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1015 = x_1014;
}
lean::cnstr_set(x_1015, 0, x_1002);
lean::cnstr_set(x_1015, 1, x_1003);
lean::cnstr_set(x_1015, 2, x_1004);
lean::cnstr_set(x_1015, 3, x_1005);
lean::cnstr_set_uint8(x_1015, sizeof(void*)*4, x_862);
if (lean::is_scalar(x_1009)) {
 x_1016 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1016 = x_1009;
}
lean::cnstr_set(x_1016, 0, x_234);
lean::cnstr_set(x_1016, 1, x_1000);
lean::cnstr_set(x_1016, 2, x_1001);
lean::cnstr_set(x_1016, 3, x_1015);
lean::cnstr_set_uint8(x_1016, sizeof(void*)*4, x_806);
if (lean::is_scalar(x_1006)) {
 x_1017 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1017 = x_1006;
}
lean::cnstr_set(x_1017, 0, x_1016);
lean::cnstr_set(x_1017, 1, x_2);
lean::cnstr_set(x_1017, 2, x_3);
lean::cnstr_set(x_1017, 3, x_1010);
lean::cnstr_set_uint8(x_1017, sizeof(void*)*4, x_862);
x_1018 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1018, 0, x_1013);
lean::cnstr_set(x_1018, 1, x_1007);
lean::cnstr_set(x_1018, 2, x_1008);
lean::cnstr_set(x_1018, 3, x_807);
lean::cnstr_set_uint8(x_1018, sizeof(void*)*4, x_862);
x_1019 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1019, 0, x_1017);
lean::cnstr_set(x_1019, 1, x_1011);
lean::cnstr_set(x_1019, 2, x_1012);
lean::cnstr_set(x_1019, 3, x_1018);
lean::cnstr_set_uint8(x_1019, sizeof(void*)*4, x_806);
return x_1019;
}
}
}
}
else
{
obj* x_1020; 
x_1020 = lean::cnstr_get(x_4, 3);
lean::inc(x_1020);
if (lean::obj_tag(x_1020) == 0)
{
uint8 x_1021; 
x_1021 = !lean::is_exclusive(x_679);
if (x_1021 == 0)
{
obj* x_1022; obj* x_1023; obj* x_1024; obj* x_1025; uint8 x_1026; 
x_1022 = lean::cnstr_get(x_679, 3);
lean::dec(x_1022);
x_1023 = lean::cnstr_get(x_679, 2);
lean::dec(x_1023);
x_1024 = lean::cnstr_get(x_679, 1);
lean::dec(x_1024);
x_1025 = lean::cnstr_get(x_679, 0);
lean::dec(x_1025);
x_1026 = !lean::is_exclusive(x_1);
if (x_1026 == 0)
{
obj* x_1027; obj* x_1028; obj* x_1029; obj* x_1030; uint8 x_1031; 
x_1027 = lean::cnstr_get(x_1, 1);
x_1028 = lean::cnstr_get(x_1, 2);
x_1029 = lean::cnstr_get(x_1, 3);
lean::dec(x_1029);
x_1030 = lean::cnstr_get(x_1, 0);
lean::dec(x_1030);
x_1031 = !lean::is_exclusive(x_235);
if (x_1031 == 0)
{
obj* x_1032; obj* x_1033; obj* x_1034; obj* x_1035; 
x_1032 = lean::cnstr_get(x_235, 0);
x_1033 = lean::cnstr_get(x_235, 1);
x_1034 = lean::cnstr_get(x_235, 2);
x_1035 = lean::cnstr_get(x_235, 3);
lean::cnstr_set(x_679, 3, x_1035);
lean::cnstr_set(x_679, 2, x_1034);
lean::cnstr_set(x_679, 1, x_1033);
lean::cnstr_set(x_679, 0, x_1032);
lean::cnstr_set(x_235, 3, x_679);
lean::cnstr_set(x_235, 2, x_1028);
lean::cnstr_set(x_235, 1, x_1027);
lean::cnstr_set(x_235, 0, x_1020);
lean::cnstr_set_uint8(x_235, sizeof(void*)*4, x_678);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_235);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_806);
return x_1;
}
else
{
obj* x_1036; obj* x_1037; obj* x_1038; obj* x_1039; obj* x_1040; 
x_1036 = lean::cnstr_get(x_235, 0);
x_1037 = lean::cnstr_get(x_235, 1);
x_1038 = lean::cnstr_get(x_235, 2);
x_1039 = lean::cnstr_get(x_235, 3);
lean::inc(x_1039);
lean::inc(x_1038);
lean::inc(x_1037);
lean::inc(x_1036);
lean::dec(x_235);
lean::cnstr_set(x_679, 3, x_1039);
lean::cnstr_set(x_679, 2, x_1038);
lean::cnstr_set(x_679, 1, x_1037);
lean::cnstr_set(x_679, 0, x_1036);
x_1040 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1040, 0, x_1020);
lean::cnstr_set(x_1040, 1, x_1027);
lean::cnstr_set(x_1040, 2, x_1028);
lean::cnstr_set(x_1040, 3, x_679);
lean::cnstr_set_uint8(x_1040, sizeof(void*)*4, x_678);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_1040);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_806);
return x_1;
}
}
else
{
obj* x_1041; obj* x_1042; obj* x_1043; obj* x_1044; obj* x_1045; obj* x_1046; obj* x_1047; obj* x_1048; obj* x_1049; 
x_1041 = lean::cnstr_get(x_1, 1);
x_1042 = lean::cnstr_get(x_1, 2);
lean::inc(x_1042);
lean::inc(x_1041);
lean::dec(x_1);
x_1043 = lean::cnstr_get(x_235, 0);
lean::inc(x_1043);
x_1044 = lean::cnstr_get(x_235, 1);
lean::inc(x_1044);
x_1045 = lean::cnstr_get(x_235, 2);
lean::inc(x_1045);
x_1046 = lean::cnstr_get(x_235, 3);
lean::inc(x_1046);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_1047 = x_235;
} else {
 lean::dec_ref(x_235);
 x_1047 = lean::box(0);
}
lean::cnstr_set(x_679, 3, x_1046);
lean::cnstr_set(x_679, 2, x_1045);
lean::cnstr_set(x_679, 1, x_1044);
lean::cnstr_set(x_679, 0, x_1043);
if (lean::is_scalar(x_1047)) {
 x_1048 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1048 = x_1047;
}
lean::cnstr_set(x_1048, 0, x_1020);
lean::cnstr_set(x_1048, 1, x_1041);
lean::cnstr_set(x_1048, 2, x_1042);
lean::cnstr_set(x_1048, 3, x_679);
lean::cnstr_set_uint8(x_1048, sizeof(void*)*4, x_678);
x_1049 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1049, 0, x_1048);
lean::cnstr_set(x_1049, 1, x_2);
lean::cnstr_set(x_1049, 2, x_3);
lean::cnstr_set(x_1049, 3, x_4);
lean::cnstr_set_uint8(x_1049, sizeof(void*)*4, x_806);
return x_1049;
}
}
else
{
obj* x_1050; obj* x_1051; obj* x_1052; obj* x_1053; obj* x_1054; obj* x_1055; obj* x_1056; obj* x_1057; obj* x_1058; obj* x_1059; obj* x_1060; 
lean::dec(x_679);
x_1050 = lean::cnstr_get(x_1, 1);
lean::inc(x_1050);
x_1051 = lean::cnstr_get(x_1, 2);
lean::inc(x_1051);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_1052 = x_1;
} else {
 lean::dec_ref(x_1);
 x_1052 = lean::box(0);
}
x_1053 = lean::cnstr_get(x_235, 0);
lean::inc(x_1053);
x_1054 = lean::cnstr_get(x_235, 1);
lean::inc(x_1054);
x_1055 = lean::cnstr_get(x_235, 2);
lean::inc(x_1055);
x_1056 = lean::cnstr_get(x_235, 3);
lean::inc(x_1056);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_1057 = x_235;
} else {
 lean::dec_ref(x_235);
 x_1057 = lean::box(0);
}
x_1058 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1058, 0, x_1053);
lean::cnstr_set(x_1058, 1, x_1054);
lean::cnstr_set(x_1058, 2, x_1055);
lean::cnstr_set(x_1058, 3, x_1056);
lean::cnstr_set_uint8(x_1058, sizeof(void*)*4, x_806);
if (lean::is_scalar(x_1057)) {
 x_1059 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1059 = x_1057;
}
lean::cnstr_set(x_1059, 0, x_1020);
lean::cnstr_set(x_1059, 1, x_1050);
lean::cnstr_set(x_1059, 2, x_1051);
lean::cnstr_set(x_1059, 3, x_1058);
lean::cnstr_set_uint8(x_1059, sizeof(void*)*4, x_678);
if (lean::is_scalar(x_1052)) {
 x_1060 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1060 = x_1052;
}
lean::cnstr_set(x_1060, 0, x_1059);
lean::cnstr_set(x_1060, 1, x_2);
lean::cnstr_set(x_1060, 2, x_3);
lean::cnstr_set(x_1060, 3, x_4);
lean::cnstr_set_uint8(x_1060, sizeof(void*)*4, x_806);
return x_1060;
}
}
else
{
uint8 x_1061; 
x_1061 = lean::cnstr_get_uint8(x_1020, sizeof(void*)*4);
if (x_1061 == 0)
{
uint8 x_1062; 
x_1062 = !lean::is_exclusive(x_1);
if (x_1062 == 0)
{
obj* x_1063; obj* x_1064; obj* x_1065; obj* x_1066; uint8 x_1067; 
x_1063 = lean::cnstr_get(x_1, 1);
x_1064 = lean::cnstr_get(x_1, 2);
x_1065 = lean::cnstr_get(x_1, 3);
lean::dec(x_1065);
x_1066 = lean::cnstr_get(x_1, 0);
lean::dec(x_1066);
x_1067 = !lean::is_exclusive(x_235);
if (x_1067 == 0)
{
uint8 x_1068; 
x_1068 = !lean::is_exclusive(x_4);
if (x_1068 == 0)
{
obj* x_1069; obj* x_1070; obj* x_1071; obj* x_1072; obj* x_1073; obj* x_1074; obj* x_1075; obj* x_1076; uint8 x_1077; 
x_1069 = lean::cnstr_get(x_235, 0);
x_1070 = lean::cnstr_get(x_235, 1);
x_1071 = lean::cnstr_get(x_235, 2);
x_1072 = lean::cnstr_get(x_235, 3);
x_1073 = lean::cnstr_get(x_4, 1);
x_1074 = lean::cnstr_get(x_4, 2);
x_1075 = lean::cnstr_get(x_4, 3);
lean::dec(x_1075);
x_1076 = lean::cnstr_get(x_4, 0);
lean::dec(x_1076);
x_1077 = !lean::is_exclusive(x_1020);
if (x_1077 == 0)
{
obj* x_1078; obj* x_1079; obj* x_1080; obj* x_1081; obj* x_1082; 
x_1078 = lean::cnstr_get(x_1020, 0);
x_1079 = lean::cnstr_get(x_1020, 1);
x_1080 = lean::cnstr_get(x_1020, 2);
x_1081 = lean::cnstr_get(x_1020, 3);
lean::cnstr_set(x_1020, 3, x_1072);
lean::cnstr_set(x_1020, 2, x_1071);
lean::cnstr_set(x_1020, 1, x_1070);
lean::cnstr_set(x_1020, 0, x_1069);
lean::cnstr_set_uint8(x_1020, sizeof(void*)*4, x_806);
lean::cnstr_set(x_4, 2, x_1064);
lean::cnstr_set(x_4, 1, x_1063);
lean::cnstr_set(x_4, 0, x_234);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1061);
lean::cnstr_set(x_235, 3, x_679);
lean::cnstr_set(x_235, 2, x_3);
lean::cnstr_set(x_235, 1, x_2);
lean::cnstr_set(x_235, 0, x_4);
lean::cnstr_set_uint8(x_235, sizeof(void*)*4, x_806);
lean::cnstr_set(x_1, 3, x_1081);
lean::cnstr_set(x_1, 2, x_1080);
lean::cnstr_set(x_1, 1, x_1079);
lean::cnstr_set(x_1, 0, x_1078);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_806);
x_1082 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1082, 0, x_235);
lean::cnstr_set(x_1082, 1, x_1073);
lean::cnstr_set(x_1082, 2, x_1074);
lean::cnstr_set(x_1082, 3, x_1);
lean::cnstr_set_uint8(x_1082, sizeof(void*)*4, x_1061);
return x_1082;
}
else
{
obj* x_1083; obj* x_1084; obj* x_1085; obj* x_1086; obj* x_1087; obj* x_1088; 
x_1083 = lean::cnstr_get(x_1020, 0);
x_1084 = lean::cnstr_get(x_1020, 1);
x_1085 = lean::cnstr_get(x_1020, 2);
x_1086 = lean::cnstr_get(x_1020, 3);
lean::inc(x_1086);
lean::inc(x_1085);
lean::inc(x_1084);
lean::inc(x_1083);
lean::dec(x_1020);
x_1087 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1087, 0, x_1069);
lean::cnstr_set(x_1087, 1, x_1070);
lean::cnstr_set(x_1087, 2, x_1071);
lean::cnstr_set(x_1087, 3, x_1072);
lean::cnstr_set_uint8(x_1087, sizeof(void*)*4, x_806);
lean::cnstr_set(x_4, 3, x_1087);
lean::cnstr_set(x_4, 2, x_1064);
lean::cnstr_set(x_4, 1, x_1063);
lean::cnstr_set(x_4, 0, x_234);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1061);
lean::cnstr_set(x_235, 3, x_679);
lean::cnstr_set(x_235, 2, x_3);
lean::cnstr_set(x_235, 1, x_2);
lean::cnstr_set(x_235, 0, x_4);
lean::cnstr_set_uint8(x_235, sizeof(void*)*4, x_806);
lean::cnstr_set(x_1, 3, x_1086);
lean::cnstr_set(x_1, 2, x_1085);
lean::cnstr_set(x_1, 1, x_1084);
lean::cnstr_set(x_1, 0, x_1083);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_806);
x_1088 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1088, 0, x_235);
lean::cnstr_set(x_1088, 1, x_1073);
lean::cnstr_set(x_1088, 2, x_1074);
lean::cnstr_set(x_1088, 3, x_1);
lean::cnstr_set_uint8(x_1088, sizeof(void*)*4, x_1061);
return x_1088;
}
}
else
{
obj* x_1089; obj* x_1090; obj* x_1091; obj* x_1092; obj* x_1093; obj* x_1094; obj* x_1095; obj* x_1096; obj* x_1097; obj* x_1098; obj* x_1099; obj* x_1100; obj* x_1101; obj* x_1102; 
x_1089 = lean::cnstr_get(x_235, 0);
x_1090 = lean::cnstr_get(x_235, 1);
x_1091 = lean::cnstr_get(x_235, 2);
x_1092 = lean::cnstr_get(x_235, 3);
x_1093 = lean::cnstr_get(x_4, 1);
x_1094 = lean::cnstr_get(x_4, 2);
lean::inc(x_1094);
lean::inc(x_1093);
lean::dec(x_4);
x_1095 = lean::cnstr_get(x_1020, 0);
lean::inc(x_1095);
x_1096 = lean::cnstr_get(x_1020, 1);
lean::inc(x_1096);
x_1097 = lean::cnstr_get(x_1020, 2);
lean::inc(x_1097);
x_1098 = lean::cnstr_get(x_1020, 3);
lean::inc(x_1098);
if (lean::is_exclusive(x_1020)) {
 lean::cnstr_release(x_1020, 0);
 lean::cnstr_release(x_1020, 1);
 lean::cnstr_release(x_1020, 2);
 lean::cnstr_release(x_1020, 3);
 x_1099 = x_1020;
} else {
 lean::dec_ref(x_1020);
 x_1099 = lean::box(0);
}
if (lean::is_scalar(x_1099)) {
 x_1100 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1100 = x_1099;
}
lean::cnstr_set(x_1100, 0, x_1089);
lean::cnstr_set(x_1100, 1, x_1090);
lean::cnstr_set(x_1100, 2, x_1091);
lean::cnstr_set(x_1100, 3, x_1092);
lean::cnstr_set_uint8(x_1100, sizeof(void*)*4, x_806);
x_1101 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1101, 0, x_234);
lean::cnstr_set(x_1101, 1, x_1063);
lean::cnstr_set(x_1101, 2, x_1064);
lean::cnstr_set(x_1101, 3, x_1100);
lean::cnstr_set_uint8(x_1101, sizeof(void*)*4, x_1061);
lean::cnstr_set(x_235, 3, x_679);
lean::cnstr_set(x_235, 2, x_3);
lean::cnstr_set(x_235, 1, x_2);
lean::cnstr_set(x_235, 0, x_1101);
lean::cnstr_set_uint8(x_235, sizeof(void*)*4, x_806);
lean::cnstr_set(x_1, 3, x_1098);
lean::cnstr_set(x_1, 2, x_1097);
lean::cnstr_set(x_1, 1, x_1096);
lean::cnstr_set(x_1, 0, x_1095);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_806);
x_1102 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1102, 0, x_235);
lean::cnstr_set(x_1102, 1, x_1093);
lean::cnstr_set(x_1102, 2, x_1094);
lean::cnstr_set(x_1102, 3, x_1);
lean::cnstr_set_uint8(x_1102, sizeof(void*)*4, x_1061);
return x_1102;
}
}
else
{
obj* x_1103; obj* x_1104; obj* x_1105; obj* x_1106; obj* x_1107; obj* x_1108; obj* x_1109; obj* x_1110; obj* x_1111; obj* x_1112; obj* x_1113; obj* x_1114; obj* x_1115; obj* x_1116; obj* x_1117; obj* x_1118; 
x_1103 = lean::cnstr_get(x_235, 0);
x_1104 = lean::cnstr_get(x_235, 1);
x_1105 = lean::cnstr_get(x_235, 2);
x_1106 = lean::cnstr_get(x_235, 3);
lean::inc(x_1106);
lean::inc(x_1105);
lean::inc(x_1104);
lean::inc(x_1103);
lean::dec(x_235);
x_1107 = lean::cnstr_get(x_4, 1);
lean::inc(x_1107);
x_1108 = lean::cnstr_get(x_4, 2);
lean::inc(x_1108);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1109 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1109 = lean::box(0);
}
x_1110 = lean::cnstr_get(x_1020, 0);
lean::inc(x_1110);
x_1111 = lean::cnstr_get(x_1020, 1);
lean::inc(x_1111);
x_1112 = lean::cnstr_get(x_1020, 2);
lean::inc(x_1112);
x_1113 = lean::cnstr_get(x_1020, 3);
lean::inc(x_1113);
if (lean::is_exclusive(x_1020)) {
 lean::cnstr_release(x_1020, 0);
 lean::cnstr_release(x_1020, 1);
 lean::cnstr_release(x_1020, 2);
 lean::cnstr_release(x_1020, 3);
 x_1114 = x_1020;
} else {
 lean::dec_ref(x_1020);
 x_1114 = lean::box(0);
}
if (lean::is_scalar(x_1114)) {
 x_1115 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1115 = x_1114;
}
lean::cnstr_set(x_1115, 0, x_1103);
lean::cnstr_set(x_1115, 1, x_1104);
lean::cnstr_set(x_1115, 2, x_1105);
lean::cnstr_set(x_1115, 3, x_1106);
lean::cnstr_set_uint8(x_1115, sizeof(void*)*4, x_806);
if (lean::is_scalar(x_1109)) {
 x_1116 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1116 = x_1109;
}
lean::cnstr_set(x_1116, 0, x_234);
lean::cnstr_set(x_1116, 1, x_1063);
lean::cnstr_set(x_1116, 2, x_1064);
lean::cnstr_set(x_1116, 3, x_1115);
lean::cnstr_set_uint8(x_1116, sizeof(void*)*4, x_1061);
x_1117 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1117, 0, x_1116);
lean::cnstr_set(x_1117, 1, x_2);
lean::cnstr_set(x_1117, 2, x_3);
lean::cnstr_set(x_1117, 3, x_679);
lean::cnstr_set_uint8(x_1117, sizeof(void*)*4, x_806);
lean::cnstr_set(x_1, 3, x_1113);
lean::cnstr_set(x_1, 2, x_1112);
lean::cnstr_set(x_1, 1, x_1111);
lean::cnstr_set(x_1, 0, x_1110);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_806);
x_1118 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1118, 0, x_1117);
lean::cnstr_set(x_1118, 1, x_1107);
lean::cnstr_set(x_1118, 2, x_1108);
lean::cnstr_set(x_1118, 3, x_1);
lean::cnstr_set_uint8(x_1118, sizeof(void*)*4, x_1061);
return x_1118;
}
}
else
{
obj* x_1119; obj* x_1120; obj* x_1121; obj* x_1122; obj* x_1123; obj* x_1124; obj* x_1125; obj* x_1126; obj* x_1127; obj* x_1128; obj* x_1129; obj* x_1130; obj* x_1131; obj* x_1132; obj* x_1133; obj* x_1134; obj* x_1135; obj* x_1136; obj* x_1137; obj* x_1138; 
x_1119 = lean::cnstr_get(x_1, 1);
x_1120 = lean::cnstr_get(x_1, 2);
lean::inc(x_1120);
lean::inc(x_1119);
lean::dec(x_1);
x_1121 = lean::cnstr_get(x_235, 0);
lean::inc(x_1121);
x_1122 = lean::cnstr_get(x_235, 1);
lean::inc(x_1122);
x_1123 = lean::cnstr_get(x_235, 2);
lean::inc(x_1123);
x_1124 = lean::cnstr_get(x_235, 3);
lean::inc(x_1124);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_1125 = x_235;
} else {
 lean::dec_ref(x_235);
 x_1125 = lean::box(0);
}
x_1126 = lean::cnstr_get(x_4, 1);
lean::inc(x_1126);
x_1127 = lean::cnstr_get(x_4, 2);
lean::inc(x_1127);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1128 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1128 = lean::box(0);
}
x_1129 = lean::cnstr_get(x_1020, 0);
lean::inc(x_1129);
x_1130 = lean::cnstr_get(x_1020, 1);
lean::inc(x_1130);
x_1131 = lean::cnstr_get(x_1020, 2);
lean::inc(x_1131);
x_1132 = lean::cnstr_get(x_1020, 3);
lean::inc(x_1132);
if (lean::is_exclusive(x_1020)) {
 lean::cnstr_release(x_1020, 0);
 lean::cnstr_release(x_1020, 1);
 lean::cnstr_release(x_1020, 2);
 lean::cnstr_release(x_1020, 3);
 x_1133 = x_1020;
} else {
 lean::dec_ref(x_1020);
 x_1133 = lean::box(0);
}
if (lean::is_scalar(x_1133)) {
 x_1134 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1134 = x_1133;
}
lean::cnstr_set(x_1134, 0, x_1121);
lean::cnstr_set(x_1134, 1, x_1122);
lean::cnstr_set(x_1134, 2, x_1123);
lean::cnstr_set(x_1134, 3, x_1124);
lean::cnstr_set_uint8(x_1134, sizeof(void*)*4, x_806);
if (lean::is_scalar(x_1128)) {
 x_1135 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1135 = x_1128;
}
lean::cnstr_set(x_1135, 0, x_234);
lean::cnstr_set(x_1135, 1, x_1119);
lean::cnstr_set(x_1135, 2, x_1120);
lean::cnstr_set(x_1135, 3, x_1134);
lean::cnstr_set_uint8(x_1135, sizeof(void*)*4, x_1061);
if (lean::is_scalar(x_1125)) {
 x_1136 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1136 = x_1125;
}
lean::cnstr_set(x_1136, 0, x_1135);
lean::cnstr_set(x_1136, 1, x_2);
lean::cnstr_set(x_1136, 2, x_3);
lean::cnstr_set(x_1136, 3, x_679);
lean::cnstr_set_uint8(x_1136, sizeof(void*)*4, x_806);
x_1137 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1137, 0, x_1129);
lean::cnstr_set(x_1137, 1, x_1130);
lean::cnstr_set(x_1137, 2, x_1131);
lean::cnstr_set(x_1137, 3, x_1132);
lean::cnstr_set_uint8(x_1137, sizeof(void*)*4, x_806);
x_1138 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1138, 0, x_1136);
lean::cnstr_set(x_1138, 1, x_1126);
lean::cnstr_set(x_1138, 2, x_1127);
lean::cnstr_set(x_1138, 3, x_1137);
lean::cnstr_set_uint8(x_1138, sizeof(void*)*4, x_1061);
return x_1138;
}
}
else
{
uint8 x_1139; 
x_1139 = !lean::is_exclusive(x_1);
if (x_1139 == 0)
{
obj* x_1140; obj* x_1141; obj* x_1142; obj* x_1143; uint8 x_1144; 
x_1140 = lean::cnstr_get(x_1, 1);
x_1141 = lean::cnstr_get(x_1, 2);
x_1142 = lean::cnstr_get(x_1, 3);
lean::dec(x_1142);
x_1143 = lean::cnstr_get(x_1, 0);
lean::dec(x_1143);
x_1144 = !lean::is_exclusive(x_235);
if (x_1144 == 0)
{
uint8 x_1145; 
x_1145 = !lean::is_exclusive(x_4);
if (x_1145 == 0)
{
obj* x_1146; obj* x_1147; obj* x_1148; obj* x_1149; obj* x_1150; obj* x_1151; obj* x_1152; obj* x_1153; uint8 x_1154; 
x_1146 = lean::cnstr_get(x_235, 0);
x_1147 = lean::cnstr_get(x_235, 1);
x_1148 = lean::cnstr_get(x_235, 2);
x_1149 = lean::cnstr_get(x_235, 3);
x_1150 = lean::cnstr_get(x_4, 1);
x_1151 = lean::cnstr_get(x_4, 2);
x_1152 = lean::cnstr_get(x_4, 3);
lean::dec(x_1152);
x_1153 = lean::cnstr_get(x_4, 0);
lean::dec(x_1153);
x_1154 = !lean::is_exclusive(x_679);
if (x_1154 == 0)
{
obj* x_1155; obj* x_1156; obj* x_1157; obj* x_1158; obj* x_1159; 
x_1155 = lean::cnstr_get(x_679, 0);
x_1156 = lean::cnstr_get(x_679, 1);
x_1157 = lean::cnstr_get(x_679, 2);
x_1158 = lean::cnstr_get(x_679, 3);
lean::cnstr_set(x_679, 3, x_1149);
lean::cnstr_set(x_679, 2, x_1148);
lean::cnstr_set(x_679, 1, x_1147);
lean::cnstr_set(x_679, 0, x_1146);
lean::cnstr_set_uint8(x_679, sizeof(void*)*4, x_1061);
lean::cnstr_set(x_4, 3, x_679);
lean::cnstr_set(x_4, 2, x_1141);
lean::cnstr_set(x_4, 1, x_1140);
lean::cnstr_set(x_4, 0, x_234);
lean::cnstr_set(x_235, 3, x_1158);
lean::cnstr_set(x_235, 2, x_1157);
lean::cnstr_set(x_235, 1, x_1156);
lean::cnstr_set(x_235, 0, x_1155);
lean::cnstr_set_uint8(x_235, sizeof(void*)*4, x_1061);
lean::cnstr_set(x_1, 3, x_1020);
lean::cnstr_set(x_1, 2, x_1151);
lean::cnstr_set(x_1, 1, x_1150);
lean::cnstr_set(x_1, 0, x_235);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_678);
x_1159 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1159, 0, x_4);
lean::cnstr_set(x_1159, 1, x_2);
lean::cnstr_set(x_1159, 2, x_3);
lean::cnstr_set(x_1159, 3, x_1);
lean::cnstr_set_uint8(x_1159, sizeof(void*)*4, x_1061);
return x_1159;
}
else
{
obj* x_1160; obj* x_1161; obj* x_1162; obj* x_1163; obj* x_1164; obj* x_1165; 
x_1160 = lean::cnstr_get(x_679, 0);
x_1161 = lean::cnstr_get(x_679, 1);
x_1162 = lean::cnstr_get(x_679, 2);
x_1163 = lean::cnstr_get(x_679, 3);
lean::inc(x_1163);
lean::inc(x_1162);
lean::inc(x_1161);
lean::inc(x_1160);
lean::dec(x_679);
x_1164 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1164, 0, x_1146);
lean::cnstr_set(x_1164, 1, x_1147);
lean::cnstr_set(x_1164, 2, x_1148);
lean::cnstr_set(x_1164, 3, x_1149);
lean::cnstr_set_uint8(x_1164, sizeof(void*)*4, x_1061);
lean::cnstr_set(x_4, 3, x_1164);
lean::cnstr_set(x_4, 2, x_1141);
lean::cnstr_set(x_4, 1, x_1140);
lean::cnstr_set(x_4, 0, x_234);
lean::cnstr_set(x_235, 3, x_1163);
lean::cnstr_set(x_235, 2, x_1162);
lean::cnstr_set(x_235, 1, x_1161);
lean::cnstr_set(x_235, 0, x_1160);
lean::cnstr_set_uint8(x_235, sizeof(void*)*4, x_1061);
lean::cnstr_set(x_1, 3, x_1020);
lean::cnstr_set(x_1, 2, x_1151);
lean::cnstr_set(x_1, 1, x_1150);
lean::cnstr_set(x_1, 0, x_235);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_678);
x_1165 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1165, 0, x_4);
lean::cnstr_set(x_1165, 1, x_2);
lean::cnstr_set(x_1165, 2, x_3);
lean::cnstr_set(x_1165, 3, x_1);
lean::cnstr_set_uint8(x_1165, sizeof(void*)*4, x_1061);
return x_1165;
}
}
else
{
obj* x_1166; obj* x_1167; obj* x_1168; obj* x_1169; obj* x_1170; obj* x_1171; obj* x_1172; obj* x_1173; obj* x_1174; obj* x_1175; obj* x_1176; obj* x_1177; obj* x_1178; obj* x_1179; 
x_1166 = lean::cnstr_get(x_235, 0);
x_1167 = lean::cnstr_get(x_235, 1);
x_1168 = lean::cnstr_get(x_235, 2);
x_1169 = lean::cnstr_get(x_235, 3);
x_1170 = lean::cnstr_get(x_4, 1);
x_1171 = lean::cnstr_get(x_4, 2);
lean::inc(x_1171);
lean::inc(x_1170);
lean::dec(x_4);
x_1172 = lean::cnstr_get(x_679, 0);
lean::inc(x_1172);
x_1173 = lean::cnstr_get(x_679, 1);
lean::inc(x_1173);
x_1174 = lean::cnstr_get(x_679, 2);
lean::inc(x_1174);
x_1175 = lean::cnstr_get(x_679, 3);
lean::inc(x_1175);
if (lean::is_exclusive(x_679)) {
 lean::cnstr_release(x_679, 0);
 lean::cnstr_release(x_679, 1);
 lean::cnstr_release(x_679, 2);
 lean::cnstr_release(x_679, 3);
 x_1176 = x_679;
} else {
 lean::dec_ref(x_679);
 x_1176 = lean::box(0);
}
if (lean::is_scalar(x_1176)) {
 x_1177 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1177 = x_1176;
}
lean::cnstr_set(x_1177, 0, x_1166);
lean::cnstr_set(x_1177, 1, x_1167);
lean::cnstr_set(x_1177, 2, x_1168);
lean::cnstr_set(x_1177, 3, x_1169);
lean::cnstr_set_uint8(x_1177, sizeof(void*)*4, x_1061);
x_1178 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1178, 0, x_234);
lean::cnstr_set(x_1178, 1, x_1140);
lean::cnstr_set(x_1178, 2, x_1141);
lean::cnstr_set(x_1178, 3, x_1177);
lean::cnstr_set_uint8(x_1178, sizeof(void*)*4, x_678);
lean::cnstr_set(x_235, 3, x_1175);
lean::cnstr_set(x_235, 2, x_1174);
lean::cnstr_set(x_235, 1, x_1173);
lean::cnstr_set(x_235, 0, x_1172);
lean::cnstr_set_uint8(x_235, sizeof(void*)*4, x_1061);
lean::cnstr_set(x_1, 3, x_1020);
lean::cnstr_set(x_1, 2, x_1171);
lean::cnstr_set(x_1, 1, x_1170);
lean::cnstr_set(x_1, 0, x_235);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_678);
x_1179 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1179, 0, x_1178);
lean::cnstr_set(x_1179, 1, x_2);
lean::cnstr_set(x_1179, 2, x_3);
lean::cnstr_set(x_1179, 3, x_1);
lean::cnstr_set_uint8(x_1179, sizeof(void*)*4, x_1061);
return x_1179;
}
}
else
{
obj* x_1180; obj* x_1181; obj* x_1182; obj* x_1183; obj* x_1184; obj* x_1185; obj* x_1186; obj* x_1187; obj* x_1188; obj* x_1189; obj* x_1190; obj* x_1191; obj* x_1192; obj* x_1193; obj* x_1194; obj* x_1195; 
x_1180 = lean::cnstr_get(x_235, 0);
x_1181 = lean::cnstr_get(x_235, 1);
x_1182 = lean::cnstr_get(x_235, 2);
x_1183 = lean::cnstr_get(x_235, 3);
lean::inc(x_1183);
lean::inc(x_1182);
lean::inc(x_1181);
lean::inc(x_1180);
lean::dec(x_235);
x_1184 = lean::cnstr_get(x_4, 1);
lean::inc(x_1184);
x_1185 = lean::cnstr_get(x_4, 2);
lean::inc(x_1185);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1186 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1186 = lean::box(0);
}
x_1187 = lean::cnstr_get(x_679, 0);
lean::inc(x_1187);
x_1188 = lean::cnstr_get(x_679, 1);
lean::inc(x_1188);
x_1189 = lean::cnstr_get(x_679, 2);
lean::inc(x_1189);
x_1190 = lean::cnstr_get(x_679, 3);
lean::inc(x_1190);
if (lean::is_exclusive(x_679)) {
 lean::cnstr_release(x_679, 0);
 lean::cnstr_release(x_679, 1);
 lean::cnstr_release(x_679, 2);
 lean::cnstr_release(x_679, 3);
 x_1191 = x_679;
} else {
 lean::dec_ref(x_679);
 x_1191 = lean::box(0);
}
if (lean::is_scalar(x_1191)) {
 x_1192 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1192 = x_1191;
}
lean::cnstr_set(x_1192, 0, x_1180);
lean::cnstr_set(x_1192, 1, x_1181);
lean::cnstr_set(x_1192, 2, x_1182);
lean::cnstr_set(x_1192, 3, x_1183);
lean::cnstr_set_uint8(x_1192, sizeof(void*)*4, x_1061);
if (lean::is_scalar(x_1186)) {
 x_1193 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1193 = x_1186;
}
lean::cnstr_set(x_1193, 0, x_234);
lean::cnstr_set(x_1193, 1, x_1140);
lean::cnstr_set(x_1193, 2, x_1141);
lean::cnstr_set(x_1193, 3, x_1192);
lean::cnstr_set_uint8(x_1193, sizeof(void*)*4, x_678);
x_1194 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1194, 0, x_1187);
lean::cnstr_set(x_1194, 1, x_1188);
lean::cnstr_set(x_1194, 2, x_1189);
lean::cnstr_set(x_1194, 3, x_1190);
lean::cnstr_set_uint8(x_1194, sizeof(void*)*4, x_1061);
lean::cnstr_set(x_1, 3, x_1020);
lean::cnstr_set(x_1, 2, x_1185);
lean::cnstr_set(x_1, 1, x_1184);
lean::cnstr_set(x_1, 0, x_1194);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_678);
x_1195 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1195, 0, x_1193);
lean::cnstr_set(x_1195, 1, x_2);
lean::cnstr_set(x_1195, 2, x_3);
lean::cnstr_set(x_1195, 3, x_1);
lean::cnstr_set_uint8(x_1195, sizeof(void*)*4, x_1061);
return x_1195;
}
}
else
{
obj* x_1196; obj* x_1197; obj* x_1198; obj* x_1199; obj* x_1200; obj* x_1201; obj* x_1202; obj* x_1203; obj* x_1204; obj* x_1205; obj* x_1206; obj* x_1207; obj* x_1208; obj* x_1209; obj* x_1210; obj* x_1211; obj* x_1212; obj* x_1213; obj* x_1214; obj* x_1215; 
x_1196 = lean::cnstr_get(x_1, 1);
x_1197 = lean::cnstr_get(x_1, 2);
lean::inc(x_1197);
lean::inc(x_1196);
lean::dec(x_1);
x_1198 = lean::cnstr_get(x_235, 0);
lean::inc(x_1198);
x_1199 = lean::cnstr_get(x_235, 1);
lean::inc(x_1199);
x_1200 = lean::cnstr_get(x_235, 2);
lean::inc(x_1200);
x_1201 = lean::cnstr_get(x_235, 3);
lean::inc(x_1201);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_1202 = x_235;
} else {
 lean::dec_ref(x_235);
 x_1202 = lean::box(0);
}
x_1203 = lean::cnstr_get(x_4, 1);
lean::inc(x_1203);
x_1204 = lean::cnstr_get(x_4, 2);
lean::inc(x_1204);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1205 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1205 = lean::box(0);
}
x_1206 = lean::cnstr_get(x_679, 0);
lean::inc(x_1206);
x_1207 = lean::cnstr_get(x_679, 1);
lean::inc(x_1207);
x_1208 = lean::cnstr_get(x_679, 2);
lean::inc(x_1208);
x_1209 = lean::cnstr_get(x_679, 3);
lean::inc(x_1209);
if (lean::is_exclusive(x_679)) {
 lean::cnstr_release(x_679, 0);
 lean::cnstr_release(x_679, 1);
 lean::cnstr_release(x_679, 2);
 lean::cnstr_release(x_679, 3);
 x_1210 = x_679;
} else {
 lean::dec_ref(x_679);
 x_1210 = lean::box(0);
}
if (lean::is_scalar(x_1210)) {
 x_1211 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1211 = x_1210;
}
lean::cnstr_set(x_1211, 0, x_1198);
lean::cnstr_set(x_1211, 1, x_1199);
lean::cnstr_set(x_1211, 2, x_1200);
lean::cnstr_set(x_1211, 3, x_1201);
lean::cnstr_set_uint8(x_1211, sizeof(void*)*4, x_1061);
if (lean::is_scalar(x_1205)) {
 x_1212 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1212 = x_1205;
}
lean::cnstr_set(x_1212, 0, x_234);
lean::cnstr_set(x_1212, 1, x_1196);
lean::cnstr_set(x_1212, 2, x_1197);
lean::cnstr_set(x_1212, 3, x_1211);
lean::cnstr_set_uint8(x_1212, sizeof(void*)*4, x_678);
if (lean::is_scalar(x_1202)) {
 x_1213 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1213 = x_1202;
}
lean::cnstr_set(x_1213, 0, x_1206);
lean::cnstr_set(x_1213, 1, x_1207);
lean::cnstr_set(x_1213, 2, x_1208);
lean::cnstr_set(x_1213, 3, x_1209);
lean::cnstr_set_uint8(x_1213, sizeof(void*)*4, x_1061);
x_1214 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1214, 0, x_1213);
lean::cnstr_set(x_1214, 1, x_1203);
lean::cnstr_set(x_1214, 2, x_1204);
lean::cnstr_set(x_1214, 3, x_1020);
lean::cnstr_set_uint8(x_1214, sizeof(void*)*4, x_678);
x_1215 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1215, 0, x_1212);
lean::cnstr_set(x_1215, 1, x_2);
lean::cnstr_set(x_1215, 2, x_3);
lean::cnstr_set(x_1215, 3, x_1214);
lean::cnstr_set_uint8(x_1215, sizeof(void*)*4, x_1061);
return x_1215;
}
}
}
}
}
}
else
{
uint8 x_1216; 
x_1216 = !lean::is_exclusive(x_1);
if (x_1216 == 0)
{
obj* x_1217; obj* x_1218; uint8 x_1219; 
x_1217 = lean::cnstr_get(x_1, 3);
lean::dec(x_1217);
x_1218 = lean::cnstr_get(x_1, 0);
lean::dec(x_1218);
x_1219 = !lean::is_exclusive(x_235);
if (x_1219 == 0)
{
obj* x_1220; 
lean::cnstr_set_uint8(x_235, sizeof(void*)*4, x_678);
x_1220 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1220, 0, x_1);
lean::cnstr_set(x_1220, 1, x_2);
lean::cnstr_set(x_1220, 2, x_3);
lean::cnstr_set(x_1220, 3, x_4);
lean::cnstr_set_uint8(x_1220, sizeof(void*)*4, x_678);
return x_1220;
}
else
{
obj* x_1221; obj* x_1222; obj* x_1223; obj* x_1224; obj* x_1225; obj* x_1226; 
x_1221 = lean::cnstr_get(x_235, 0);
x_1222 = lean::cnstr_get(x_235, 1);
x_1223 = lean::cnstr_get(x_235, 2);
x_1224 = lean::cnstr_get(x_235, 3);
lean::inc(x_1224);
lean::inc(x_1223);
lean::inc(x_1222);
lean::inc(x_1221);
lean::dec(x_235);
x_1225 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1225, 0, x_1221);
lean::cnstr_set(x_1225, 1, x_1222);
lean::cnstr_set(x_1225, 2, x_1223);
lean::cnstr_set(x_1225, 3, x_1224);
lean::cnstr_set_uint8(x_1225, sizeof(void*)*4, x_678);
lean::cnstr_set(x_1, 3, x_1225);
x_1226 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1226, 0, x_1);
lean::cnstr_set(x_1226, 1, x_2);
lean::cnstr_set(x_1226, 2, x_3);
lean::cnstr_set(x_1226, 3, x_4);
lean::cnstr_set_uint8(x_1226, sizeof(void*)*4, x_678);
return x_1226;
}
}
else
{
obj* x_1227; obj* x_1228; obj* x_1229; obj* x_1230; obj* x_1231; obj* x_1232; obj* x_1233; obj* x_1234; obj* x_1235; obj* x_1236; 
x_1227 = lean::cnstr_get(x_1, 1);
x_1228 = lean::cnstr_get(x_1, 2);
lean::inc(x_1228);
lean::inc(x_1227);
lean::dec(x_1);
x_1229 = lean::cnstr_get(x_235, 0);
lean::inc(x_1229);
x_1230 = lean::cnstr_get(x_235, 1);
lean::inc(x_1230);
x_1231 = lean::cnstr_get(x_235, 2);
lean::inc(x_1231);
x_1232 = lean::cnstr_get(x_235, 3);
lean::inc(x_1232);
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 lean::cnstr_release(x_235, 1);
 lean::cnstr_release(x_235, 2);
 lean::cnstr_release(x_235, 3);
 x_1233 = x_235;
} else {
 lean::dec_ref(x_235);
 x_1233 = lean::box(0);
}
if (lean::is_scalar(x_1233)) {
 x_1234 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1234 = x_1233;
}
lean::cnstr_set(x_1234, 0, x_1229);
lean::cnstr_set(x_1234, 1, x_1230);
lean::cnstr_set(x_1234, 2, x_1231);
lean::cnstr_set(x_1234, 3, x_1232);
lean::cnstr_set_uint8(x_1234, sizeof(void*)*4, x_678);
x_1235 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1235, 0, x_234);
lean::cnstr_set(x_1235, 1, x_1227);
lean::cnstr_set(x_1235, 2, x_1228);
lean::cnstr_set(x_1235, 3, x_1234);
lean::cnstr_set_uint8(x_1235, sizeof(void*)*4, x_233);
x_1236 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1236, 0, x_1235);
lean::cnstr_set(x_1236, 1, x_2);
lean::cnstr_set(x_1236, 2, x_3);
lean::cnstr_set(x_1236, 3, x_4);
lean::cnstr_set_uint8(x_1236, sizeof(void*)*4, x_678);
return x_1236;
}
}
}
}
}
}
else
{
uint8 x_1237; 
x_1237 = lean::cnstr_get_uint8(x_234, sizeof(void*)*4);
if (x_1237 == 0)
{
uint8 x_1238; 
x_1238 = !lean::is_exclusive(x_1);
if (x_1238 == 0)
{
obj* x_1239; obj* x_1240; obj* x_1241; obj* x_1242; uint8 x_1243; 
x_1239 = lean::cnstr_get(x_1, 1);
x_1240 = lean::cnstr_get(x_1, 2);
x_1241 = lean::cnstr_get(x_1, 3);
x_1242 = lean::cnstr_get(x_1, 0);
lean::dec(x_1242);
x_1243 = !lean::is_exclusive(x_234);
if (x_1243 == 0)
{
uint8 x_1244; obj* x_1245; 
x_1244 = 1;
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1244);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_1241);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1244);
x_1245 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1245, 0, x_234);
lean::cnstr_set(x_1245, 1, x_1239);
lean::cnstr_set(x_1245, 2, x_1240);
lean::cnstr_set(x_1245, 3, x_1);
lean::cnstr_set_uint8(x_1245, sizeof(void*)*4, x_1237);
return x_1245;
}
else
{
obj* x_1246; obj* x_1247; obj* x_1248; obj* x_1249; uint8 x_1250; obj* x_1251; obj* x_1252; 
x_1246 = lean::cnstr_get(x_234, 0);
x_1247 = lean::cnstr_get(x_234, 1);
x_1248 = lean::cnstr_get(x_234, 2);
x_1249 = lean::cnstr_get(x_234, 3);
lean::inc(x_1249);
lean::inc(x_1248);
lean::inc(x_1247);
lean::inc(x_1246);
lean::dec(x_234);
x_1250 = 1;
x_1251 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1251, 0, x_1246);
lean::cnstr_set(x_1251, 1, x_1247);
lean::cnstr_set(x_1251, 2, x_1248);
lean::cnstr_set(x_1251, 3, x_1249);
lean::cnstr_set_uint8(x_1251, sizeof(void*)*4, x_1250);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_1241);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1250);
x_1252 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1252, 0, x_1251);
lean::cnstr_set(x_1252, 1, x_1239);
lean::cnstr_set(x_1252, 2, x_1240);
lean::cnstr_set(x_1252, 3, x_1);
lean::cnstr_set_uint8(x_1252, sizeof(void*)*4, x_1237);
return x_1252;
}
}
else
{
obj* x_1253; obj* x_1254; obj* x_1255; obj* x_1256; obj* x_1257; obj* x_1258; obj* x_1259; obj* x_1260; uint8 x_1261; obj* x_1262; obj* x_1263; obj* x_1264; 
x_1253 = lean::cnstr_get(x_1, 1);
x_1254 = lean::cnstr_get(x_1, 2);
x_1255 = lean::cnstr_get(x_1, 3);
lean::inc(x_1255);
lean::inc(x_1254);
lean::inc(x_1253);
lean::dec(x_1);
x_1256 = lean::cnstr_get(x_234, 0);
lean::inc(x_1256);
x_1257 = lean::cnstr_get(x_234, 1);
lean::inc(x_1257);
x_1258 = lean::cnstr_get(x_234, 2);
lean::inc(x_1258);
x_1259 = lean::cnstr_get(x_234, 3);
lean::inc(x_1259);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1260 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1260 = lean::box(0);
}
x_1261 = 1;
if (lean::is_scalar(x_1260)) {
 x_1262 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1262 = x_1260;
}
lean::cnstr_set(x_1262, 0, x_1256);
lean::cnstr_set(x_1262, 1, x_1257);
lean::cnstr_set(x_1262, 2, x_1258);
lean::cnstr_set(x_1262, 3, x_1259);
lean::cnstr_set_uint8(x_1262, sizeof(void*)*4, x_1261);
x_1263 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1263, 0, x_1255);
lean::cnstr_set(x_1263, 1, x_2);
lean::cnstr_set(x_1263, 2, x_3);
lean::cnstr_set(x_1263, 3, x_4);
lean::cnstr_set_uint8(x_1263, sizeof(void*)*4, x_1261);
x_1264 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1264, 0, x_1262);
lean::cnstr_set(x_1264, 1, x_1253);
lean::cnstr_set(x_1264, 2, x_1254);
lean::cnstr_set(x_1264, 3, x_1263);
lean::cnstr_set_uint8(x_1264, sizeof(void*)*4, x_1237);
return x_1264;
}
}
else
{
obj* x_1265; 
x_1265 = lean::cnstr_get(x_1, 3);
lean::inc(x_1265);
if (lean::obj_tag(x_1265) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
uint8 x_1266; 
x_1266 = !lean::is_exclusive(x_1);
if (x_1266 == 0)
{
obj* x_1267; obj* x_1268; obj* x_1269; 
x_1267 = lean::cnstr_get(x_1, 3);
lean::dec(x_1267);
x_1268 = lean::cnstr_get(x_1, 0);
lean::dec(x_1268);
lean::cnstr_set(x_1, 3, x_4);
x_1269 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1269, 0, x_1);
lean::cnstr_set(x_1269, 1, x_2);
lean::cnstr_set(x_1269, 2, x_3);
lean::cnstr_set(x_1269, 3, x_4);
lean::cnstr_set_uint8(x_1269, sizeof(void*)*4, x_1237);
return x_1269;
}
else
{
obj* x_1270; obj* x_1271; obj* x_1272; obj* x_1273; 
x_1270 = lean::cnstr_get(x_1, 1);
x_1271 = lean::cnstr_get(x_1, 2);
lean::inc(x_1271);
lean::inc(x_1270);
lean::dec(x_1);
x_1272 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1272, 0, x_234);
lean::cnstr_set(x_1272, 1, x_1270);
lean::cnstr_set(x_1272, 2, x_1271);
lean::cnstr_set(x_1272, 3, x_4);
lean::cnstr_set_uint8(x_1272, sizeof(void*)*4, x_233);
x_1273 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1273, 0, x_1272);
lean::cnstr_set(x_1273, 1, x_2);
lean::cnstr_set(x_1273, 2, x_3);
lean::cnstr_set(x_1273, 3, x_4);
lean::cnstr_set_uint8(x_1273, sizeof(void*)*4, x_1237);
return x_1273;
}
}
else
{
uint8 x_1274; 
x_1274 = lean::cnstr_get_uint8(x_4, sizeof(void*)*4);
if (x_1274 == 0)
{
obj* x_1275; 
x_1275 = lean::cnstr_get(x_4, 0);
lean::inc(x_1275);
if (lean::obj_tag(x_1275) == 0)
{
obj* x_1276; 
x_1276 = lean::cnstr_get(x_4, 3);
lean::inc(x_1276);
if (lean::obj_tag(x_1276) == 0)
{
uint8 x_1277; 
x_1277 = !lean::is_exclusive(x_1);
if (x_1277 == 0)
{
obj* x_1278; obj* x_1279; obj* x_1280; obj* x_1281; uint8 x_1282; 
x_1278 = lean::cnstr_get(x_1, 1);
x_1279 = lean::cnstr_get(x_1, 2);
x_1280 = lean::cnstr_get(x_1, 3);
lean::dec(x_1280);
x_1281 = lean::cnstr_get(x_1, 0);
lean::dec(x_1281);
x_1282 = !lean::is_exclusive(x_4);
if (x_1282 == 0)
{
obj* x_1283; obj* x_1284; obj* x_1285; obj* x_1286; uint8 x_1287; 
x_1283 = lean::cnstr_get(x_4, 1);
x_1284 = lean::cnstr_get(x_4, 2);
x_1285 = lean::cnstr_get(x_4, 3);
lean::dec(x_1285);
x_1286 = lean::cnstr_get(x_4, 0);
lean::dec(x_1286);
lean::inc(x_234);
lean::cnstr_set(x_4, 2, x_1279);
lean::cnstr_set(x_4, 1, x_1278);
lean::cnstr_set(x_4, 0, x_234);
x_1287 = !lean::is_exclusive(x_234);
if (x_1287 == 0)
{
obj* x_1288; obj* x_1289; obj* x_1290; obj* x_1291; 
x_1288 = lean::cnstr_get(x_234, 3);
lean::dec(x_1288);
x_1289 = lean::cnstr_get(x_234, 2);
lean::dec(x_1289);
x_1290 = lean::cnstr_get(x_234, 1);
lean::dec(x_1290);
x_1291 = lean::cnstr_get(x_234, 0);
lean::dec(x_1291);
lean::cnstr_set(x_234, 3, x_1276);
lean::cnstr_set(x_234, 2, x_1284);
lean::cnstr_set(x_234, 1, x_1283);
lean::cnstr_set(x_234, 0, x_1276);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1274);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1237);
return x_1;
}
else
{
obj* x_1292; 
lean::dec(x_234);
x_1292 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1292, 0, x_1276);
lean::cnstr_set(x_1292, 1, x_1283);
lean::cnstr_set(x_1292, 2, x_1284);
lean::cnstr_set(x_1292, 3, x_1276);
lean::cnstr_set_uint8(x_1292, sizeof(void*)*4, x_1274);
lean::cnstr_set(x_1, 3, x_1292);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1237);
return x_1;
}
}
else
{
obj* x_1293; obj* x_1294; obj* x_1295; obj* x_1296; obj* x_1297; 
x_1293 = lean::cnstr_get(x_4, 1);
x_1294 = lean::cnstr_get(x_4, 2);
lean::inc(x_1294);
lean::inc(x_1293);
lean::dec(x_4);
lean::inc(x_234);
x_1295 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1295, 0, x_234);
lean::cnstr_set(x_1295, 1, x_1278);
lean::cnstr_set(x_1295, 2, x_1279);
lean::cnstr_set(x_1295, 3, x_1276);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1296 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1296 = lean::box(0);
}
lean::cnstr_set_uint8(x_1295, sizeof(void*)*4, x_1274);
if (lean::is_scalar(x_1296)) {
 x_1297 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1297 = x_1296;
}
lean::cnstr_set(x_1297, 0, x_1276);
lean::cnstr_set(x_1297, 1, x_1293);
lean::cnstr_set(x_1297, 2, x_1294);
lean::cnstr_set(x_1297, 3, x_1276);
lean::cnstr_set_uint8(x_1297, sizeof(void*)*4, x_1274);
lean::cnstr_set(x_1, 3, x_1297);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_1295);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1237);
return x_1;
}
}
else
{
obj* x_1298; obj* x_1299; obj* x_1300; obj* x_1301; obj* x_1302; obj* x_1303; obj* x_1304; obj* x_1305; obj* x_1306; 
x_1298 = lean::cnstr_get(x_1, 1);
x_1299 = lean::cnstr_get(x_1, 2);
lean::inc(x_1299);
lean::inc(x_1298);
lean::dec(x_1);
x_1300 = lean::cnstr_get(x_4, 1);
lean::inc(x_1300);
x_1301 = lean::cnstr_get(x_4, 2);
lean::inc(x_1301);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1302 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1302 = lean::box(0);
}
lean::inc(x_234);
if (lean::is_scalar(x_1302)) {
 x_1303 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1303 = x_1302;
}
lean::cnstr_set(x_1303, 0, x_234);
lean::cnstr_set(x_1303, 1, x_1298);
lean::cnstr_set(x_1303, 2, x_1299);
lean::cnstr_set(x_1303, 3, x_1276);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1304 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1304 = lean::box(0);
}
lean::cnstr_set_uint8(x_1303, sizeof(void*)*4, x_1274);
if (lean::is_scalar(x_1304)) {
 x_1305 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1305 = x_1304;
}
lean::cnstr_set(x_1305, 0, x_1276);
lean::cnstr_set(x_1305, 1, x_1300);
lean::cnstr_set(x_1305, 2, x_1301);
lean::cnstr_set(x_1305, 3, x_1276);
lean::cnstr_set_uint8(x_1305, sizeof(void*)*4, x_1274);
x_1306 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1306, 0, x_1303);
lean::cnstr_set(x_1306, 1, x_2);
lean::cnstr_set(x_1306, 2, x_3);
lean::cnstr_set(x_1306, 3, x_1305);
lean::cnstr_set_uint8(x_1306, sizeof(void*)*4, x_1237);
return x_1306;
}
}
else
{
uint8 x_1307; 
x_1307 = lean::cnstr_get_uint8(x_1276, sizeof(void*)*4);
if (x_1307 == 0)
{
uint8 x_1308; 
x_1308 = !lean::is_exclusive(x_1);
if (x_1308 == 0)
{
obj* x_1309; obj* x_1310; obj* x_1311; obj* x_1312; uint8 x_1313; 
x_1309 = lean::cnstr_get(x_1, 1);
x_1310 = lean::cnstr_get(x_1, 2);
x_1311 = lean::cnstr_get(x_1, 3);
lean::dec(x_1311);
x_1312 = lean::cnstr_get(x_1, 0);
lean::dec(x_1312);
x_1313 = !lean::is_exclusive(x_4);
if (x_1313 == 0)
{
obj* x_1314; obj* x_1315; obj* x_1316; obj* x_1317; uint8 x_1318; 
x_1314 = lean::cnstr_get(x_4, 1);
x_1315 = lean::cnstr_get(x_4, 2);
x_1316 = lean::cnstr_get(x_4, 3);
lean::dec(x_1316);
x_1317 = lean::cnstr_get(x_4, 0);
lean::dec(x_1317);
x_1318 = !lean::is_exclusive(x_1276);
if (x_1318 == 0)
{
obj* x_1319; obj* x_1320; obj* x_1321; obj* x_1322; uint8 x_1323; 
x_1319 = lean::cnstr_get(x_1276, 0);
x_1320 = lean::cnstr_get(x_1276, 1);
x_1321 = lean::cnstr_get(x_1276, 2);
x_1322 = lean::cnstr_get(x_1276, 3);
lean::inc(x_234);
lean::cnstr_set(x_1276, 3, x_1275);
lean::cnstr_set(x_1276, 2, x_1310);
lean::cnstr_set(x_1276, 1, x_1309);
lean::cnstr_set(x_1276, 0, x_234);
x_1323 = !lean::is_exclusive(x_234);
if (x_1323 == 0)
{
obj* x_1324; obj* x_1325; obj* x_1326; obj* x_1327; 
x_1324 = lean::cnstr_get(x_234, 3);
lean::dec(x_1324);
x_1325 = lean::cnstr_get(x_234, 2);
lean::dec(x_1325);
x_1326 = lean::cnstr_get(x_234, 1);
lean::dec(x_1326);
x_1327 = lean::cnstr_get(x_234, 0);
lean::dec(x_1327);
lean::cnstr_set(x_4, 3, x_1275);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_1276);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_234, 3, x_1322);
lean::cnstr_set(x_234, 2, x_1321);
lean::cnstr_set(x_234, 1, x_1320);
lean::cnstr_set(x_234, 0, x_1319);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_1315);
lean::cnstr_set(x_1, 1, x_1314);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1307);
return x_1;
}
else
{
obj* x_1328; 
lean::dec(x_234);
lean::cnstr_set(x_4, 3, x_1275);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_1276);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1237);
x_1328 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1328, 0, x_1319);
lean::cnstr_set(x_1328, 1, x_1320);
lean::cnstr_set(x_1328, 2, x_1321);
lean::cnstr_set(x_1328, 3, x_1322);
lean::cnstr_set_uint8(x_1328, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_1, 3, x_1328);
lean::cnstr_set(x_1, 2, x_1315);
lean::cnstr_set(x_1, 1, x_1314);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1307);
return x_1;
}
}
else
{
obj* x_1329; obj* x_1330; obj* x_1331; obj* x_1332; obj* x_1333; obj* x_1334; obj* x_1335; 
x_1329 = lean::cnstr_get(x_1276, 0);
x_1330 = lean::cnstr_get(x_1276, 1);
x_1331 = lean::cnstr_get(x_1276, 2);
x_1332 = lean::cnstr_get(x_1276, 3);
lean::inc(x_1332);
lean::inc(x_1331);
lean::inc(x_1330);
lean::inc(x_1329);
lean::dec(x_1276);
lean::inc(x_234);
x_1333 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1333, 0, x_234);
lean::cnstr_set(x_1333, 1, x_1309);
lean::cnstr_set(x_1333, 2, x_1310);
lean::cnstr_set(x_1333, 3, x_1275);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1334 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1334 = lean::box(0);
}
lean::cnstr_set_uint8(x_1333, sizeof(void*)*4, x_1307);
lean::cnstr_set(x_4, 3, x_1275);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_1333);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1237);
if (lean::is_scalar(x_1334)) {
 x_1335 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1335 = x_1334;
}
lean::cnstr_set(x_1335, 0, x_1329);
lean::cnstr_set(x_1335, 1, x_1330);
lean::cnstr_set(x_1335, 2, x_1331);
lean::cnstr_set(x_1335, 3, x_1332);
lean::cnstr_set_uint8(x_1335, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_1, 3, x_1335);
lean::cnstr_set(x_1, 2, x_1315);
lean::cnstr_set(x_1, 1, x_1314);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1307);
return x_1;
}
}
else
{
obj* x_1336; obj* x_1337; obj* x_1338; obj* x_1339; obj* x_1340; obj* x_1341; obj* x_1342; obj* x_1343; obj* x_1344; obj* x_1345; obj* x_1346; 
x_1336 = lean::cnstr_get(x_4, 1);
x_1337 = lean::cnstr_get(x_4, 2);
lean::inc(x_1337);
lean::inc(x_1336);
lean::dec(x_4);
x_1338 = lean::cnstr_get(x_1276, 0);
lean::inc(x_1338);
x_1339 = lean::cnstr_get(x_1276, 1);
lean::inc(x_1339);
x_1340 = lean::cnstr_get(x_1276, 2);
lean::inc(x_1340);
x_1341 = lean::cnstr_get(x_1276, 3);
lean::inc(x_1341);
if (lean::is_exclusive(x_1276)) {
 lean::cnstr_release(x_1276, 0);
 lean::cnstr_release(x_1276, 1);
 lean::cnstr_release(x_1276, 2);
 lean::cnstr_release(x_1276, 3);
 x_1342 = x_1276;
} else {
 lean::dec_ref(x_1276);
 x_1342 = lean::box(0);
}
lean::inc(x_234);
if (lean::is_scalar(x_1342)) {
 x_1343 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1343 = x_1342;
}
lean::cnstr_set(x_1343, 0, x_234);
lean::cnstr_set(x_1343, 1, x_1309);
lean::cnstr_set(x_1343, 2, x_1310);
lean::cnstr_set(x_1343, 3, x_1275);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1344 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1344 = lean::box(0);
}
lean::cnstr_set_uint8(x_1343, sizeof(void*)*4, x_1307);
x_1345 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1345, 0, x_1343);
lean::cnstr_set(x_1345, 1, x_2);
lean::cnstr_set(x_1345, 2, x_3);
lean::cnstr_set(x_1345, 3, x_1275);
lean::cnstr_set_uint8(x_1345, sizeof(void*)*4, x_1237);
if (lean::is_scalar(x_1344)) {
 x_1346 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1346 = x_1344;
}
lean::cnstr_set(x_1346, 0, x_1338);
lean::cnstr_set(x_1346, 1, x_1339);
lean::cnstr_set(x_1346, 2, x_1340);
lean::cnstr_set(x_1346, 3, x_1341);
lean::cnstr_set_uint8(x_1346, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_1, 3, x_1346);
lean::cnstr_set(x_1, 2, x_1337);
lean::cnstr_set(x_1, 1, x_1336);
lean::cnstr_set(x_1, 0, x_1345);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1307);
return x_1;
}
}
else
{
obj* x_1347; obj* x_1348; obj* x_1349; obj* x_1350; obj* x_1351; obj* x_1352; obj* x_1353; obj* x_1354; obj* x_1355; obj* x_1356; obj* x_1357; obj* x_1358; obj* x_1359; obj* x_1360; obj* x_1361; 
x_1347 = lean::cnstr_get(x_1, 1);
x_1348 = lean::cnstr_get(x_1, 2);
lean::inc(x_1348);
lean::inc(x_1347);
lean::dec(x_1);
x_1349 = lean::cnstr_get(x_4, 1);
lean::inc(x_1349);
x_1350 = lean::cnstr_get(x_4, 2);
lean::inc(x_1350);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1351 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1351 = lean::box(0);
}
x_1352 = lean::cnstr_get(x_1276, 0);
lean::inc(x_1352);
x_1353 = lean::cnstr_get(x_1276, 1);
lean::inc(x_1353);
x_1354 = lean::cnstr_get(x_1276, 2);
lean::inc(x_1354);
x_1355 = lean::cnstr_get(x_1276, 3);
lean::inc(x_1355);
if (lean::is_exclusive(x_1276)) {
 lean::cnstr_release(x_1276, 0);
 lean::cnstr_release(x_1276, 1);
 lean::cnstr_release(x_1276, 2);
 lean::cnstr_release(x_1276, 3);
 x_1356 = x_1276;
} else {
 lean::dec_ref(x_1276);
 x_1356 = lean::box(0);
}
lean::inc(x_234);
if (lean::is_scalar(x_1356)) {
 x_1357 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1357 = x_1356;
}
lean::cnstr_set(x_1357, 0, x_234);
lean::cnstr_set(x_1357, 1, x_1347);
lean::cnstr_set(x_1357, 2, x_1348);
lean::cnstr_set(x_1357, 3, x_1275);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1358 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1358 = lean::box(0);
}
lean::cnstr_set_uint8(x_1357, sizeof(void*)*4, x_1307);
if (lean::is_scalar(x_1351)) {
 x_1359 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1359 = x_1351;
}
lean::cnstr_set(x_1359, 0, x_1357);
lean::cnstr_set(x_1359, 1, x_2);
lean::cnstr_set(x_1359, 2, x_3);
lean::cnstr_set(x_1359, 3, x_1275);
lean::cnstr_set_uint8(x_1359, sizeof(void*)*4, x_1237);
if (lean::is_scalar(x_1358)) {
 x_1360 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1360 = x_1358;
}
lean::cnstr_set(x_1360, 0, x_1352);
lean::cnstr_set(x_1360, 1, x_1353);
lean::cnstr_set(x_1360, 2, x_1354);
lean::cnstr_set(x_1360, 3, x_1355);
lean::cnstr_set_uint8(x_1360, sizeof(void*)*4, x_1237);
x_1361 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1361, 0, x_1359);
lean::cnstr_set(x_1361, 1, x_1349);
lean::cnstr_set(x_1361, 2, x_1350);
lean::cnstr_set(x_1361, 3, x_1360);
lean::cnstr_set_uint8(x_1361, sizeof(void*)*4, x_1307);
return x_1361;
}
}
else
{
uint8 x_1362; 
x_1362 = !lean::is_exclusive(x_1276);
if (x_1362 == 0)
{
obj* x_1363; obj* x_1364; obj* x_1365; obj* x_1366; uint8 x_1367; 
x_1363 = lean::cnstr_get(x_1276, 3);
lean::dec(x_1363);
x_1364 = lean::cnstr_get(x_1276, 2);
lean::dec(x_1364);
x_1365 = lean::cnstr_get(x_1276, 1);
lean::dec(x_1365);
x_1366 = lean::cnstr_get(x_1276, 0);
lean::dec(x_1366);
x_1367 = !lean::is_exclusive(x_1);
if (x_1367 == 0)
{
obj* x_1368; obj* x_1369; obj* x_1370; obj* x_1371; uint8 x_1372; 
x_1368 = lean::cnstr_get(x_1, 1);
x_1369 = lean::cnstr_get(x_1, 2);
x_1370 = lean::cnstr_get(x_1, 3);
lean::dec(x_1370);
x_1371 = lean::cnstr_get(x_1, 0);
lean::dec(x_1371);
x_1372 = !lean::is_exclusive(x_234);
if (x_1372 == 0)
{
obj* x_1373; obj* x_1374; obj* x_1375; obj* x_1376; 
x_1373 = lean::cnstr_get(x_234, 0);
x_1374 = lean::cnstr_get(x_234, 1);
x_1375 = lean::cnstr_get(x_234, 2);
x_1376 = lean::cnstr_get(x_234, 3);
lean::cnstr_set(x_1276, 3, x_1376);
lean::cnstr_set(x_1276, 2, x_1375);
lean::cnstr_set(x_1276, 1, x_1374);
lean::cnstr_set(x_1276, 0, x_1373);
lean::cnstr_set(x_234, 3, x_1275);
lean::cnstr_set(x_234, 2, x_1369);
lean::cnstr_set(x_234, 1, x_1368);
lean::cnstr_set(x_234, 0, x_1276);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1274);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1307);
return x_1;
}
else
{
obj* x_1377; obj* x_1378; obj* x_1379; obj* x_1380; obj* x_1381; 
x_1377 = lean::cnstr_get(x_234, 0);
x_1378 = lean::cnstr_get(x_234, 1);
x_1379 = lean::cnstr_get(x_234, 2);
x_1380 = lean::cnstr_get(x_234, 3);
lean::inc(x_1380);
lean::inc(x_1379);
lean::inc(x_1378);
lean::inc(x_1377);
lean::dec(x_234);
lean::cnstr_set(x_1276, 3, x_1380);
lean::cnstr_set(x_1276, 2, x_1379);
lean::cnstr_set(x_1276, 1, x_1378);
lean::cnstr_set(x_1276, 0, x_1377);
x_1381 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1381, 0, x_1276);
lean::cnstr_set(x_1381, 1, x_1368);
lean::cnstr_set(x_1381, 2, x_1369);
lean::cnstr_set(x_1381, 3, x_1275);
lean::cnstr_set_uint8(x_1381, sizeof(void*)*4, x_1274);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_1381);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1307);
return x_1;
}
}
else
{
obj* x_1382; obj* x_1383; obj* x_1384; obj* x_1385; obj* x_1386; obj* x_1387; obj* x_1388; obj* x_1389; obj* x_1390; 
x_1382 = lean::cnstr_get(x_1, 1);
x_1383 = lean::cnstr_get(x_1, 2);
lean::inc(x_1383);
lean::inc(x_1382);
lean::dec(x_1);
x_1384 = lean::cnstr_get(x_234, 0);
lean::inc(x_1384);
x_1385 = lean::cnstr_get(x_234, 1);
lean::inc(x_1385);
x_1386 = lean::cnstr_get(x_234, 2);
lean::inc(x_1386);
x_1387 = lean::cnstr_get(x_234, 3);
lean::inc(x_1387);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1388 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1388 = lean::box(0);
}
lean::cnstr_set(x_1276, 3, x_1387);
lean::cnstr_set(x_1276, 2, x_1386);
lean::cnstr_set(x_1276, 1, x_1385);
lean::cnstr_set(x_1276, 0, x_1384);
if (lean::is_scalar(x_1388)) {
 x_1389 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1389 = x_1388;
}
lean::cnstr_set(x_1389, 0, x_1276);
lean::cnstr_set(x_1389, 1, x_1382);
lean::cnstr_set(x_1389, 2, x_1383);
lean::cnstr_set(x_1389, 3, x_1275);
lean::cnstr_set_uint8(x_1389, sizeof(void*)*4, x_1274);
x_1390 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1390, 0, x_1389);
lean::cnstr_set(x_1390, 1, x_2);
lean::cnstr_set(x_1390, 2, x_3);
lean::cnstr_set(x_1390, 3, x_4);
lean::cnstr_set_uint8(x_1390, sizeof(void*)*4, x_1307);
return x_1390;
}
}
else
{
obj* x_1391; obj* x_1392; obj* x_1393; obj* x_1394; obj* x_1395; obj* x_1396; obj* x_1397; obj* x_1398; obj* x_1399; obj* x_1400; obj* x_1401; 
lean::dec(x_1276);
x_1391 = lean::cnstr_get(x_1, 1);
lean::inc(x_1391);
x_1392 = lean::cnstr_get(x_1, 2);
lean::inc(x_1392);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_1393 = x_1;
} else {
 lean::dec_ref(x_1);
 x_1393 = lean::box(0);
}
x_1394 = lean::cnstr_get(x_234, 0);
lean::inc(x_1394);
x_1395 = lean::cnstr_get(x_234, 1);
lean::inc(x_1395);
x_1396 = lean::cnstr_get(x_234, 2);
lean::inc(x_1396);
x_1397 = lean::cnstr_get(x_234, 3);
lean::inc(x_1397);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1398 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1398 = lean::box(0);
}
x_1399 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1399, 0, x_1394);
lean::cnstr_set(x_1399, 1, x_1395);
lean::cnstr_set(x_1399, 2, x_1396);
lean::cnstr_set(x_1399, 3, x_1397);
lean::cnstr_set_uint8(x_1399, sizeof(void*)*4, x_1307);
if (lean::is_scalar(x_1398)) {
 x_1400 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1400 = x_1398;
}
lean::cnstr_set(x_1400, 0, x_1399);
lean::cnstr_set(x_1400, 1, x_1391);
lean::cnstr_set(x_1400, 2, x_1392);
lean::cnstr_set(x_1400, 3, x_1275);
lean::cnstr_set_uint8(x_1400, sizeof(void*)*4, x_1274);
if (lean::is_scalar(x_1393)) {
 x_1401 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1401 = x_1393;
}
lean::cnstr_set(x_1401, 0, x_1400);
lean::cnstr_set(x_1401, 1, x_2);
lean::cnstr_set(x_1401, 2, x_3);
lean::cnstr_set(x_1401, 3, x_4);
lean::cnstr_set_uint8(x_1401, sizeof(void*)*4, x_1307);
return x_1401;
}
}
}
}
else
{
uint8 x_1402; 
x_1402 = lean::cnstr_get_uint8(x_1275, sizeof(void*)*4);
if (x_1402 == 0)
{
obj* x_1403; 
x_1403 = lean::cnstr_get(x_4, 3);
lean::inc(x_1403);
if (lean::obj_tag(x_1403) == 0)
{
uint8 x_1404; 
x_1404 = !lean::is_exclusive(x_1);
if (x_1404 == 0)
{
obj* x_1405; obj* x_1406; obj* x_1407; obj* x_1408; uint8 x_1409; 
x_1405 = lean::cnstr_get(x_1, 1);
x_1406 = lean::cnstr_get(x_1, 2);
x_1407 = lean::cnstr_get(x_1, 3);
lean::dec(x_1407);
x_1408 = lean::cnstr_get(x_1, 0);
lean::dec(x_1408);
x_1409 = !lean::is_exclusive(x_4);
if (x_1409 == 0)
{
obj* x_1410; obj* x_1411; obj* x_1412; obj* x_1413; uint8 x_1414; 
x_1410 = lean::cnstr_get(x_4, 1);
x_1411 = lean::cnstr_get(x_4, 2);
x_1412 = lean::cnstr_get(x_4, 3);
lean::dec(x_1412);
x_1413 = lean::cnstr_get(x_4, 0);
lean::dec(x_1413);
x_1414 = !lean::is_exclusive(x_1275);
if (x_1414 == 0)
{
obj* x_1415; obj* x_1416; obj* x_1417; obj* x_1418; uint8 x_1419; 
x_1415 = lean::cnstr_get(x_1275, 0);
x_1416 = lean::cnstr_get(x_1275, 1);
x_1417 = lean::cnstr_get(x_1275, 2);
x_1418 = lean::cnstr_get(x_1275, 3);
lean::inc(x_234);
lean::cnstr_set(x_1275, 3, x_1403);
lean::cnstr_set(x_1275, 2, x_1406);
lean::cnstr_set(x_1275, 1, x_1405);
lean::cnstr_set(x_1275, 0, x_234);
x_1419 = !lean::is_exclusive(x_234);
if (x_1419 == 0)
{
obj* x_1420; obj* x_1421; obj* x_1422; obj* x_1423; 
x_1420 = lean::cnstr_get(x_234, 3);
lean::dec(x_1420);
x_1421 = lean::cnstr_get(x_234, 2);
lean::dec(x_1421);
x_1422 = lean::cnstr_get(x_234, 1);
lean::dec(x_1422);
x_1423 = lean::cnstr_get(x_234, 0);
lean::dec(x_1423);
lean::cnstr_set(x_4, 3, x_1415);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_234, 3, x_1403);
lean::cnstr_set(x_234, 2, x_1411);
lean::cnstr_set(x_234, 1, x_1410);
lean::cnstr_set(x_234, 0, x_1418);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_1417);
lean::cnstr_set(x_1, 1, x_1416);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1402);
return x_1;
}
else
{
obj* x_1424; 
lean::dec(x_234);
lean::cnstr_set(x_4, 3, x_1415);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1237);
x_1424 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1424, 0, x_1418);
lean::cnstr_set(x_1424, 1, x_1410);
lean::cnstr_set(x_1424, 2, x_1411);
lean::cnstr_set(x_1424, 3, x_1403);
lean::cnstr_set_uint8(x_1424, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_1, 3, x_1424);
lean::cnstr_set(x_1, 2, x_1417);
lean::cnstr_set(x_1, 1, x_1416);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1402);
return x_1;
}
}
else
{
obj* x_1425; obj* x_1426; obj* x_1427; obj* x_1428; obj* x_1429; obj* x_1430; obj* x_1431; 
x_1425 = lean::cnstr_get(x_1275, 0);
x_1426 = lean::cnstr_get(x_1275, 1);
x_1427 = lean::cnstr_get(x_1275, 2);
x_1428 = lean::cnstr_get(x_1275, 3);
lean::inc(x_1428);
lean::inc(x_1427);
lean::inc(x_1426);
lean::inc(x_1425);
lean::dec(x_1275);
lean::inc(x_234);
x_1429 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1429, 0, x_234);
lean::cnstr_set(x_1429, 1, x_1405);
lean::cnstr_set(x_1429, 2, x_1406);
lean::cnstr_set(x_1429, 3, x_1403);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1430 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1430 = lean::box(0);
}
lean::cnstr_set_uint8(x_1429, sizeof(void*)*4, x_1402);
lean::cnstr_set(x_4, 3, x_1425);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_1429);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1237);
if (lean::is_scalar(x_1430)) {
 x_1431 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1431 = x_1430;
}
lean::cnstr_set(x_1431, 0, x_1428);
lean::cnstr_set(x_1431, 1, x_1410);
lean::cnstr_set(x_1431, 2, x_1411);
lean::cnstr_set(x_1431, 3, x_1403);
lean::cnstr_set_uint8(x_1431, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_1, 3, x_1431);
lean::cnstr_set(x_1, 2, x_1427);
lean::cnstr_set(x_1, 1, x_1426);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1402);
return x_1;
}
}
else
{
obj* x_1432; obj* x_1433; obj* x_1434; obj* x_1435; obj* x_1436; obj* x_1437; obj* x_1438; obj* x_1439; obj* x_1440; obj* x_1441; obj* x_1442; 
x_1432 = lean::cnstr_get(x_4, 1);
x_1433 = lean::cnstr_get(x_4, 2);
lean::inc(x_1433);
lean::inc(x_1432);
lean::dec(x_4);
x_1434 = lean::cnstr_get(x_1275, 0);
lean::inc(x_1434);
x_1435 = lean::cnstr_get(x_1275, 1);
lean::inc(x_1435);
x_1436 = lean::cnstr_get(x_1275, 2);
lean::inc(x_1436);
x_1437 = lean::cnstr_get(x_1275, 3);
lean::inc(x_1437);
if (lean::is_exclusive(x_1275)) {
 lean::cnstr_release(x_1275, 0);
 lean::cnstr_release(x_1275, 1);
 lean::cnstr_release(x_1275, 2);
 lean::cnstr_release(x_1275, 3);
 x_1438 = x_1275;
} else {
 lean::dec_ref(x_1275);
 x_1438 = lean::box(0);
}
lean::inc(x_234);
if (lean::is_scalar(x_1438)) {
 x_1439 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1439 = x_1438;
}
lean::cnstr_set(x_1439, 0, x_234);
lean::cnstr_set(x_1439, 1, x_1405);
lean::cnstr_set(x_1439, 2, x_1406);
lean::cnstr_set(x_1439, 3, x_1403);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1440 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1440 = lean::box(0);
}
lean::cnstr_set_uint8(x_1439, sizeof(void*)*4, x_1402);
x_1441 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1441, 0, x_1439);
lean::cnstr_set(x_1441, 1, x_2);
lean::cnstr_set(x_1441, 2, x_3);
lean::cnstr_set(x_1441, 3, x_1434);
lean::cnstr_set_uint8(x_1441, sizeof(void*)*4, x_1237);
if (lean::is_scalar(x_1440)) {
 x_1442 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1442 = x_1440;
}
lean::cnstr_set(x_1442, 0, x_1437);
lean::cnstr_set(x_1442, 1, x_1432);
lean::cnstr_set(x_1442, 2, x_1433);
lean::cnstr_set(x_1442, 3, x_1403);
lean::cnstr_set_uint8(x_1442, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_1, 3, x_1442);
lean::cnstr_set(x_1, 2, x_1436);
lean::cnstr_set(x_1, 1, x_1435);
lean::cnstr_set(x_1, 0, x_1441);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1402);
return x_1;
}
}
else
{
obj* x_1443; obj* x_1444; obj* x_1445; obj* x_1446; obj* x_1447; obj* x_1448; obj* x_1449; obj* x_1450; obj* x_1451; obj* x_1452; obj* x_1453; obj* x_1454; obj* x_1455; obj* x_1456; obj* x_1457; 
x_1443 = lean::cnstr_get(x_1, 1);
x_1444 = lean::cnstr_get(x_1, 2);
lean::inc(x_1444);
lean::inc(x_1443);
lean::dec(x_1);
x_1445 = lean::cnstr_get(x_4, 1);
lean::inc(x_1445);
x_1446 = lean::cnstr_get(x_4, 2);
lean::inc(x_1446);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1447 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1447 = lean::box(0);
}
x_1448 = lean::cnstr_get(x_1275, 0);
lean::inc(x_1448);
x_1449 = lean::cnstr_get(x_1275, 1);
lean::inc(x_1449);
x_1450 = lean::cnstr_get(x_1275, 2);
lean::inc(x_1450);
x_1451 = lean::cnstr_get(x_1275, 3);
lean::inc(x_1451);
if (lean::is_exclusive(x_1275)) {
 lean::cnstr_release(x_1275, 0);
 lean::cnstr_release(x_1275, 1);
 lean::cnstr_release(x_1275, 2);
 lean::cnstr_release(x_1275, 3);
 x_1452 = x_1275;
} else {
 lean::dec_ref(x_1275);
 x_1452 = lean::box(0);
}
lean::inc(x_234);
if (lean::is_scalar(x_1452)) {
 x_1453 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1453 = x_1452;
}
lean::cnstr_set(x_1453, 0, x_234);
lean::cnstr_set(x_1453, 1, x_1443);
lean::cnstr_set(x_1453, 2, x_1444);
lean::cnstr_set(x_1453, 3, x_1403);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1454 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1454 = lean::box(0);
}
lean::cnstr_set_uint8(x_1453, sizeof(void*)*4, x_1402);
if (lean::is_scalar(x_1447)) {
 x_1455 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1455 = x_1447;
}
lean::cnstr_set(x_1455, 0, x_1453);
lean::cnstr_set(x_1455, 1, x_2);
lean::cnstr_set(x_1455, 2, x_3);
lean::cnstr_set(x_1455, 3, x_1448);
lean::cnstr_set_uint8(x_1455, sizeof(void*)*4, x_1237);
if (lean::is_scalar(x_1454)) {
 x_1456 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1456 = x_1454;
}
lean::cnstr_set(x_1456, 0, x_1451);
lean::cnstr_set(x_1456, 1, x_1445);
lean::cnstr_set(x_1456, 2, x_1446);
lean::cnstr_set(x_1456, 3, x_1403);
lean::cnstr_set_uint8(x_1456, sizeof(void*)*4, x_1237);
x_1457 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1457, 0, x_1455);
lean::cnstr_set(x_1457, 1, x_1449);
lean::cnstr_set(x_1457, 2, x_1450);
lean::cnstr_set(x_1457, 3, x_1456);
lean::cnstr_set_uint8(x_1457, sizeof(void*)*4, x_1402);
return x_1457;
}
}
else
{
uint8 x_1458; 
x_1458 = lean::cnstr_get_uint8(x_1403, sizeof(void*)*4);
if (x_1458 == 0)
{
uint8 x_1459; 
x_1459 = !lean::is_exclusive(x_1);
if (x_1459 == 0)
{
obj* x_1460; obj* x_1461; obj* x_1462; obj* x_1463; uint8 x_1464; 
x_1460 = lean::cnstr_get(x_1, 1);
x_1461 = lean::cnstr_get(x_1, 2);
x_1462 = lean::cnstr_get(x_1, 3);
lean::dec(x_1462);
x_1463 = lean::cnstr_get(x_1, 0);
lean::dec(x_1463);
x_1464 = !lean::is_exclusive(x_4);
if (x_1464 == 0)
{
obj* x_1465; obj* x_1466; obj* x_1467; obj* x_1468; uint8 x_1469; 
x_1465 = lean::cnstr_get(x_4, 1);
x_1466 = lean::cnstr_get(x_4, 2);
x_1467 = lean::cnstr_get(x_4, 3);
lean::dec(x_1467);
x_1468 = lean::cnstr_get(x_4, 0);
lean::dec(x_1468);
x_1469 = !lean::is_exclusive(x_1275);
if (x_1469 == 0)
{
uint8 x_1470; 
x_1470 = !lean::is_exclusive(x_1403);
if (x_1470 == 0)
{
obj* x_1471; obj* x_1472; obj* x_1473; obj* x_1474; uint8 x_1475; 
x_1471 = lean::cnstr_get(x_1403, 0);
x_1472 = lean::cnstr_get(x_1403, 1);
x_1473 = lean::cnstr_get(x_1403, 2);
x_1474 = lean::cnstr_get(x_1403, 3);
lean::inc(x_234);
lean::cnstr_set(x_1403, 3, x_1265);
lean::cnstr_set(x_1403, 2, x_1461);
lean::cnstr_set(x_1403, 1, x_1460);
lean::cnstr_set(x_1403, 0, x_234);
x_1475 = !lean::is_exclusive(x_234);
if (x_1475 == 0)
{
obj* x_1476; obj* x_1477; obj* x_1478; obj* x_1479; 
x_1476 = lean::cnstr_get(x_234, 3);
lean::dec(x_1476);
x_1477 = lean::cnstr_get(x_234, 2);
lean::dec(x_1477);
x_1478 = lean::cnstr_get(x_234, 1);
lean::dec(x_1478);
x_1479 = lean::cnstr_get(x_234, 0);
lean::dec(x_1479);
lean::cnstr_set_uint8(x_1275, sizeof(void*)*4, x_1458);
lean::cnstr_set(x_4, 3, x_1275);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_1403);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_234, 3, x_1474);
lean::cnstr_set(x_234, 2, x_1473);
lean::cnstr_set(x_234, 1, x_1472);
lean::cnstr_set(x_234, 0, x_1471);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_1466);
lean::cnstr_set(x_1, 1, x_1465);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1458);
return x_1;
}
else
{
obj* x_1480; 
lean::dec(x_234);
lean::cnstr_set_uint8(x_1275, sizeof(void*)*4, x_1458);
lean::cnstr_set(x_4, 3, x_1275);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_1403);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1237);
x_1480 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1480, 0, x_1471);
lean::cnstr_set(x_1480, 1, x_1472);
lean::cnstr_set(x_1480, 2, x_1473);
lean::cnstr_set(x_1480, 3, x_1474);
lean::cnstr_set_uint8(x_1480, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_1, 3, x_1480);
lean::cnstr_set(x_1, 2, x_1466);
lean::cnstr_set(x_1, 1, x_1465);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1458);
return x_1;
}
}
else
{
obj* x_1481; obj* x_1482; obj* x_1483; obj* x_1484; obj* x_1485; obj* x_1486; obj* x_1487; 
x_1481 = lean::cnstr_get(x_1403, 0);
x_1482 = lean::cnstr_get(x_1403, 1);
x_1483 = lean::cnstr_get(x_1403, 2);
x_1484 = lean::cnstr_get(x_1403, 3);
lean::inc(x_1484);
lean::inc(x_1483);
lean::inc(x_1482);
lean::inc(x_1481);
lean::dec(x_1403);
lean::inc(x_234);
x_1485 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1485, 0, x_234);
lean::cnstr_set(x_1485, 1, x_1460);
lean::cnstr_set(x_1485, 2, x_1461);
lean::cnstr_set(x_1485, 3, x_1265);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1486 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1486 = lean::box(0);
}
lean::cnstr_set_uint8(x_1485, sizeof(void*)*4, x_1458);
lean::cnstr_set_uint8(x_1275, sizeof(void*)*4, x_1458);
lean::cnstr_set(x_4, 3, x_1275);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_1485);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1237);
if (lean::is_scalar(x_1486)) {
 x_1487 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1487 = x_1486;
}
lean::cnstr_set(x_1487, 0, x_1481);
lean::cnstr_set(x_1487, 1, x_1482);
lean::cnstr_set(x_1487, 2, x_1483);
lean::cnstr_set(x_1487, 3, x_1484);
lean::cnstr_set_uint8(x_1487, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_1, 3, x_1487);
lean::cnstr_set(x_1, 2, x_1466);
lean::cnstr_set(x_1, 1, x_1465);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1458);
return x_1;
}
}
else
{
obj* x_1488; obj* x_1489; obj* x_1490; obj* x_1491; obj* x_1492; obj* x_1493; obj* x_1494; obj* x_1495; obj* x_1496; obj* x_1497; obj* x_1498; obj* x_1499; obj* x_1500; 
x_1488 = lean::cnstr_get(x_1275, 0);
x_1489 = lean::cnstr_get(x_1275, 1);
x_1490 = lean::cnstr_get(x_1275, 2);
x_1491 = lean::cnstr_get(x_1275, 3);
lean::inc(x_1491);
lean::inc(x_1490);
lean::inc(x_1489);
lean::inc(x_1488);
lean::dec(x_1275);
x_1492 = lean::cnstr_get(x_1403, 0);
lean::inc(x_1492);
x_1493 = lean::cnstr_get(x_1403, 1);
lean::inc(x_1493);
x_1494 = lean::cnstr_get(x_1403, 2);
lean::inc(x_1494);
x_1495 = lean::cnstr_get(x_1403, 3);
lean::inc(x_1495);
if (lean::is_exclusive(x_1403)) {
 lean::cnstr_release(x_1403, 0);
 lean::cnstr_release(x_1403, 1);
 lean::cnstr_release(x_1403, 2);
 lean::cnstr_release(x_1403, 3);
 x_1496 = x_1403;
} else {
 lean::dec_ref(x_1403);
 x_1496 = lean::box(0);
}
lean::inc(x_234);
if (lean::is_scalar(x_1496)) {
 x_1497 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1497 = x_1496;
}
lean::cnstr_set(x_1497, 0, x_234);
lean::cnstr_set(x_1497, 1, x_1460);
lean::cnstr_set(x_1497, 2, x_1461);
lean::cnstr_set(x_1497, 3, x_1265);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1498 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1498 = lean::box(0);
}
lean::cnstr_set_uint8(x_1497, sizeof(void*)*4, x_1458);
x_1499 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1499, 0, x_1488);
lean::cnstr_set(x_1499, 1, x_1489);
lean::cnstr_set(x_1499, 2, x_1490);
lean::cnstr_set(x_1499, 3, x_1491);
lean::cnstr_set_uint8(x_1499, sizeof(void*)*4, x_1458);
lean::cnstr_set(x_4, 3, x_1499);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_1497);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1237);
if (lean::is_scalar(x_1498)) {
 x_1500 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1500 = x_1498;
}
lean::cnstr_set(x_1500, 0, x_1492);
lean::cnstr_set(x_1500, 1, x_1493);
lean::cnstr_set(x_1500, 2, x_1494);
lean::cnstr_set(x_1500, 3, x_1495);
lean::cnstr_set_uint8(x_1500, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_1, 3, x_1500);
lean::cnstr_set(x_1, 2, x_1466);
lean::cnstr_set(x_1, 1, x_1465);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1458);
return x_1;
}
}
else
{
obj* x_1501; obj* x_1502; obj* x_1503; obj* x_1504; obj* x_1505; obj* x_1506; obj* x_1507; obj* x_1508; obj* x_1509; obj* x_1510; obj* x_1511; obj* x_1512; obj* x_1513; obj* x_1514; obj* x_1515; obj* x_1516; obj* x_1517; 
x_1501 = lean::cnstr_get(x_4, 1);
x_1502 = lean::cnstr_get(x_4, 2);
lean::inc(x_1502);
lean::inc(x_1501);
lean::dec(x_4);
x_1503 = lean::cnstr_get(x_1275, 0);
lean::inc(x_1503);
x_1504 = lean::cnstr_get(x_1275, 1);
lean::inc(x_1504);
x_1505 = lean::cnstr_get(x_1275, 2);
lean::inc(x_1505);
x_1506 = lean::cnstr_get(x_1275, 3);
lean::inc(x_1506);
if (lean::is_exclusive(x_1275)) {
 lean::cnstr_release(x_1275, 0);
 lean::cnstr_release(x_1275, 1);
 lean::cnstr_release(x_1275, 2);
 lean::cnstr_release(x_1275, 3);
 x_1507 = x_1275;
} else {
 lean::dec_ref(x_1275);
 x_1507 = lean::box(0);
}
x_1508 = lean::cnstr_get(x_1403, 0);
lean::inc(x_1508);
x_1509 = lean::cnstr_get(x_1403, 1);
lean::inc(x_1509);
x_1510 = lean::cnstr_get(x_1403, 2);
lean::inc(x_1510);
x_1511 = lean::cnstr_get(x_1403, 3);
lean::inc(x_1511);
if (lean::is_exclusive(x_1403)) {
 lean::cnstr_release(x_1403, 0);
 lean::cnstr_release(x_1403, 1);
 lean::cnstr_release(x_1403, 2);
 lean::cnstr_release(x_1403, 3);
 x_1512 = x_1403;
} else {
 lean::dec_ref(x_1403);
 x_1512 = lean::box(0);
}
lean::inc(x_234);
if (lean::is_scalar(x_1512)) {
 x_1513 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1513 = x_1512;
}
lean::cnstr_set(x_1513, 0, x_234);
lean::cnstr_set(x_1513, 1, x_1460);
lean::cnstr_set(x_1513, 2, x_1461);
lean::cnstr_set(x_1513, 3, x_1265);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1514 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1514 = lean::box(0);
}
lean::cnstr_set_uint8(x_1513, sizeof(void*)*4, x_1458);
if (lean::is_scalar(x_1507)) {
 x_1515 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1515 = x_1507;
}
lean::cnstr_set(x_1515, 0, x_1503);
lean::cnstr_set(x_1515, 1, x_1504);
lean::cnstr_set(x_1515, 2, x_1505);
lean::cnstr_set(x_1515, 3, x_1506);
lean::cnstr_set_uint8(x_1515, sizeof(void*)*4, x_1458);
x_1516 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1516, 0, x_1513);
lean::cnstr_set(x_1516, 1, x_2);
lean::cnstr_set(x_1516, 2, x_3);
lean::cnstr_set(x_1516, 3, x_1515);
lean::cnstr_set_uint8(x_1516, sizeof(void*)*4, x_1237);
if (lean::is_scalar(x_1514)) {
 x_1517 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1517 = x_1514;
}
lean::cnstr_set(x_1517, 0, x_1508);
lean::cnstr_set(x_1517, 1, x_1509);
lean::cnstr_set(x_1517, 2, x_1510);
lean::cnstr_set(x_1517, 3, x_1511);
lean::cnstr_set_uint8(x_1517, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_1, 3, x_1517);
lean::cnstr_set(x_1, 2, x_1502);
lean::cnstr_set(x_1, 1, x_1501);
lean::cnstr_set(x_1, 0, x_1516);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1458);
return x_1;
}
}
else
{
obj* x_1518; obj* x_1519; obj* x_1520; obj* x_1521; obj* x_1522; obj* x_1523; obj* x_1524; obj* x_1525; obj* x_1526; obj* x_1527; obj* x_1528; obj* x_1529; obj* x_1530; obj* x_1531; obj* x_1532; obj* x_1533; obj* x_1534; obj* x_1535; obj* x_1536; obj* x_1537; obj* x_1538; 
x_1518 = lean::cnstr_get(x_1, 1);
x_1519 = lean::cnstr_get(x_1, 2);
lean::inc(x_1519);
lean::inc(x_1518);
lean::dec(x_1);
x_1520 = lean::cnstr_get(x_4, 1);
lean::inc(x_1520);
x_1521 = lean::cnstr_get(x_4, 2);
lean::inc(x_1521);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1522 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1522 = lean::box(0);
}
x_1523 = lean::cnstr_get(x_1275, 0);
lean::inc(x_1523);
x_1524 = lean::cnstr_get(x_1275, 1);
lean::inc(x_1524);
x_1525 = lean::cnstr_get(x_1275, 2);
lean::inc(x_1525);
x_1526 = lean::cnstr_get(x_1275, 3);
lean::inc(x_1526);
if (lean::is_exclusive(x_1275)) {
 lean::cnstr_release(x_1275, 0);
 lean::cnstr_release(x_1275, 1);
 lean::cnstr_release(x_1275, 2);
 lean::cnstr_release(x_1275, 3);
 x_1527 = x_1275;
} else {
 lean::dec_ref(x_1275);
 x_1527 = lean::box(0);
}
x_1528 = lean::cnstr_get(x_1403, 0);
lean::inc(x_1528);
x_1529 = lean::cnstr_get(x_1403, 1);
lean::inc(x_1529);
x_1530 = lean::cnstr_get(x_1403, 2);
lean::inc(x_1530);
x_1531 = lean::cnstr_get(x_1403, 3);
lean::inc(x_1531);
if (lean::is_exclusive(x_1403)) {
 lean::cnstr_release(x_1403, 0);
 lean::cnstr_release(x_1403, 1);
 lean::cnstr_release(x_1403, 2);
 lean::cnstr_release(x_1403, 3);
 x_1532 = x_1403;
} else {
 lean::dec_ref(x_1403);
 x_1532 = lean::box(0);
}
lean::inc(x_234);
if (lean::is_scalar(x_1532)) {
 x_1533 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1533 = x_1532;
}
lean::cnstr_set(x_1533, 0, x_234);
lean::cnstr_set(x_1533, 1, x_1518);
lean::cnstr_set(x_1533, 2, x_1519);
lean::cnstr_set(x_1533, 3, x_1265);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1534 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1534 = lean::box(0);
}
lean::cnstr_set_uint8(x_1533, sizeof(void*)*4, x_1458);
if (lean::is_scalar(x_1527)) {
 x_1535 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1535 = x_1527;
}
lean::cnstr_set(x_1535, 0, x_1523);
lean::cnstr_set(x_1535, 1, x_1524);
lean::cnstr_set(x_1535, 2, x_1525);
lean::cnstr_set(x_1535, 3, x_1526);
lean::cnstr_set_uint8(x_1535, sizeof(void*)*4, x_1458);
if (lean::is_scalar(x_1522)) {
 x_1536 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1536 = x_1522;
}
lean::cnstr_set(x_1536, 0, x_1533);
lean::cnstr_set(x_1536, 1, x_2);
lean::cnstr_set(x_1536, 2, x_3);
lean::cnstr_set(x_1536, 3, x_1535);
lean::cnstr_set_uint8(x_1536, sizeof(void*)*4, x_1237);
if (lean::is_scalar(x_1534)) {
 x_1537 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1537 = x_1534;
}
lean::cnstr_set(x_1537, 0, x_1528);
lean::cnstr_set(x_1537, 1, x_1529);
lean::cnstr_set(x_1537, 2, x_1530);
lean::cnstr_set(x_1537, 3, x_1531);
lean::cnstr_set_uint8(x_1537, sizeof(void*)*4, x_1237);
x_1538 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1538, 0, x_1536);
lean::cnstr_set(x_1538, 1, x_1520);
lean::cnstr_set(x_1538, 2, x_1521);
lean::cnstr_set(x_1538, 3, x_1537);
lean::cnstr_set_uint8(x_1538, sizeof(void*)*4, x_1458);
return x_1538;
}
}
else
{
uint8 x_1539; 
x_1539 = !lean::is_exclusive(x_1);
if (x_1539 == 0)
{
obj* x_1540; obj* x_1541; obj* x_1542; obj* x_1543; uint8 x_1544; 
x_1540 = lean::cnstr_get(x_1, 1);
x_1541 = lean::cnstr_get(x_1, 2);
x_1542 = lean::cnstr_get(x_1, 3);
lean::dec(x_1542);
x_1543 = lean::cnstr_get(x_1, 0);
lean::dec(x_1543);
x_1544 = !lean::is_exclusive(x_234);
if (x_1544 == 0)
{
uint8 x_1545; 
x_1545 = !lean::is_exclusive(x_4);
if (x_1545 == 0)
{
obj* x_1546; obj* x_1547; obj* x_1548; obj* x_1549; obj* x_1550; obj* x_1551; obj* x_1552; obj* x_1553; uint8 x_1554; 
x_1546 = lean::cnstr_get(x_234, 0);
x_1547 = lean::cnstr_get(x_234, 1);
x_1548 = lean::cnstr_get(x_234, 2);
x_1549 = lean::cnstr_get(x_234, 3);
x_1550 = lean::cnstr_get(x_4, 1);
x_1551 = lean::cnstr_get(x_4, 2);
x_1552 = lean::cnstr_get(x_4, 3);
lean::dec(x_1552);
x_1553 = lean::cnstr_get(x_4, 0);
lean::dec(x_1553);
x_1554 = !lean::is_exclusive(x_1275);
if (x_1554 == 0)
{
obj* x_1555; obj* x_1556; obj* x_1557; obj* x_1558; obj* x_1559; 
x_1555 = lean::cnstr_get(x_1275, 0);
x_1556 = lean::cnstr_get(x_1275, 1);
x_1557 = lean::cnstr_get(x_1275, 2);
x_1558 = lean::cnstr_get(x_1275, 3);
lean::cnstr_set(x_1275, 3, x_1549);
lean::cnstr_set(x_1275, 2, x_1548);
lean::cnstr_set(x_1275, 1, x_1547);
lean::cnstr_set(x_1275, 0, x_1546);
lean::cnstr_set_uint8(x_1275, sizeof(void*)*4, x_1458);
lean::cnstr_set(x_4, 3, x_1265);
lean::cnstr_set(x_4, 2, x_1541);
lean::cnstr_set(x_4, 1, x_1540);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1402);
lean::cnstr_set(x_234, 3, x_1555);
lean::cnstr_set(x_234, 2, x_3);
lean::cnstr_set(x_234, 1, x_2);
lean::cnstr_set(x_234, 0, x_4);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1458);
lean::cnstr_set(x_1, 3, x_1403);
lean::cnstr_set(x_1, 2, x_1551);
lean::cnstr_set(x_1, 1, x_1550);
lean::cnstr_set(x_1, 0, x_1558);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1458);
x_1559 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1559, 0, x_234);
lean::cnstr_set(x_1559, 1, x_1556);
lean::cnstr_set(x_1559, 2, x_1557);
lean::cnstr_set(x_1559, 3, x_1);
lean::cnstr_set_uint8(x_1559, sizeof(void*)*4, x_1402);
return x_1559;
}
else
{
obj* x_1560; obj* x_1561; obj* x_1562; obj* x_1563; obj* x_1564; obj* x_1565; 
x_1560 = lean::cnstr_get(x_1275, 0);
x_1561 = lean::cnstr_get(x_1275, 1);
x_1562 = lean::cnstr_get(x_1275, 2);
x_1563 = lean::cnstr_get(x_1275, 3);
lean::inc(x_1563);
lean::inc(x_1562);
lean::inc(x_1561);
lean::inc(x_1560);
lean::dec(x_1275);
x_1564 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1564, 0, x_1546);
lean::cnstr_set(x_1564, 1, x_1547);
lean::cnstr_set(x_1564, 2, x_1548);
lean::cnstr_set(x_1564, 3, x_1549);
lean::cnstr_set_uint8(x_1564, sizeof(void*)*4, x_1458);
lean::cnstr_set(x_4, 3, x_1265);
lean::cnstr_set(x_4, 2, x_1541);
lean::cnstr_set(x_4, 1, x_1540);
lean::cnstr_set(x_4, 0, x_1564);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1402);
lean::cnstr_set(x_234, 3, x_1560);
lean::cnstr_set(x_234, 2, x_3);
lean::cnstr_set(x_234, 1, x_2);
lean::cnstr_set(x_234, 0, x_4);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1458);
lean::cnstr_set(x_1, 3, x_1403);
lean::cnstr_set(x_1, 2, x_1551);
lean::cnstr_set(x_1, 1, x_1550);
lean::cnstr_set(x_1, 0, x_1563);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1458);
x_1565 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1565, 0, x_234);
lean::cnstr_set(x_1565, 1, x_1561);
lean::cnstr_set(x_1565, 2, x_1562);
lean::cnstr_set(x_1565, 3, x_1);
lean::cnstr_set_uint8(x_1565, sizeof(void*)*4, x_1402);
return x_1565;
}
}
else
{
obj* x_1566; obj* x_1567; obj* x_1568; obj* x_1569; obj* x_1570; obj* x_1571; obj* x_1572; obj* x_1573; obj* x_1574; obj* x_1575; obj* x_1576; obj* x_1577; obj* x_1578; obj* x_1579; 
x_1566 = lean::cnstr_get(x_234, 0);
x_1567 = lean::cnstr_get(x_234, 1);
x_1568 = lean::cnstr_get(x_234, 2);
x_1569 = lean::cnstr_get(x_234, 3);
x_1570 = lean::cnstr_get(x_4, 1);
x_1571 = lean::cnstr_get(x_4, 2);
lean::inc(x_1571);
lean::inc(x_1570);
lean::dec(x_4);
x_1572 = lean::cnstr_get(x_1275, 0);
lean::inc(x_1572);
x_1573 = lean::cnstr_get(x_1275, 1);
lean::inc(x_1573);
x_1574 = lean::cnstr_get(x_1275, 2);
lean::inc(x_1574);
x_1575 = lean::cnstr_get(x_1275, 3);
lean::inc(x_1575);
if (lean::is_exclusive(x_1275)) {
 lean::cnstr_release(x_1275, 0);
 lean::cnstr_release(x_1275, 1);
 lean::cnstr_release(x_1275, 2);
 lean::cnstr_release(x_1275, 3);
 x_1576 = x_1275;
} else {
 lean::dec_ref(x_1275);
 x_1576 = lean::box(0);
}
if (lean::is_scalar(x_1576)) {
 x_1577 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1577 = x_1576;
}
lean::cnstr_set(x_1577, 0, x_1566);
lean::cnstr_set(x_1577, 1, x_1567);
lean::cnstr_set(x_1577, 2, x_1568);
lean::cnstr_set(x_1577, 3, x_1569);
lean::cnstr_set_uint8(x_1577, sizeof(void*)*4, x_1458);
x_1578 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1578, 0, x_1577);
lean::cnstr_set(x_1578, 1, x_1540);
lean::cnstr_set(x_1578, 2, x_1541);
lean::cnstr_set(x_1578, 3, x_1265);
lean::cnstr_set_uint8(x_1578, sizeof(void*)*4, x_1402);
lean::cnstr_set(x_234, 3, x_1572);
lean::cnstr_set(x_234, 2, x_3);
lean::cnstr_set(x_234, 1, x_2);
lean::cnstr_set(x_234, 0, x_1578);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1458);
lean::cnstr_set(x_1, 3, x_1403);
lean::cnstr_set(x_1, 2, x_1571);
lean::cnstr_set(x_1, 1, x_1570);
lean::cnstr_set(x_1, 0, x_1575);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1458);
x_1579 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1579, 0, x_234);
lean::cnstr_set(x_1579, 1, x_1573);
lean::cnstr_set(x_1579, 2, x_1574);
lean::cnstr_set(x_1579, 3, x_1);
lean::cnstr_set_uint8(x_1579, sizeof(void*)*4, x_1402);
return x_1579;
}
}
else
{
obj* x_1580; obj* x_1581; obj* x_1582; obj* x_1583; obj* x_1584; obj* x_1585; obj* x_1586; obj* x_1587; obj* x_1588; obj* x_1589; obj* x_1590; obj* x_1591; obj* x_1592; obj* x_1593; obj* x_1594; obj* x_1595; 
x_1580 = lean::cnstr_get(x_234, 0);
x_1581 = lean::cnstr_get(x_234, 1);
x_1582 = lean::cnstr_get(x_234, 2);
x_1583 = lean::cnstr_get(x_234, 3);
lean::inc(x_1583);
lean::inc(x_1582);
lean::inc(x_1581);
lean::inc(x_1580);
lean::dec(x_234);
x_1584 = lean::cnstr_get(x_4, 1);
lean::inc(x_1584);
x_1585 = lean::cnstr_get(x_4, 2);
lean::inc(x_1585);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1586 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1586 = lean::box(0);
}
x_1587 = lean::cnstr_get(x_1275, 0);
lean::inc(x_1587);
x_1588 = lean::cnstr_get(x_1275, 1);
lean::inc(x_1588);
x_1589 = lean::cnstr_get(x_1275, 2);
lean::inc(x_1589);
x_1590 = lean::cnstr_get(x_1275, 3);
lean::inc(x_1590);
if (lean::is_exclusive(x_1275)) {
 lean::cnstr_release(x_1275, 0);
 lean::cnstr_release(x_1275, 1);
 lean::cnstr_release(x_1275, 2);
 lean::cnstr_release(x_1275, 3);
 x_1591 = x_1275;
} else {
 lean::dec_ref(x_1275);
 x_1591 = lean::box(0);
}
if (lean::is_scalar(x_1591)) {
 x_1592 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1592 = x_1591;
}
lean::cnstr_set(x_1592, 0, x_1580);
lean::cnstr_set(x_1592, 1, x_1581);
lean::cnstr_set(x_1592, 2, x_1582);
lean::cnstr_set(x_1592, 3, x_1583);
lean::cnstr_set_uint8(x_1592, sizeof(void*)*4, x_1458);
if (lean::is_scalar(x_1586)) {
 x_1593 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1593 = x_1586;
}
lean::cnstr_set(x_1593, 0, x_1592);
lean::cnstr_set(x_1593, 1, x_1540);
lean::cnstr_set(x_1593, 2, x_1541);
lean::cnstr_set(x_1593, 3, x_1265);
lean::cnstr_set_uint8(x_1593, sizeof(void*)*4, x_1402);
x_1594 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1594, 0, x_1593);
lean::cnstr_set(x_1594, 1, x_2);
lean::cnstr_set(x_1594, 2, x_3);
lean::cnstr_set(x_1594, 3, x_1587);
lean::cnstr_set_uint8(x_1594, sizeof(void*)*4, x_1458);
lean::cnstr_set(x_1, 3, x_1403);
lean::cnstr_set(x_1, 2, x_1585);
lean::cnstr_set(x_1, 1, x_1584);
lean::cnstr_set(x_1, 0, x_1590);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1458);
x_1595 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1595, 0, x_1594);
lean::cnstr_set(x_1595, 1, x_1588);
lean::cnstr_set(x_1595, 2, x_1589);
lean::cnstr_set(x_1595, 3, x_1);
lean::cnstr_set_uint8(x_1595, sizeof(void*)*4, x_1402);
return x_1595;
}
}
else
{
obj* x_1596; obj* x_1597; obj* x_1598; obj* x_1599; obj* x_1600; obj* x_1601; obj* x_1602; obj* x_1603; obj* x_1604; obj* x_1605; obj* x_1606; obj* x_1607; obj* x_1608; obj* x_1609; obj* x_1610; obj* x_1611; obj* x_1612; obj* x_1613; obj* x_1614; obj* x_1615; 
x_1596 = lean::cnstr_get(x_1, 1);
x_1597 = lean::cnstr_get(x_1, 2);
lean::inc(x_1597);
lean::inc(x_1596);
lean::dec(x_1);
x_1598 = lean::cnstr_get(x_234, 0);
lean::inc(x_1598);
x_1599 = lean::cnstr_get(x_234, 1);
lean::inc(x_1599);
x_1600 = lean::cnstr_get(x_234, 2);
lean::inc(x_1600);
x_1601 = lean::cnstr_get(x_234, 3);
lean::inc(x_1601);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1602 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1602 = lean::box(0);
}
x_1603 = lean::cnstr_get(x_4, 1);
lean::inc(x_1603);
x_1604 = lean::cnstr_get(x_4, 2);
lean::inc(x_1604);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1605 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1605 = lean::box(0);
}
x_1606 = lean::cnstr_get(x_1275, 0);
lean::inc(x_1606);
x_1607 = lean::cnstr_get(x_1275, 1);
lean::inc(x_1607);
x_1608 = lean::cnstr_get(x_1275, 2);
lean::inc(x_1608);
x_1609 = lean::cnstr_get(x_1275, 3);
lean::inc(x_1609);
if (lean::is_exclusive(x_1275)) {
 lean::cnstr_release(x_1275, 0);
 lean::cnstr_release(x_1275, 1);
 lean::cnstr_release(x_1275, 2);
 lean::cnstr_release(x_1275, 3);
 x_1610 = x_1275;
} else {
 lean::dec_ref(x_1275);
 x_1610 = lean::box(0);
}
if (lean::is_scalar(x_1610)) {
 x_1611 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1611 = x_1610;
}
lean::cnstr_set(x_1611, 0, x_1598);
lean::cnstr_set(x_1611, 1, x_1599);
lean::cnstr_set(x_1611, 2, x_1600);
lean::cnstr_set(x_1611, 3, x_1601);
lean::cnstr_set_uint8(x_1611, sizeof(void*)*4, x_1458);
if (lean::is_scalar(x_1605)) {
 x_1612 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1612 = x_1605;
}
lean::cnstr_set(x_1612, 0, x_1611);
lean::cnstr_set(x_1612, 1, x_1596);
lean::cnstr_set(x_1612, 2, x_1597);
lean::cnstr_set(x_1612, 3, x_1265);
lean::cnstr_set_uint8(x_1612, sizeof(void*)*4, x_1402);
if (lean::is_scalar(x_1602)) {
 x_1613 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1613 = x_1602;
}
lean::cnstr_set(x_1613, 0, x_1612);
lean::cnstr_set(x_1613, 1, x_2);
lean::cnstr_set(x_1613, 2, x_3);
lean::cnstr_set(x_1613, 3, x_1606);
lean::cnstr_set_uint8(x_1613, sizeof(void*)*4, x_1458);
x_1614 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1614, 0, x_1609);
lean::cnstr_set(x_1614, 1, x_1603);
lean::cnstr_set(x_1614, 2, x_1604);
lean::cnstr_set(x_1614, 3, x_1403);
lean::cnstr_set_uint8(x_1614, sizeof(void*)*4, x_1458);
x_1615 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1615, 0, x_1613);
lean::cnstr_set(x_1615, 1, x_1607);
lean::cnstr_set(x_1615, 2, x_1608);
lean::cnstr_set(x_1615, 3, x_1614);
lean::cnstr_set_uint8(x_1615, sizeof(void*)*4, x_1402);
return x_1615;
}
}
}
}
else
{
obj* x_1616; 
x_1616 = lean::cnstr_get(x_4, 3);
lean::inc(x_1616);
if (lean::obj_tag(x_1616) == 0)
{
uint8 x_1617; 
x_1617 = !lean::is_exclusive(x_1275);
if (x_1617 == 0)
{
obj* x_1618; obj* x_1619; obj* x_1620; obj* x_1621; uint8 x_1622; 
x_1618 = lean::cnstr_get(x_1275, 3);
lean::dec(x_1618);
x_1619 = lean::cnstr_get(x_1275, 2);
lean::dec(x_1619);
x_1620 = lean::cnstr_get(x_1275, 1);
lean::dec(x_1620);
x_1621 = lean::cnstr_get(x_1275, 0);
lean::dec(x_1621);
x_1622 = !lean::is_exclusive(x_1);
if (x_1622 == 0)
{
obj* x_1623; obj* x_1624; obj* x_1625; obj* x_1626; uint8 x_1627; 
x_1623 = lean::cnstr_get(x_1, 1);
x_1624 = lean::cnstr_get(x_1, 2);
x_1625 = lean::cnstr_get(x_1, 3);
lean::dec(x_1625);
x_1626 = lean::cnstr_get(x_1, 0);
lean::dec(x_1626);
x_1627 = !lean::is_exclusive(x_234);
if (x_1627 == 0)
{
obj* x_1628; obj* x_1629; obj* x_1630; obj* x_1631; 
x_1628 = lean::cnstr_get(x_234, 0);
x_1629 = lean::cnstr_get(x_234, 1);
x_1630 = lean::cnstr_get(x_234, 2);
x_1631 = lean::cnstr_get(x_234, 3);
lean::cnstr_set(x_1275, 3, x_1631);
lean::cnstr_set(x_1275, 2, x_1630);
lean::cnstr_set(x_1275, 1, x_1629);
lean::cnstr_set(x_1275, 0, x_1628);
lean::cnstr_set(x_234, 3, x_1616);
lean::cnstr_set(x_234, 2, x_1624);
lean::cnstr_set(x_234, 1, x_1623);
lean::cnstr_set(x_234, 0, x_1275);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1274);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1402);
return x_1;
}
else
{
obj* x_1632; obj* x_1633; obj* x_1634; obj* x_1635; obj* x_1636; 
x_1632 = lean::cnstr_get(x_234, 0);
x_1633 = lean::cnstr_get(x_234, 1);
x_1634 = lean::cnstr_get(x_234, 2);
x_1635 = lean::cnstr_get(x_234, 3);
lean::inc(x_1635);
lean::inc(x_1634);
lean::inc(x_1633);
lean::inc(x_1632);
lean::dec(x_234);
lean::cnstr_set(x_1275, 3, x_1635);
lean::cnstr_set(x_1275, 2, x_1634);
lean::cnstr_set(x_1275, 1, x_1633);
lean::cnstr_set(x_1275, 0, x_1632);
x_1636 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1636, 0, x_1275);
lean::cnstr_set(x_1636, 1, x_1623);
lean::cnstr_set(x_1636, 2, x_1624);
lean::cnstr_set(x_1636, 3, x_1616);
lean::cnstr_set_uint8(x_1636, sizeof(void*)*4, x_1274);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_1636);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1402);
return x_1;
}
}
else
{
obj* x_1637; obj* x_1638; obj* x_1639; obj* x_1640; obj* x_1641; obj* x_1642; obj* x_1643; obj* x_1644; obj* x_1645; 
x_1637 = lean::cnstr_get(x_1, 1);
x_1638 = lean::cnstr_get(x_1, 2);
lean::inc(x_1638);
lean::inc(x_1637);
lean::dec(x_1);
x_1639 = lean::cnstr_get(x_234, 0);
lean::inc(x_1639);
x_1640 = lean::cnstr_get(x_234, 1);
lean::inc(x_1640);
x_1641 = lean::cnstr_get(x_234, 2);
lean::inc(x_1641);
x_1642 = lean::cnstr_get(x_234, 3);
lean::inc(x_1642);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1643 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1643 = lean::box(0);
}
lean::cnstr_set(x_1275, 3, x_1642);
lean::cnstr_set(x_1275, 2, x_1641);
lean::cnstr_set(x_1275, 1, x_1640);
lean::cnstr_set(x_1275, 0, x_1639);
if (lean::is_scalar(x_1643)) {
 x_1644 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1644 = x_1643;
}
lean::cnstr_set(x_1644, 0, x_1275);
lean::cnstr_set(x_1644, 1, x_1637);
lean::cnstr_set(x_1644, 2, x_1638);
lean::cnstr_set(x_1644, 3, x_1616);
lean::cnstr_set_uint8(x_1644, sizeof(void*)*4, x_1274);
x_1645 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1645, 0, x_1644);
lean::cnstr_set(x_1645, 1, x_2);
lean::cnstr_set(x_1645, 2, x_3);
lean::cnstr_set(x_1645, 3, x_4);
lean::cnstr_set_uint8(x_1645, sizeof(void*)*4, x_1402);
return x_1645;
}
}
else
{
obj* x_1646; obj* x_1647; obj* x_1648; obj* x_1649; obj* x_1650; obj* x_1651; obj* x_1652; obj* x_1653; obj* x_1654; obj* x_1655; obj* x_1656; 
lean::dec(x_1275);
x_1646 = lean::cnstr_get(x_1, 1);
lean::inc(x_1646);
x_1647 = lean::cnstr_get(x_1, 2);
lean::inc(x_1647);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_1648 = x_1;
} else {
 lean::dec_ref(x_1);
 x_1648 = lean::box(0);
}
x_1649 = lean::cnstr_get(x_234, 0);
lean::inc(x_1649);
x_1650 = lean::cnstr_get(x_234, 1);
lean::inc(x_1650);
x_1651 = lean::cnstr_get(x_234, 2);
lean::inc(x_1651);
x_1652 = lean::cnstr_get(x_234, 3);
lean::inc(x_1652);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1653 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1653 = lean::box(0);
}
x_1654 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1654, 0, x_1649);
lean::cnstr_set(x_1654, 1, x_1650);
lean::cnstr_set(x_1654, 2, x_1651);
lean::cnstr_set(x_1654, 3, x_1652);
lean::cnstr_set_uint8(x_1654, sizeof(void*)*4, x_1402);
if (lean::is_scalar(x_1653)) {
 x_1655 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1655 = x_1653;
}
lean::cnstr_set(x_1655, 0, x_1654);
lean::cnstr_set(x_1655, 1, x_1646);
lean::cnstr_set(x_1655, 2, x_1647);
lean::cnstr_set(x_1655, 3, x_1616);
lean::cnstr_set_uint8(x_1655, sizeof(void*)*4, x_1274);
if (lean::is_scalar(x_1648)) {
 x_1656 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1656 = x_1648;
}
lean::cnstr_set(x_1656, 0, x_1655);
lean::cnstr_set(x_1656, 1, x_2);
lean::cnstr_set(x_1656, 2, x_3);
lean::cnstr_set(x_1656, 3, x_4);
lean::cnstr_set_uint8(x_1656, sizeof(void*)*4, x_1402);
return x_1656;
}
}
else
{
uint8 x_1657; 
x_1657 = lean::cnstr_get_uint8(x_1616, sizeof(void*)*4);
if (x_1657 == 0)
{
uint8 x_1658; 
x_1658 = !lean::is_exclusive(x_1);
if (x_1658 == 0)
{
obj* x_1659; obj* x_1660; obj* x_1661; obj* x_1662; uint8 x_1663; 
x_1659 = lean::cnstr_get(x_1, 1);
x_1660 = lean::cnstr_get(x_1, 2);
x_1661 = lean::cnstr_get(x_1, 3);
lean::dec(x_1661);
x_1662 = lean::cnstr_get(x_1, 0);
lean::dec(x_1662);
x_1663 = !lean::is_exclusive(x_234);
if (x_1663 == 0)
{
uint8 x_1664; 
x_1664 = !lean::is_exclusive(x_4);
if (x_1664 == 0)
{
obj* x_1665; obj* x_1666; obj* x_1667; obj* x_1668; obj* x_1669; obj* x_1670; obj* x_1671; obj* x_1672; uint8 x_1673; 
x_1665 = lean::cnstr_get(x_234, 0);
x_1666 = lean::cnstr_get(x_234, 1);
x_1667 = lean::cnstr_get(x_234, 2);
x_1668 = lean::cnstr_get(x_234, 3);
x_1669 = lean::cnstr_get(x_4, 1);
x_1670 = lean::cnstr_get(x_4, 2);
x_1671 = lean::cnstr_get(x_4, 3);
lean::dec(x_1671);
x_1672 = lean::cnstr_get(x_4, 0);
lean::dec(x_1672);
x_1673 = !lean::is_exclusive(x_1616);
if (x_1673 == 0)
{
obj* x_1674; obj* x_1675; obj* x_1676; obj* x_1677; obj* x_1678; 
x_1674 = lean::cnstr_get(x_1616, 0);
x_1675 = lean::cnstr_get(x_1616, 1);
x_1676 = lean::cnstr_get(x_1616, 2);
x_1677 = lean::cnstr_get(x_1616, 3);
lean::cnstr_set(x_1616, 3, x_1668);
lean::cnstr_set(x_1616, 2, x_1667);
lean::cnstr_set(x_1616, 1, x_1666);
lean::cnstr_set(x_1616, 0, x_1665);
lean::cnstr_set_uint8(x_1616, sizeof(void*)*4, x_1402);
lean::cnstr_set(x_4, 3, x_1265);
lean::cnstr_set(x_4, 2, x_1660);
lean::cnstr_set(x_4, 1, x_1659);
lean::cnstr_set(x_4, 0, x_1616);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1657);
lean::cnstr_set(x_234, 3, x_1275);
lean::cnstr_set(x_234, 2, x_3);
lean::cnstr_set(x_234, 1, x_2);
lean::cnstr_set(x_234, 0, x_4);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1402);
lean::cnstr_set(x_1, 3, x_1677);
lean::cnstr_set(x_1, 2, x_1676);
lean::cnstr_set(x_1, 1, x_1675);
lean::cnstr_set(x_1, 0, x_1674);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1402);
x_1678 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1678, 0, x_234);
lean::cnstr_set(x_1678, 1, x_1669);
lean::cnstr_set(x_1678, 2, x_1670);
lean::cnstr_set(x_1678, 3, x_1);
lean::cnstr_set_uint8(x_1678, sizeof(void*)*4, x_1657);
return x_1678;
}
else
{
obj* x_1679; obj* x_1680; obj* x_1681; obj* x_1682; obj* x_1683; obj* x_1684; 
x_1679 = lean::cnstr_get(x_1616, 0);
x_1680 = lean::cnstr_get(x_1616, 1);
x_1681 = lean::cnstr_get(x_1616, 2);
x_1682 = lean::cnstr_get(x_1616, 3);
lean::inc(x_1682);
lean::inc(x_1681);
lean::inc(x_1680);
lean::inc(x_1679);
lean::dec(x_1616);
x_1683 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1683, 0, x_1665);
lean::cnstr_set(x_1683, 1, x_1666);
lean::cnstr_set(x_1683, 2, x_1667);
lean::cnstr_set(x_1683, 3, x_1668);
lean::cnstr_set_uint8(x_1683, sizeof(void*)*4, x_1402);
lean::cnstr_set(x_4, 3, x_1265);
lean::cnstr_set(x_4, 2, x_1660);
lean::cnstr_set(x_4, 1, x_1659);
lean::cnstr_set(x_4, 0, x_1683);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1657);
lean::cnstr_set(x_234, 3, x_1275);
lean::cnstr_set(x_234, 2, x_3);
lean::cnstr_set(x_234, 1, x_2);
lean::cnstr_set(x_234, 0, x_4);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1402);
lean::cnstr_set(x_1, 3, x_1682);
lean::cnstr_set(x_1, 2, x_1681);
lean::cnstr_set(x_1, 1, x_1680);
lean::cnstr_set(x_1, 0, x_1679);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1402);
x_1684 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1684, 0, x_234);
lean::cnstr_set(x_1684, 1, x_1669);
lean::cnstr_set(x_1684, 2, x_1670);
lean::cnstr_set(x_1684, 3, x_1);
lean::cnstr_set_uint8(x_1684, sizeof(void*)*4, x_1657);
return x_1684;
}
}
else
{
obj* x_1685; obj* x_1686; obj* x_1687; obj* x_1688; obj* x_1689; obj* x_1690; obj* x_1691; obj* x_1692; obj* x_1693; obj* x_1694; obj* x_1695; obj* x_1696; obj* x_1697; obj* x_1698; 
x_1685 = lean::cnstr_get(x_234, 0);
x_1686 = lean::cnstr_get(x_234, 1);
x_1687 = lean::cnstr_get(x_234, 2);
x_1688 = lean::cnstr_get(x_234, 3);
x_1689 = lean::cnstr_get(x_4, 1);
x_1690 = lean::cnstr_get(x_4, 2);
lean::inc(x_1690);
lean::inc(x_1689);
lean::dec(x_4);
x_1691 = lean::cnstr_get(x_1616, 0);
lean::inc(x_1691);
x_1692 = lean::cnstr_get(x_1616, 1);
lean::inc(x_1692);
x_1693 = lean::cnstr_get(x_1616, 2);
lean::inc(x_1693);
x_1694 = lean::cnstr_get(x_1616, 3);
lean::inc(x_1694);
if (lean::is_exclusive(x_1616)) {
 lean::cnstr_release(x_1616, 0);
 lean::cnstr_release(x_1616, 1);
 lean::cnstr_release(x_1616, 2);
 lean::cnstr_release(x_1616, 3);
 x_1695 = x_1616;
} else {
 lean::dec_ref(x_1616);
 x_1695 = lean::box(0);
}
if (lean::is_scalar(x_1695)) {
 x_1696 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1696 = x_1695;
}
lean::cnstr_set(x_1696, 0, x_1685);
lean::cnstr_set(x_1696, 1, x_1686);
lean::cnstr_set(x_1696, 2, x_1687);
lean::cnstr_set(x_1696, 3, x_1688);
lean::cnstr_set_uint8(x_1696, sizeof(void*)*4, x_1402);
x_1697 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1697, 0, x_1696);
lean::cnstr_set(x_1697, 1, x_1659);
lean::cnstr_set(x_1697, 2, x_1660);
lean::cnstr_set(x_1697, 3, x_1265);
lean::cnstr_set_uint8(x_1697, sizeof(void*)*4, x_1657);
lean::cnstr_set(x_234, 3, x_1275);
lean::cnstr_set(x_234, 2, x_3);
lean::cnstr_set(x_234, 1, x_2);
lean::cnstr_set(x_234, 0, x_1697);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1402);
lean::cnstr_set(x_1, 3, x_1694);
lean::cnstr_set(x_1, 2, x_1693);
lean::cnstr_set(x_1, 1, x_1692);
lean::cnstr_set(x_1, 0, x_1691);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1402);
x_1698 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1698, 0, x_234);
lean::cnstr_set(x_1698, 1, x_1689);
lean::cnstr_set(x_1698, 2, x_1690);
lean::cnstr_set(x_1698, 3, x_1);
lean::cnstr_set_uint8(x_1698, sizeof(void*)*4, x_1657);
return x_1698;
}
}
else
{
obj* x_1699; obj* x_1700; obj* x_1701; obj* x_1702; obj* x_1703; obj* x_1704; obj* x_1705; obj* x_1706; obj* x_1707; obj* x_1708; obj* x_1709; obj* x_1710; obj* x_1711; obj* x_1712; obj* x_1713; obj* x_1714; 
x_1699 = lean::cnstr_get(x_234, 0);
x_1700 = lean::cnstr_get(x_234, 1);
x_1701 = lean::cnstr_get(x_234, 2);
x_1702 = lean::cnstr_get(x_234, 3);
lean::inc(x_1702);
lean::inc(x_1701);
lean::inc(x_1700);
lean::inc(x_1699);
lean::dec(x_234);
x_1703 = lean::cnstr_get(x_4, 1);
lean::inc(x_1703);
x_1704 = lean::cnstr_get(x_4, 2);
lean::inc(x_1704);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1705 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1705 = lean::box(0);
}
x_1706 = lean::cnstr_get(x_1616, 0);
lean::inc(x_1706);
x_1707 = lean::cnstr_get(x_1616, 1);
lean::inc(x_1707);
x_1708 = lean::cnstr_get(x_1616, 2);
lean::inc(x_1708);
x_1709 = lean::cnstr_get(x_1616, 3);
lean::inc(x_1709);
if (lean::is_exclusive(x_1616)) {
 lean::cnstr_release(x_1616, 0);
 lean::cnstr_release(x_1616, 1);
 lean::cnstr_release(x_1616, 2);
 lean::cnstr_release(x_1616, 3);
 x_1710 = x_1616;
} else {
 lean::dec_ref(x_1616);
 x_1710 = lean::box(0);
}
if (lean::is_scalar(x_1710)) {
 x_1711 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1711 = x_1710;
}
lean::cnstr_set(x_1711, 0, x_1699);
lean::cnstr_set(x_1711, 1, x_1700);
lean::cnstr_set(x_1711, 2, x_1701);
lean::cnstr_set(x_1711, 3, x_1702);
lean::cnstr_set_uint8(x_1711, sizeof(void*)*4, x_1402);
if (lean::is_scalar(x_1705)) {
 x_1712 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1712 = x_1705;
}
lean::cnstr_set(x_1712, 0, x_1711);
lean::cnstr_set(x_1712, 1, x_1659);
lean::cnstr_set(x_1712, 2, x_1660);
lean::cnstr_set(x_1712, 3, x_1265);
lean::cnstr_set_uint8(x_1712, sizeof(void*)*4, x_1657);
x_1713 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1713, 0, x_1712);
lean::cnstr_set(x_1713, 1, x_2);
lean::cnstr_set(x_1713, 2, x_3);
lean::cnstr_set(x_1713, 3, x_1275);
lean::cnstr_set_uint8(x_1713, sizeof(void*)*4, x_1402);
lean::cnstr_set(x_1, 3, x_1709);
lean::cnstr_set(x_1, 2, x_1708);
lean::cnstr_set(x_1, 1, x_1707);
lean::cnstr_set(x_1, 0, x_1706);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1402);
x_1714 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1714, 0, x_1713);
lean::cnstr_set(x_1714, 1, x_1703);
lean::cnstr_set(x_1714, 2, x_1704);
lean::cnstr_set(x_1714, 3, x_1);
lean::cnstr_set_uint8(x_1714, sizeof(void*)*4, x_1657);
return x_1714;
}
}
else
{
obj* x_1715; obj* x_1716; obj* x_1717; obj* x_1718; obj* x_1719; obj* x_1720; obj* x_1721; obj* x_1722; obj* x_1723; obj* x_1724; obj* x_1725; obj* x_1726; obj* x_1727; obj* x_1728; obj* x_1729; obj* x_1730; obj* x_1731; obj* x_1732; obj* x_1733; obj* x_1734; 
x_1715 = lean::cnstr_get(x_1, 1);
x_1716 = lean::cnstr_get(x_1, 2);
lean::inc(x_1716);
lean::inc(x_1715);
lean::dec(x_1);
x_1717 = lean::cnstr_get(x_234, 0);
lean::inc(x_1717);
x_1718 = lean::cnstr_get(x_234, 1);
lean::inc(x_1718);
x_1719 = lean::cnstr_get(x_234, 2);
lean::inc(x_1719);
x_1720 = lean::cnstr_get(x_234, 3);
lean::inc(x_1720);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1721 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1721 = lean::box(0);
}
x_1722 = lean::cnstr_get(x_4, 1);
lean::inc(x_1722);
x_1723 = lean::cnstr_get(x_4, 2);
lean::inc(x_1723);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1724 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1724 = lean::box(0);
}
x_1725 = lean::cnstr_get(x_1616, 0);
lean::inc(x_1725);
x_1726 = lean::cnstr_get(x_1616, 1);
lean::inc(x_1726);
x_1727 = lean::cnstr_get(x_1616, 2);
lean::inc(x_1727);
x_1728 = lean::cnstr_get(x_1616, 3);
lean::inc(x_1728);
if (lean::is_exclusive(x_1616)) {
 lean::cnstr_release(x_1616, 0);
 lean::cnstr_release(x_1616, 1);
 lean::cnstr_release(x_1616, 2);
 lean::cnstr_release(x_1616, 3);
 x_1729 = x_1616;
} else {
 lean::dec_ref(x_1616);
 x_1729 = lean::box(0);
}
if (lean::is_scalar(x_1729)) {
 x_1730 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1730 = x_1729;
}
lean::cnstr_set(x_1730, 0, x_1717);
lean::cnstr_set(x_1730, 1, x_1718);
lean::cnstr_set(x_1730, 2, x_1719);
lean::cnstr_set(x_1730, 3, x_1720);
lean::cnstr_set_uint8(x_1730, sizeof(void*)*4, x_1402);
if (lean::is_scalar(x_1724)) {
 x_1731 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1731 = x_1724;
}
lean::cnstr_set(x_1731, 0, x_1730);
lean::cnstr_set(x_1731, 1, x_1715);
lean::cnstr_set(x_1731, 2, x_1716);
lean::cnstr_set(x_1731, 3, x_1265);
lean::cnstr_set_uint8(x_1731, sizeof(void*)*4, x_1657);
if (lean::is_scalar(x_1721)) {
 x_1732 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1732 = x_1721;
}
lean::cnstr_set(x_1732, 0, x_1731);
lean::cnstr_set(x_1732, 1, x_2);
lean::cnstr_set(x_1732, 2, x_3);
lean::cnstr_set(x_1732, 3, x_1275);
lean::cnstr_set_uint8(x_1732, sizeof(void*)*4, x_1402);
x_1733 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1733, 0, x_1725);
lean::cnstr_set(x_1733, 1, x_1726);
lean::cnstr_set(x_1733, 2, x_1727);
lean::cnstr_set(x_1733, 3, x_1728);
lean::cnstr_set_uint8(x_1733, sizeof(void*)*4, x_1402);
x_1734 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1734, 0, x_1732);
lean::cnstr_set(x_1734, 1, x_1722);
lean::cnstr_set(x_1734, 2, x_1723);
lean::cnstr_set(x_1734, 3, x_1733);
lean::cnstr_set_uint8(x_1734, sizeof(void*)*4, x_1657);
return x_1734;
}
}
else
{
uint8 x_1735; 
x_1735 = !lean::is_exclusive(x_1);
if (x_1735 == 0)
{
obj* x_1736; obj* x_1737; obj* x_1738; obj* x_1739; uint8 x_1740; 
x_1736 = lean::cnstr_get(x_1, 1);
x_1737 = lean::cnstr_get(x_1, 2);
x_1738 = lean::cnstr_get(x_1, 3);
lean::dec(x_1738);
x_1739 = lean::cnstr_get(x_1, 0);
lean::dec(x_1739);
x_1740 = !lean::is_exclusive(x_234);
if (x_1740 == 0)
{
uint8 x_1741; 
x_1741 = !lean::is_exclusive(x_4);
if (x_1741 == 0)
{
obj* x_1742; obj* x_1743; obj* x_1744; obj* x_1745; obj* x_1746; obj* x_1747; obj* x_1748; obj* x_1749; uint8 x_1750; 
x_1742 = lean::cnstr_get(x_234, 0);
x_1743 = lean::cnstr_get(x_234, 1);
x_1744 = lean::cnstr_get(x_234, 2);
x_1745 = lean::cnstr_get(x_234, 3);
x_1746 = lean::cnstr_get(x_4, 1);
x_1747 = lean::cnstr_get(x_4, 2);
x_1748 = lean::cnstr_get(x_4, 3);
lean::dec(x_1748);
x_1749 = lean::cnstr_get(x_4, 0);
lean::dec(x_1749);
x_1750 = !lean::is_exclusive(x_1275);
if (x_1750 == 0)
{
obj* x_1751; obj* x_1752; obj* x_1753; obj* x_1754; obj* x_1755; 
x_1751 = lean::cnstr_get(x_1275, 0);
x_1752 = lean::cnstr_get(x_1275, 1);
x_1753 = lean::cnstr_get(x_1275, 2);
x_1754 = lean::cnstr_get(x_1275, 3);
lean::cnstr_set(x_1275, 3, x_1745);
lean::cnstr_set(x_1275, 2, x_1744);
lean::cnstr_set(x_1275, 1, x_1743);
lean::cnstr_set(x_1275, 0, x_1742);
lean::cnstr_set_uint8(x_1275, sizeof(void*)*4, x_1657);
lean::cnstr_set(x_4, 3, x_1265);
lean::cnstr_set(x_4, 2, x_1737);
lean::cnstr_set(x_4, 1, x_1736);
lean::cnstr_set(x_234, 3, x_1754);
lean::cnstr_set(x_234, 2, x_1753);
lean::cnstr_set(x_234, 1, x_1752);
lean::cnstr_set(x_234, 0, x_1751);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1657);
lean::cnstr_set(x_1, 3, x_1616);
lean::cnstr_set(x_1, 2, x_1747);
lean::cnstr_set(x_1, 1, x_1746);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1274);
x_1755 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1755, 0, x_4);
lean::cnstr_set(x_1755, 1, x_2);
lean::cnstr_set(x_1755, 2, x_3);
lean::cnstr_set(x_1755, 3, x_1);
lean::cnstr_set_uint8(x_1755, sizeof(void*)*4, x_1657);
return x_1755;
}
else
{
obj* x_1756; obj* x_1757; obj* x_1758; obj* x_1759; obj* x_1760; obj* x_1761; 
x_1756 = lean::cnstr_get(x_1275, 0);
x_1757 = lean::cnstr_get(x_1275, 1);
x_1758 = lean::cnstr_get(x_1275, 2);
x_1759 = lean::cnstr_get(x_1275, 3);
lean::inc(x_1759);
lean::inc(x_1758);
lean::inc(x_1757);
lean::inc(x_1756);
lean::dec(x_1275);
x_1760 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1760, 0, x_1742);
lean::cnstr_set(x_1760, 1, x_1743);
lean::cnstr_set(x_1760, 2, x_1744);
lean::cnstr_set(x_1760, 3, x_1745);
lean::cnstr_set_uint8(x_1760, sizeof(void*)*4, x_1657);
lean::cnstr_set(x_4, 3, x_1265);
lean::cnstr_set(x_4, 2, x_1737);
lean::cnstr_set(x_4, 1, x_1736);
lean::cnstr_set(x_4, 0, x_1760);
lean::cnstr_set(x_234, 3, x_1759);
lean::cnstr_set(x_234, 2, x_1758);
lean::cnstr_set(x_234, 1, x_1757);
lean::cnstr_set(x_234, 0, x_1756);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1657);
lean::cnstr_set(x_1, 3, x_1616);
lean::cnstr_set(x_1, 2, x_1747);
lean::cnstr_set(x_1, 1, x_1746);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1274);
x_1761 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1761, 0, x_4);
lean::cnstr_set(x_1761, 1, x_2);
lean::cnstr_set(x_1761, 2, x_3);
lean::cnstr_set(x_1761, 3, x_1);
lean::cnstr_set_uint8(x_1761, sizeof(void*)*4, x_1657);
return x_1761;
}
}
else
{
obj* x_1762; obj* x_1763; obj* x_1764; obj* x_1765; obj* x_1766; obj* x_1767; obj* x_1768; obj* x_1769; obj* x_1770; obj* x_1771; obj* x_1772; obj* x_1773; obj* x_1774; obj* x_1775; 
x_1762 = lean::cnstr_get(x_234, 0);
x_1763 = lean::cnstr_get(x_234, 1);
x_1764 = lean::cnstr_get(x_234, 2);
x_1765 = lean::cnstr_get(x_234, 3);
x_1766 = lean::cnstr_get(x_4, 1);
x_1767 = lean::cnstr_get(x_4, 2);
lean::inc(x_1767);
lean::inc(x_1766);
lean::dec(x_4);
x_1768 = lean::cnstr_get(x_1275, 0);
lean::inc(x_1768);
x_1769 = lean::cnstr_get(x_1275, 1);
lean::inc(x_1769);
x_1770 = lean::cnstr_get(x_1275, 2);
lean::inc(x_1770);
x_1771 = lean::cnstr_get(x_1275, 3);
lean::inc(x_1771);
if (lean::is_exclusive(x_1275)) {
 lean::cnstr_release(x_1275, 0);
 lean::cnstr_release(x_1275, 1);
 lean::cnstr_release(x_1275, 2);
 lean::cnstr_release(x_1275, 3);
 x_1772 = x_1275;
} else {
 lean::dec_ref(x_1275);
 x_1772 = lean::box(0);
}
if (lean::is_scalar(x_1772)) {
 x_1773 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1773 = x_1772;
}
lean::cnstr_set(x_1773, 0, x_1762);
lean::cnstr_set(x_1773, 1, x_1763);
lean::cnstr_set(x_1773, 2, x_1764);
lean::cnstr_set(x_1773, 3, x_1765);
lean::cnstr_set_uint8(x_1773, sizeof(void*)*4, x_1657);
x_1774 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1774, 0, x_1773);
lean::cnstr_set(x_1774, 1, x_1736);
lean::cnstr_set(x_1774, 2, x_1737);
lean::cnstr_set(x_1774, 3, x_1265);
lean::cnstr_set_uint8(x_1774, sizeof(void*)*4, x_1274);
lean::cnstr_set(x_234, 3, x_1771);
lean::cnstr_set(x_234, 2, x_1770);
lean::cnstr_set(x_234, 1, x_1769);
lean::cnstr_set(x_234, 0, x_1768);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1657);
lean::cnstr_set(x_1, 3, x_1616);
lean::cnstr_set(x_1, 2, x_1767);
lean::cnstr_set(x_1, 1, x_1766);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1274);
x_1775 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1775, 0, x_1774);
lean::cnstr_set(x_1775, 1, x_2);
lean::cnstr_set(x_1775, 2, x_3);
lean::cnstr_set(x_1775, 3, x_1);
lean::cnstr_set_uint8(x_1775, sizeof(void*)*4, x_1657);
return x_1775;
}
}
else
{
obj* x_1776; obj* x_1777; obj* x_1778; obj* x_1779; obj* x_1780; obj* x_1781; obj* x_1782; obj* x_1783; obj* x_1784; obj* x_1785; obj* x_1786; obj* x_1787; obj* x_1788; obj* x_1789; obj* x_1790; obj* x_1791; 
x_1776 = lean::cnstr_get(x_234, 0);
x_1777 = lean::cnstr_get(x_234, 1);
x_1778 = lean::cnstr_get(x_234, 2);
x_1779 = lean::cnstr_get(x_234, 3);
lean::inc(x_1779);
lean::inc(x_1778);
lean::inc(x_1777);
lean::inc(x_1776);
lean::dec(x_234);
x_1780 = lean::cnstr_get(x_4, 1);
lean::inc(x_1780);
x_1781 = lean::cnstr_get(x_4, 2);
lean::inc(x_1781);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1782 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1782 = lean::box(0);
}
x_1783 = lean::cnstr_get(x_1275, 0);
lean::inc(x_1783);
x_1784 = lean::cnstr_get(x_1275, 1);
lean::inc(x_1784);
x_1785 = lean::cnstr_get(x_1275, 2);
lean::inc(x_1785);
x_1786 = lean::cnstr_get(x_1275, 3);
lean::inc(x_1786);
if (lean::is_exclusive(x_1275)) {
 lean::cnstr_release(x_1275, 0);
 lean::cnstr_release(x_1275, 1);
 lean::cnstr_release(x_1275, 2);
 lean::cnstr_release(x_1275, 3);
 x_1787 = x_1275;
} else {
 lean::dec_ref(x_1275);
 x_1787 = lean::box(0);
}
if (lean::is_scalar(x_1787)) {
 x_1788 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1788 = x_1787;
}
lean::cnstr_set(x_1788, 0, x_1776);
lean::cnstr_set(x_1788, 1, x_1777);
lean::cnstr_set(x_1788, 2, x_1778);
lean::cnstr_set(x_1788, 3, x_1779);
lean::cnstr_set_uint8(x_1788, sizeof(void*)*4, x_1657);
if (lean::is_scalar(x_1782)) {
 x_1789 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1789 = x_1782;
}
lean::cnstr_set(x_1789, 0, x_1788);
lean::cnstr_set(x_1789, 1, x_1736);
lean::cnstr_set(x_1789, 2, x_1737);
lean::cnstr_set(x_1789, 3, x_1265);
lean::cnstr_set_uint8(x_1789, sizeof(void*)*4, x_1274);
x_1790 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1790, 0, x_1783);
lean::cnstr_set(x_1790, 1, x_1784);
lean::cnstr_set(x_1790, 2, x_1785);
lean::cnstr_set(x_1790, 3, x_1786);
lean::cnstr_set_uint8(x_1790, sizeof(void*)*4, x_1657);
lean::cnstr_set(x_1, 3, x_1616);
lean::cnstr_set(x_1, 2, x_1781);
lean::cnstr_set(x_1, 1, x_1780);
lean::cnstr_set(x_1, 0, x_1790);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1274);
x_1791 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1791, 0, x_1789);
lean::cnstr_set(x_1791, 1, x_2);
lean::cnstr_set(x_1791, 2, x_3);
lean::cnstr_set(x_1791, 3, x_1);
lean::cnstr_set_uint8(x_1791, sizeof(void*)*4, x_1657);
return x_1791;
}
}
else
{
obj* x_1792; obj* x_1793; obj* x_1794; obj* x_1795; obj* x_1796; obj* x_1797; obj* x_1798; obj* x_1799; obj* x_1800; obj* x_1801; obj* x_1802; obj* x_1803; obj* x_1804; obj* x_1805; obj* x_1806; obj* x_1807; obj* x_1808; obj* x_1809; obj* x_1810; obj* x_1811; 
x_1792 = lean::cnstr_get(x_1, 1);
x_1793 = lean::cnstr_get(x_1, 2);
lean::inc(x_1793);
lean::inc(x_1792);
lean::dec(x_1);
x_1794 = lean::cnstr_get(x_234, 0);
lean::inc(x_1794);
x_1795 = lean::cnstr_get(x_234, 1);
lean::inc(x_1795);
x_1796 = lean::cnstr_get(x_234, 2);
lean::inc(x_1796);
x_1797 = lean::cnstr_get(x_234, 3);
lean::inc(x_1797);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1798 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1798 = lean::box(0);
}
x_1799 = lean::cnstr_get(x_4, 1);
lean::inc(x_1799);
x_1800 = lean::cnstr_get(x_4, 2);
lean::inc(x_1800);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1801 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1801 = lean::box(0);
}
x_1802 = lean::cnstr_get(x_1275, 0);
lean::inc(x_1802);
x_1803 = lean::cnstr_get(x_1275, 1);
lean::inc(x_1803);
x_1804 = lean::cnstr_get(x_1275, 2);
lean::inc(x_1804);
x_1805 = lean::cnstr_get(x_1275, 3);
lean::inc(x_1805);
if (lean::is_exclusive(x_1275)) {
 lean::cnstr_release(x_1275, 0);
 lean::cnstr_release(x_1275, 1);
 lean::cnstr_release(x_1275, 2);
 lean::cnstr_release(x_1275, 3);
 x_1806 = x_1275;
} else {
 lean::dec_ref(x_1275);
 x_1806 = lean::box(0);
}
if (lean::is_scalar(x_1806)) {
 x_1807 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1807 = x_1806;
}
lean::cnstr_set(x_1807, 0, x_1794);
lean::cnstr_set(x_1807, 1, x_1795);
lean::cnstr_set(x_1807, 2, x_1796);
lean::cnstr_set(x_1807, 3, x_1797);
lean::cnstr_set_uint8(x_1807, sizeof(void*)*4, x_1657);
if (lean::is_scalar(x_1801)) {
 x_1808 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1808 = x_1801;
}
lean::cnstr_set(x_1808, 0, x_1807);
lean::cnstr_set(x_1808, 1, x_1792);
lean::cnstr_set(x_1808, 2, x_1793);
lean::cnstr_set(x_1808, 3, x_1265);
lean::cnstr_set_uint8(x_1808, sizeof(void*)*4, x_1274);
if (lean::is_scalar(x_1798)) {
 x_1809 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1809 = x_1798;
}
lean::cnstr_set(x_1809, 0, x_1802);
lean::cnstr_set(x_1809, 1, x_1803);
lean::cnstr_set(x_1809, 2, x_1804);
lean::cnstr_set(x_1809, 3, x_1805);
lean::cnstr_set_uint8(x_1809, sizeof(void*)*4, x_1657);
x_1810 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1810, 0, x_1809);
lean::cnstr_set(x_1810, 1, x_1799);
lean::cnstr_set(x_1810, 2, x_1800);
lean::cnstr_set(x_1810, 3, x_1616);
lean::cnstr_set_uint8(x_1810, sizeof(void*)*4, x_1274);
x_1811 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1811, 0, x_1808);
lean::cnstr_set(x_1811, 1, x_2);
lean::cnstr_set(x_1811, 2, x_3);
lean::cnstr_set(x_1811, 3, x_1810);
lean::cnstr_set_uint8(x_1811, sizeof(void*)*4, x_1657);
return x_1811;
}
}
}
}
}
}
else
{
uint8 x_1812; 
x_1812 = !lean::is_exclusive(x_1);
if (x_1812 == 0)
{
obj* x_1813; obj* x_1814; uint8 x_1815; 
x_1813 = lean::cnstr_get(x_1, 3);
lean::dec(x_1813);
x_1814 = lean::cnstr_get(x_1, 0);
lean::dec(x_1814);
x_1815 = !lean::is_exclusive(x_234);
if (x_1815 == 0)
{
obj* x_1816; 
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1274);
x_1816 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1816, 0, x_1);
lean::cnstr_set(x_1816, 1, x_2);
lean::cnstr_set(x_1816, 2, x_3);
lean::cnstr_set(x_1816, 3, x_4);
lean::cnstr_set_uint8(x_1816, sizeof(void*)*4, x_1274);
return x_1816;
}
else
{
obj* x_1817; obj* x_1818; obj* x_1819; obj* x_1820; obj* x_1821; obj* x_1822; 
x_1817 = lean::cnstr_get(x_234, 0);
x_1818 = lean::cnstr_get(x_234, 1);
x_1819 = lean::cnstr_get(x_234, 2);
x_1820 = lean::cnstr_get(x_234, 3);
lean::inc(x_1820);
lean::inc(x_1819);
lean::inc(x_1818);
lean::inc(x_1817);
lean::dec(x_234);
x_1821 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1821, 0, x_1817);
lean::cnstr_set(x_1821, 1, x_1818);
lean::cnstr_set(x_1821, 2, x_1819);
lean::cnstr_set(x_1821, 3, x_1820);
lean::cnstr_set_uint8(x_1821, sizeof(void*)*4, x_1274);
lean::cnstr_set(x_1, 0, x_1821);
x_1822 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1822, 0, x_1);
lean::cnstr_set(x_1822, 1, x_2);
lean::cnstr_set(x_1822, 2, x_3);
lean::cnstr_set(x_1822, 3, x_4);
lean::cnstr_set_uint8(x_1822, sizeof(void*)*4, x_1274);
return x_1822;
}
}
else
{
obj* x_1823; obj* x_1824; obj* x_1825; obj* x_1826; obj* x_1827; obj* x_1828; obj* x_1829; obj* x_1830; obj* x_1831; obj* x_1832; 
x_1823 = lean::cnstr_get(x_1, 1);
x_1824 = lean::cnstr_get(x_1, 2);
lean::inc(x_1824);
lean::inc(x_1823);
lean::dec(x_1);
x_1825 = lean::cnstr_get(x_234, 0);
lean::inc(x_1825);
x_1826 = lean::cnstr_get(x_234, 1);
lean::inc(x_1826);
x_1827 = lean::cnstr_get(x_234, 2);
lean::inc(x_1827);
x_1828 = lean::cnstr_get(x_234, 3);
lean::inc(x_1828);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1829 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1829 = lean::box(0);
}
if (lean::is_scalar(x_1829)) {
 x_1830 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1830 = x_1829;
}
lean::cnstr_set(x_1830, 0, x_1825);
lean::cnstr_set(x_1830, 1, x_1826);
lean::cnstr_set(x_1830, 2, x_1827);
lean::cnstr_set(x_1830, 3, x_1828);
lean::cnstr_set_uint8(x_1830, sizeof(void*)*4, x_1274);
x_1831 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1831, 0, x_1830);
lean::cnstr_set(x_1831, 1, x_1823);
lean::cnstr_set(x_1831, 2, x_1824);
lean::cnstr_set(x_1831, 3, x_1265);
lean::cnstr_set_uint8(x_1831, sizeof(void*)*4, x_233);
x_1832 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1832, 0, x_1831);
lean::cnstr_set(x_1832, 1, x_2);
lean::cnstr_set(x_1832, 2, x_3);
lean::cnstr_set(x_1832, 3, x_4);
lean::cnstr_set_uint8(x_1832, sizeof(void*)*4, x_1274);
return x_1832;
}
}
}
}
else
{
uint8 x_1833; 
x_1833 = lean::cnstr_get_uint8(x_1265, sizeof(void*)*4);
if (x_1833 == 0)
{
uint8 x_1834; 
x_1834 = !lean::is_exclusive(x_1);
if (x_1834 == 0)
{
obj* x_1835; obj* x_1836; obj* x_1837; obj* x_1838; uint8 x_1839; 
x_1835 = lean::cnstr_get(x_1, 1);
x_1836 = lean::cnstr_get(x_1, 2);
x_1837 = lean::cnstr_get(x_1, 3);
lean::dec(x_1837);
x_1838 = lean::cnstr_get(x_1, 0);
lean::dec(x_1838);
x_1839 = !lean::is_exclusive(x_1265);
if (x_1839 == 0)
{
obj* x_1840; obj* x_1841; obj* x_1842; obj* x_1843; uint8 x_1844; 
x_1840 = lean::cnstr_get(x_1265, 0);
x_1841 = lean::cnstr_get(x_1265, 1);
x_1842 = lean::cnstr_get(x_1265, 2);
x_1843 = lean::cnstr_get(x_1265, 3);
lean::inc(x_234);
lean::cnstr_set(x_1265, 3, x_1840);
lean::cnstr_set(x_1265, 2, x_1836);
lean::cnstr_set(x_1265, 1, x_1835);
lean::cnstr_set(x_1265, 0, x_234);
x_1844 = !lean::is_exclusive(x_234);
if (x_1844 == 0)
{
obj* x_1845; obj* x_1846; obj* x_1847; obj* x_1848; 
x_1845 = lean::cnstr_get(x_234, 3);
lean::dec(x_1845);
x_1846 = lean::cnstr_get(x_234, 2);
lean::dec(x_1846);
x_1847 = lean::cnstr_get(x_234, 1);
lean::dec(x_1847);
x_1848 = lean::cnstr_get(x_234, 0);
lean::dec(x_1848);
lean::cnstr_set_uint8(x_1265, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_234, 3, x_4);
lean::cnstr_set(x_234, 2, x_3);
lean::cnstr_set(x_234, 1, x_2);
lean::cnstr_set(x_234, 0, x_1843);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_1842);
lean::cnstr_set(x_1, 1, x_1841);
lean::cnstr_set(x_1, 0, x_1265);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1833);
return x_1;
}
else
{
obj* x_1849; 
lean::dec(x_234);
lean::cnstr_set_uint8(x_1265, sizeof(void*)*4, x_1237);
x_1849 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1849, 0, x_1843);
lean::cnstr_set(x_1849, 1, x_2);
lean::cnstr_set(x_1849, 2, x_3);
lean::cnstr_set(x_1849, 3, x_4);
lean::cnstr_set_uint8(x_1849, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_1, 3, x_1849);
lean::cnstr_set(x_1, 2, x_1842);
lean::cnstr_set(x_1, 1, x_1841);
lean::cnstr_set(x_1, 0, x_1265);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1833);
return x_1;
}
}
else
{
obj* x_1850; obj* x_1851; obj* x_1852; obj* x_1853; obj* x_1854; obj* x_1855; obj* x_1856; 
x_1850 = lean::cnstr_get(x_1265, 0);
x_1851 = lean::cnstr_get(x_1265, 1);
x_1852 = lean::cnstr_get(x_1265, 2);
x_1853 = lean::cnstr_get(x_1265, 3);
lean::inc(x_1853);
lean::inc(x_1852);
lean::inc(x_1851);
lean::inc(x_1850);
lean::dec(x_1265);
lean::inc(x_234);
x_1854 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1854, 0, x_234);
lean::cnstr_set(x_1854, 1, x_1835);
lean::cnstr_set(x_1854, 2, x_1836);
lean::cnstr_set(x_1854, 3, x_1850);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1855 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1855 = lean::box(0);
}
lean::cnstr_set_uint8(x_1854, sizeof(void*)*4, x_1237);
if (lean::is_scalar(x_1855)) {
 x_1856 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1856 = x_1855;
}
lean::cnstr_set(x_1856, 0, x_1853);
lean::cnstr_set(x_1856, 1, x_2);
lean::cnstr_set(x_1856, 2, x_3);
lean::cnstr_set(x_1856, 3, x_4);
lean::cnstr_set_uint8(x_1856, sizeof(void*)*4, x_1237);
lean::cnstr_set(x_1, 3, x_1856);
lean::cnstr_set(x_1, 2, x_1852);
lean::cnstr_set(x_1, 1, x_1851);
lean::cnstr_set(x_1, 0, x_1854);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1833);
return x_1;
}
}
else
{
obj* x_1857; obj* x_1858; obj* x_1859; obj* x_1860; obj* x_1861; obj* x_1862; obj* x_1863; obj* x_1864; obj* x_1865; obj* x_1866; obj* x_1867; 
x_1857 = lean::cnstr_get(x_1, 1);
x_1858 = lean::cnstr_get(x_1, 2);
lean::inc(x_1858);
lean::inc(x_1857);
lean::dec(x_1);
x_1859 = lean::cnstr_get(x_1265, 0);
lean::inc(x_1859);
x_1860 = lean::cnstr_get(x_1265, 1);
lean::inc(x_1860);
x_1861 = lean::cnstr_get(x_1265, 2);
lean::inc(x_1861);
x_1862 = lean::cnstr_get(x_1265, 3);
lean::inc(x_1862);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_1863 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_1863 = lean::box(0);
}
lean::inc(x_234);
if (lean::is_scalar(x_1863)) {
 x_1864 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1864 = x_1863;
}
lean::cnstr_set(x_1864, 0, x_234);
lean::cnstr_set(x_1864, 1, x_1857);
lean::cnstr_set(x_1864, 2, x_1858);
lean::cnstr_set(x_1864, 3, x_1859);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1865 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1865 = lean::box(0);
}
lean::cnstr_set_uint8(x_1864, sizeof(void*)*4, x_1237);
if (lean::is_scalar(x_1865)) {
 x_1866 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1866 = x_1865;
}
lean::cnstr_set(x_1866, 0, x_1862);
lean::cnstr_set(x_1866, 1, x_2);
lean::cnstr_set(x_1866, 2, x_3);
lean::cnstr_set(x_1866, 3, x_4);
lean::cnstr_set_uint8(x_1866, sizeof(void*)*4, x_1237);
x_1867 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1867, 0, x_1864);
lean::cnstr_set(x_1867, 1, x_1860);
lean::cnstr_set(x_1867, 2, x_1861);
lean::cnstr_set(x_1867, 3, x_1866);
lean::cnstr_set_uint8(x_1867, sizeof(void*)*4, x_1833);
return x_1867;
}
}
else
{
if (lean::obj_tag(x_4) == 0)
{
uint8 x_1868; 
x_1868 = !lean::is_exclusive(x_1);
if (x_1868 == 0)
{
obj* x_1869; obj* x_1870; uint8 x_1871; 
x_1869 = lean::cnstr_get(x_1, 3);
lean::dec(x_1869);
x_1870 = lean::cnstr_get(x_1, 0);
lean::dec(x_1870);
x_1871 = !lean::is_exclusive(x_234);
if (x_1871 == 0)
{
obj* x_1872; 
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1833);
x_1872 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1872, 0, x_1);
lean::cnstr_set(x_1872, 1, x_2);
lean::cnstr_set(x_1872, 2, x_3);
lean::cnstr_set(x_1872, 3, x_4);
lean::cnstr_set_uint8(x_1872, sizeof(void*)*4, x_1833);
return x_1872;
}
else
{
obj* x_1873; obj* x_1874; obj* x_1875; obj* x_1876; obj* x_1877; obj* x_1878; 
x_1873 = lean::cnstr_get(x_234, 0);
x_1874 = lean::cnstr_get(x_234, 1);
x_1875 = lean::cnstr_get(x_234, 2);
x_1876 = lean::cnstr_get(x_234, 3);
lean::inc(x_1876);
lean::inc(x_1875);
lean::inc(x_1874);
lean::inc(x_1873);
lean::dec(x_234);
x_1877 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1877, 0, x_1873);
lean::cnstr_set(x_1877, 1, x_1874);
lean::cnstr_set(x_1877, 2, x_1875);
lean::cnstr_set(x_1877, 3, x_1876);
lean::cnstr_set_uint8(x_1877, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 0, x_1877);
x_1878 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1878, 0, x_1);
lean::cnstr_set(x_1878, 1, x_2);
lean::cnstr_set(x_1878, 2, x_3);
lean::cnstr_set(x_1878, 3, x_4);
lean::cnstr_set_uint8(x_1878, sizeof(void*)*4, x_1833);
return x_1878;
}
}
else
{
obj* x_1879; obj* x_1880; obj* x_1881; obj* x_1882; obj* x_1883; obj* x_1884; obj* x_1885; obj* x_1886; obj* x_1887; obj* x_1888; 
x_1879 = lean::cnstr_get(x_1, 1);
x_1880 = lean::cnstr_get(x_1, 2);
lean::inc(x_1880);
lean::inc(x_1879);
lean::dec(x_1);
x_1881 = lean::cnstr_get(x_234, 0);
lean::inc(x_1881);
x_1882 = lean::cnstr_get(x_234, 1);
lean::inc(x_1882);
x_1883 = lean::cnstr_get(x_234, 2);
lean::inc(x_1883);
x_1884 = lean::cnstr_get(x_234, 3);
lean::inc(x_1884);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1885 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1885 = lean::box(0);
}
if (lean::is_scalar(x_1885)) {
 x_1886 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1886 = x_1885;
}
lean::cnstr_set(x_1886, 0, x_1881);
lean::cnstr_set(x_1886, 1, x_1882);
lean::cnstr_set(x_1886, 2, x_1883);
lean::cnstr_set(x_1886, 3, x_1884);
lean::cnstr_set_uint8(x_1886, sizeof(void*)*4, x_1833);
x_1887 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1887, 0, x_1886);
lean::cnstr_set(x_1887, 1, x_1879);
lean::cnstr_set(x_1887, 2, x_1880);
lean::cnstr_set(x_1887, 3, x_1265);
lean::cnstr_set_uint8(x_1887, sizeof(void*)*4, x_233);
x_1888 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1888, 0, x_1887);
lean::cnstr_set(x_1888, 1, x_2);
lean::cnstr_set(x_1888, 2, x_3);
lean::cnstr_set(x_1888, 3, x_4);
lean::cnstr_set_uint8(x_1888, sizeof(void*)*4, x_1833);
return x_1888;
}
}
else
{
uint8 x_1889; 
x_1889 = lean::cnstr_get_uint8(x_4, sizeof(void*)*4);
if (x_1889 == 0)
{
obj* x_1890; 
x_1890 = lean::cnstr_get(x_4, 0);
lean::inc(x_1890);
if (lean::obj_tag(x_1890) == 0)
{
obj* x_1891; 
x_1891 = lean::cnstr_get(x_4, 3);
lean::inc(x_1891);
if (lean::obj_tag(x_1891) == 0)
{
uint8 x_1892; 
x_1892 = !lean::is_exclusive(x_1);
if (x_1892 == 0)
{
obj* x_1893; obj* x_1894; obj* x_1895; obj* x_1896; uint8 x_1897; 
x_1893 = lean::cnstr_get(x_1, 1);
x_1894 = lean::cnstr_get(x_1, 2);
x_1895 = lean::cnstr_get(x_1, 3);
lean::dec(x_1895);
x_1896 = lean::cnstr_get(x_1, 0);
lean::dec(x_1896);
x_1897 = !lean::is_exclusive(x_234);
if (x_1897 == 0)
{
uint8 x_1898; 
x_1898 = !lean::is_exclusive(x_4);
if (x_1898 == 0)
{
obj* x_1899; obj* x_1900; obj* x_1901; obj* x_1902; obj* x_1903; obj* x_1904; obj* x_1905; obj* x_1906; obj* x_1907; 
x_1899 = lean::cnstr_get(x_234, 0);
x_1900 = lean::cnstr_get(x_234, 1);
x_1901 = lean::cnstr_get(x_234, 2);
x_1902 = lean::cnstr_get(x_234, 3);
x_1903 = lean::cnstr_get(x_4, 1);
x_1904 = lean::cnstr_get(x_4, 2);
x_1905 = lean::cnstr_get(x_4, 3);
lean::dec(x_1905);
x_1906 = lean::cnstr_get(x_4, 0);
lean::dec(x_1906);
lean::cnstr_set(x_4, 3, x_1902);
lean::cnstr_set(x_4, 2, x_1901);
lean::cnstr_set(x_4, 1, x_1900);
lean::cnstr_set(x_4, 0, x_1899);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_234, 3, x_1265);
lean::cnstr_set(x_234, 2, x_1894);
lean::cnstr_set(x_234, 1, x_1893);
lean::cnstr_set(x_234, 0, x_4);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_1, 3, x_1891);
lean::cnstr_set(x_1, 2, x_1904);
lean::cnstr_set(x_1, 1, x_1903);
lean::cnstr_set(x_1, 0, x_1891);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_1907 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1907, 0, x_234);
lean::cnstr_set(x_1907, 1, x_2);
lean::cnstr_set(x_1907, 2, x_3);
lean::cnstr_set(x_1907, 3, x_1);
lean::cnstr_set_uint8(x_1907, sizeof(void*)*4, x_1833);
return x_1907;
}
else
{
obj* x_1908; obj* x_1909; obj* x_1910; obj* x_1911; obj* x_1912; obj* x_1913; obj* x_1914; obj* x_1915; 
x_1908 = lean::cnstr_get(x_234, 0);
x_1909 = lean::cnstr_get(x_234, 1);
x_1910 = lean::cnstr_get(x_234, 2);
x_1911 = lean::cnstr_get(x_234, 3);
x_1912 = lean::cnstr_get(x_4, 1);
x_1913 = lean::cnstr_get(x_4, 2);
lean::inc(x_1913);
lean::inc(x_1912);
lean::dec(x_4);
x_1914 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1914, 0, x_1908);
lean::cnstr_set(x_1914, 1, x_1909);
lean::cnstr_set(x_1914, 2, x_1910);
lean::cnstr_set(x_1914, 3, x_1911);
lean::cnstr_set_uint8(x_1914, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_234, 3, x_1265);
lean::cnstr_set(x_234, 2, x_1894);
lean::cnstr_set(x_234, 1, x_1893);
lean::cnstr_set(x_234, 0, x_1914);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_1, 3, x_1891);
lean::cnstr_set(x_1, 2, x_1913);
lean::cnstr_set(x_1, 1, x_1912);
lean::cnstr_set(x_1, 0, x_1891);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_1915 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1915, 0, x_234);
lean::cnstr_set(x_1915, 1, x_2);
lean::cnstr_set(x_1915, 2, x_3);
lean::cnstr_set(x_1915, 3, x_1);
lean::cnstr_set_uint8(x_1915, sizeof(void*)*4, x_1833);
return x_1915;
}
}
else
{
obj* x_1916; obj* x_1917; obj* x_1918; obj* x_1919; obj* x_1920; obj* x_1921; obj* x_1922; obj* x_1923; obj* x_1924; obj* x_1925; 
x_1916 = lean::cnstr_get(x_234, 0);
x_1917 = lean::cnstr_get(x_234, 1);
x_1918 = lean::cnstr_get(x_234, 2);
x_1919 = lean::cnstr_get(x_234, 3);
lean::inc(x_1919);
lean::inc(x_1918);
lean::inc(x_1917);
lean::inc(x_1916);
lean::dec(x_234);
x_1920 = lean::cnstr_get(x_4, 1);
lean::inc(x_1920);
x_1921 = lean::cnstr_get(x_4, 2);
lean::inc(x_1921);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1922 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1922 = lean::box(0);
}
if (lean::is_scalar(x_1922)) {
 x_1923 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1923 = x_1922;
}
lean::cnstr_set(x_1923, 0, x_1916);
lean::cnstr_set(x_1923, 1, x_1917);
lean::cnstr_set(x_1923, 2, x_1918);
lean::cnstr_set(x_1923, 3, x_1919);
lean::cnstr_set_uint8(x_1923, sizeof(void*)*4, x_1833);
x_1924 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1924, 0, x_1923);
lean::cnstr_set(x_1924, 1, x_1893);
lean::cnstr_set(x_1924, 2, x_1894);
lean::cnstr_set(x_1924, 3, x_1265);
lean::cnstr_set_uint8(x_1924, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_1, 3, x_1891);
lean::cnstr_set(x_1, 2, x_1921);
lean::cnstr_set(x_1, 1, x_1920);
lean::cnstr_set(x_1, 0, x_1891);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_1925 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1925, 0, x_1924);
lean::cnstr_set(x_1925, 1, x_2);
lean::cnstr_set(x_1925, 2, x_3);
lean::cnstr_set(x_1925, 3, x_1);
lean::cnstr_set_uint8(x_1925, sizeof(void*)*4, x_1833);
return x_1925;
}
}
else
{
obj* x_1926; obj* x_1927; obj* x_1928; obj* x_1929; obj* x_1930; obj* x_1931; obj* x_1932; obj* x_1933; obj* x_1934; obj* x_1935; obj* x_1936; obj* x_1937; obj* x_1938; obj* x_1939; 
x_1926 = lean::cnstr_get(x_1, 1);
x_1927 = lean::cnstr_get(x_1, 2);
lean::inc(x_1927);
lean::inc(x_1926);
lean::dec(x_1);
x_1928 = lean::cnstr_get(x_234, 0);
lean::inc(x_1928);
x_1929 = lean::cnstr_get(x_234, 1);
lean::inc(x_1929);
x_1930 = lean::cnstr_get(x_234, 2);
lean::inc(x_1930);
x_1931 = lean::cnstr_get(x_234, 3);
lean::inc(x_1931);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_1932 = x_234;
} else {
 lean::dec_ref(x_234);
 x_1932 = lean::box(0);
}
x_1933 = lean::cnstr_get(x_4, 1);
lean::inc(x_1933);
x_1934 = lean::cnstr_get(x_4, 2);
lean::inc(x_1934);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1935 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1935 = lean::box(0);
}
if (lean::is_scalar(x_1935)) {
 x_1936 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1936 = x_1935;
}
lean::cnstr_set(x_1936, 0, x_1928);
lean::cnstr_set(x_1936, 1, x_1929);
lean::cnstr_set(x_1936, 2, x_1930);
lean::cnstr_set(x_1936, 3, x_1931);
lean::cnstr_set_uint8(x_1936, sizeof(void*)*4, x_1833);
if (lean::is_scalar(x_1932)) {
 x_1937 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1937 = x_1932;
}
lean::cnstr_set(x_1937, 0, x_1936);
lean::cnstr_set(x_1937, 1, x_1926);
lean::cnstr_set(x_1937, 2, x_1927);
lean::cnstr_set(x_1937, 3, x_1265);
lean::cnstr_set_uint8(x_1937, sizeof(void*)*4, x_1889);
x_1938 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1938, 0, x_1891);
lean::cnstr_set(x_1938, 1, x_1933);
lean::cnstr_set(x_1938, 2, x_1934);
lean::cnstr_set(x_1938, 3, x_1891);
lean::cnstr_set_uint8(x_1938, sizeof(void*)*4, x_1889);
x_1939 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1939, 0, x_1937);
lean::cnstr_set(x_1939, 1, x_2);
lean::cnstr_set(x_1939, 2, x_3);
lean::cnstr_set(x_1939, 3, x_1938);
lean::cnstr_set_uint8(x_1939, sizeof(void*)*4, x_1833);
return x_1939;
}
}
else
{
uint8 x_1940; 
x_1940 = lean::cnstr_get_uint8(x_1891, sizeof(void*)*4);
if (x_1940 == 0)
{
uint8 x_1941; 
x_1941 = !lean::is_exclusive(x_1);
if (x_1941 == 0)
{
obj* x_1942; obj* x_1943; obj* x_1944; obj* x_1945; uint8 x_1946; 
x_1942 = lean::cnstr_get(x_1, 1);
x_1943 = lean::cnstr_get(x_1, 2);
x_1944 = lean::cnstr_get(x_1, 3);
lean::dec(x_1944);
x_1945 = lean::cnstr_get(x_1, 0);
lean::dec(x_1945);
x_1946 = !lean::is_exclusive(x_234);
if (x_1946 == 0)
{
uint8 x_1947; 
x_1947 = !lean::is_exclusive(x_4);
if (x_1947 == 0)
{
obj* x_1948; obj* x_1949; obj* x_1950; obj* x_1951; obj* x_1952; obj* x_1953; obj* x_1954; obj* x_1955; uint8 x_1956; 
x_1948 = lean::cnstr_get(x_234, 0);
x_1949 = lean::cnstr_get(x_234, 1);
x_1950 = lean::cnstr_get(x_234, 2);
x_1951 = lean::cnstr_get(x_234, 3);
x_1952 = lean::cnstr_get(x_4, 1);
x_1953 = lean::cnstr_get(x_4, 2);
x_1954 = lean::cnstr_get(x_4, 3);
lean::dec(x_1954);
x_1955 = lean::cnstr_get(x_4, 0);
lean::dec(x_1955);
x_1956 = !lean::is_exclusive(x_1891);
if (x_1956 == 0)
{
obj* x_1957; obj* x_1958; obj* x_1959; obj* x_1960; uint8 x_1961; 
x_1957 = lean::cnstr_get(x_1891, 0);
x_1958 = lean::cnstr_get(x_1891, 1);
x_1959 = lean::cnstr_get(x_1891, 2);
x_1960 = lean::cnstr_get(x_1891, 3);
lean::cnstr_set(x_1891, 3, x_1951);
lean::cnstr_set(x_1891, 2, x_1950);
lean::cnstr_set(x_1891, 1, x_1949);
lean::cnstr_set(x_1891, 0, x_1948);
lean::cnstr_set_uint8(x_1891, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
lean::cnstr_set(x_4, 3, x_1265);
lean::cnstr_set(x_4, 2, x_1943);
lean::cnstr_set(x_4, 1, x_1942);
lean::cnstr_set(x_4, 0, x_1891);
x_1961 = !lean::is_exclusive(x_1265);
if (x_1961 == 0)
{
obj* x_1962; obj* x_1963; obj* x_1964; obj* x_1965; 
x_1962 = lean::cnstr_get(x_1265, 3);
lean::dec(x_1962);
x_1963 = lean::cnstr_get(x_1265, 2);
lean::dec(x_1963);
x_1964 = lean::cnstr_get(x_1265, 1);
lean::dec(x_1964);
x_1965 = lean::cnstr_get(x_1265, 0);
lean::dec(x_1965);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1940);
lean::cnstr_set(x_1265, 3, x_1890);
lean::cnstr_set(x_1265, 2, x_3);
lean::cnstr_set(x_1265, 1, x_2);
lean::cnstr_set(x_1265, 0, x_4);
lean::cnstr_set(x_234, 3, x_1960);
lean::cnstr_set(x_234, 2, x_1959);
lean::cnstr_set(x_234, 1, x_1958);
lean::cnstr_set(x_234, 0, x_1957);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_1953);
lean::cnstr_set(x_1, 1, x_1952);
lean::cnstr_set(x_1, 0, x_1265);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
else
{
obj* x_1966; 
lean::dec(x_1265);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1940);
x_1966 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1966, 0, x_4);
lean::cnstr_set(x_1966, 1, x_2);
lean::cnstr_set(x_1966, 2, x_3);
lean::cnstr_set(x_1966, 3, x_1890);
lean::cnstr_set_uint8(x_1966, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_234, 3, x_1960);
lean::cnstr_set(x_234, 2, x_1959);
lean::cnstr_set(x_234, 1, x_1958);
lean::cnstr_set(x_234, 0, x_1957);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_1953);
lean::cnstr_set(x_1, 1, x_1952);
lean::cnstr_set(x_1, 0, x_1966);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
}
else
{
obj* x_1967; obj* x_1968; obj* x_1969; obj* x_1970; obj* x_1971; obj* x_1972; obj* x_1973; 
x_1967 = lean::cnstr_get(x_1891, 0);
x_1968 = lean::cnstr_get(x_1891, 1);
x_1969 = lean::cnstr_get(x_1891, 2);
x_1970 = lean::cnstr_get(x_1891, 3);
lean::inc(x_1970);
lean::inc(x_1969);
lean::inc(x_1968);
lean::inc(x_1967);
lean::dec(x_1891);
x_1971 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1971, 0, x_1948);
lean::cnstr_set(x_1971, 1, x_1949);
lean::cnstr_set(x_1971, 2, x_1950);
lean::cnstr_set(x_1971, 3, x_1951);
lean::cnstr_set_uint8(x_1971, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
lean::cnstr_set(x_4, 3, x_1265);
lean::cnstr_set(x_4, 2, x_1943);
lean::cnstr_set(x_4, 1, x_1942);
lean::cnstr_set(x_4, 0, x_1971);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_1972 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_1972 = lean::box(0);
}
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_1940);
if (lean::is_scalar(x_1972)) {
 x_1973 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1973 = x_1972;
}
lean::cnstr_set(x_1973, 0, x_4);
lean::cnstr_set(x_1973, 1, x_2);
lean::cnstr_set(x_1973, 2, x_3);
lean::cnstr_set(x_1973, 3, x_1890);
lean::cnstr_set_uint8(x_1973, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_234, 3, x_1970);
lean::cnstr_set(x_234, 2, x_1969);
lean::cnstr_set(x_234, 1, x_1968);
lean::cnstr_set(x_234, 0, x_1967);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_1953);
lean::cnstr_set(x_1, 1, x_1952);
lean::cnstr_set(x_1, 0, x_1973);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
}
else
{
obj* x_1974; obj* x_1975; obj* x_1976; obj* x_1977; obj* x_1978; obj* x_1979; obj* x_1980; obj* x_1981; obj* x_1982; obj* x_1983; obj* x_1984; obj* x_1985; obj* x_1986; obj* x_1987; obj* x_1988; 
x_1974 = lean::cnstr_get(x_234, 0);
x_1975 = lean::cnstr_get(x_234, 1);
x_1976 = lean::cnstr_get(x_234, 2);
x_1977 = lean::cnstr_get(x_234, 3);
x_1978 = lean::cnstr_get(x_4, 1);
x_1979 = lean::cnstr_get(x_4, 2);
lean::inc(x_1979);
lean::inc(x_1978);
lean::dec(x_4);
x_1980 = lean::cnstr_get(x_1891, 0);
lean::inc(x_1980);
x_1981 = lean::cnstr_get(x_1891, 1);
lean::inc(x_1981);
x_1982 = lean::cnstr_get(x_1891, 2);
lean::inc(x_1982);
x_1983 = lean::cnstr_get(x_1891, 3);
lean::inc(x_1983);
if (lean::is_exclusive(x_1891)) {
 lean::cnstr_release(x_1891, 0);
 lean::cnstr_release(x_1891, 1);
 lean::cnstr_release(x_1891, 2);
 lean::cnstr_release(x_1891, 3);
 x_1984 = x_1891;
} else {
 lean::dec_ref(x_1891);
 x_1984 = lean::box(0);
}
if (lean::is_scalar(x_1984)) {
 x_1985 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1985 = x_1984;
}
lean::cnstr_set(x_1985, 0, x_1974);
lean::cnstr_set(x_1985, 1, x_1975);
lean::cnstr_set(x_1985, 2, x_1976);
lean::cnstr_set(x_1985, 3, x_1977);
lean::cnstr_set_uint8(x_1985, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
x_1986 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1986, 0, x_1985);
lean::cnstr_set(x_1986, 1, x_1942);
lean::cnstr_set(x_1986, 2, x_1943);
lean::cnstr_set(x_1986, 3, x_1265);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_1987 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_1987 = lean::box(0);
}
lean::cnstr_set_uint8(x_1986, sizeof(void*)*4, x_1940);
if (lean::is_scalar(x_1987)) {
 x_1988 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1988 = x_1987;
}
lean::cnstr_set(x_1988, 0, x_1986);
lean::cnstr_set(x_1988, 1, x_2);
lean::cnstr_set(x_1988, 2, x_3);
lean::cnstr_set(x_1988, 3, x_1890);
lean::cnstr_set_uint8(x_1988, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_234, 3, x_1983);
lean::cnstr_set(x_234, 2, x_1982);
lean::cnstr_set(x_234, 1, x_1981);
lean::cnstr_set(x_234, 0, x_1980);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_1979);
lean::cnstr_set(x_1, 1, x_1978);
lean::cnstr_set(x_1, 0, x_1988);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
}
else
{
obj* x_1989; obj* x_1990; obj* x_1991; obj* x_1992; obj* x_1993; obj* x_1994; obj* x_1995; obj* x_1996; obj* x_1997; obj* x_1998; obj* x_1999; obj* x_2000; obj* x_2001; obj* x_2002; obj* x_2003; obj* x_2004; obj* x_2005; 
x_1989 = lean::cnstr_get(x_234, 0);
x_1990 = lean::cnstr_get(x_234, 1);
x_1991 = lean::cnstr_get(x_234, 2);
x_1992 = lean::cnstr_get(x_234, 3);
lean::inc(x_1992);
lean::inc(x_1991);
lean::inc(x_1990);
lean::inc(x_1989);
lean::dec(x_234);
x_1993 = lean::cnstr_get(x_4, 1);
lean::inc(x_1993);
x_1994 = lean::cnstr_get(x_4, 2);
lean::inc(x_1994);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_1995 = x_4;
} else {
 lean::dec_ref(x_4);
 x_1995 = lean::box(0);
}
x_1996 = lean::cnstr_get(x_1891, 0);
lean::inc(x_1996);
x_1997 = lean::cnstr_get(x_1891, 1);
lean::inc(x_1997);
x_1998 = lean::cnstr_get(x_1891, 2);
lean::inc(x_1998);
x_1999 = lean::cnstr_get(x_1891, 3);
lean::inc(x_1999);
if (lean::is_exclusive(x_1891)) {
 lean::cnstr_release(x_1891, 0);
 lean::cnstr_release(x_1891, 1);
 lean::cnstr_release(x_1891, 2);
 lean::cnstr_release(x_1891, 3);
 x_2000 = x_1891;
} else {
 lean::dec_ref(x_1891);
 x_2000 = lean::box(0);
}
if (lean::is_scalar(x_2000)) {
 x_2001 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2001 = x_2000;
}
lean::cnstr_set(x_2001, 0, x_1989);
lean::cnstr_set(x_2001, 1, x_1990);
lean::cnstr_set(x_2001, 2, x_1991);
lean::cnstr_set(x_2001, 3, x_1992);
lean::cnstr_set_uint8(x_2001, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
if (lean::is_scalar(x_1995)) {
 x_2002 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2002 = x_1995;
}
lean::cnstr_set(x_2002, 0, x_2001);
lean::cnstr_set(x_2002, 1, x_1942);
lean::cnstr_set(x_2002, 2, x_1943);
lean::cnstr_set(x_2002, 3, x_1265);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2003 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2003 = lean::box(0);
}
lean::cnstr_set_uint8(x_2002, sizeof(void*)*4, x_1940);
if (lean::is_scalar(x_2003)) {
 x_2004 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2004 = x_2003;
}
lean::cnstr_set(x_2004, 0, x_2002);
lean::cnstr_set(x_2004, 1, x_2);
lean::cnstr_set(x_2004, 2, x_3);
lean::cnstr_set(x_2004, 3, x_1890);
lean::cnstr_set_uint8(x_2004, sizeof(void*)*4, x_1833);
x_2005 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2005, 0, x_1996);
lean::cnstr_set(x_2005, 1, x_1997);
lean::cnstr_set(x_2005, 2, x_1998);
lean::cnstr_set(x_2005, 3, x_1999);
lean::cnstr_set_uint8(x_2005, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_2005);
lean::cnstr_set(x_1, 2, x_1994);
lean::cnstr_set(x_1, 1, x_1993);
lean::cnstr_set(x_1, 0, x_2004);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
}
else
{
obj* x_2006; obj* x_2007; obj* x_2008; obj* x_2009; obj* x_2010; obj* x_2011; obj* x_2012; obj* x_2013; obj* x_2014; obj* x_2015; obj* x_2016; obj* x_2017; obj* x_2018; obj* x_2019; obj* x_2020; obj* x_2021; obj* x_2022; obj* x_2023; obj* x_2024; obj* x_2025; obj* x_2026; 
x_2006 = lean::cnstr_get(x_1, 1);
x_2007 = lean::cnstr_get(x_1, 2);
lean::inc(x_2007);
lean::inc(x_2006);
lean::dec(x_1);
x_2008 = lean::cnstr_get(x_234, 0);
lean::inc(x_2008);
x_2009 = lean::cnstr_get(x_234, 1);
lean::inc(x_2009);
x_2010 = lean::cnstr_get(x_234, 2);
lean::inc(x_2010);
x_2011 = lean::cnstr_get(x_234, 3);
lean::inc(x_2011);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_2012 = x_234;
} else {
 lean::dec_ref(x_234);
 x_2012 = lean::box(0);
}
x_2013 = lean::cnstr_get(x_4, 1);
lean::inc(x_2013);
x_2014 = lean::cnstr_get(x_4, 2);
lean::inc(x_2014);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_2015 = x_4;
} else {
 lean::dec_ref(x_4);
 x_2015 = lean::box(0);
}
x_2016 = lean::cnstr_get(x_1891, 0);
lean::inc(x_2016);
x_2017 = lean::cnstr_get(x_1891, 1);
lean::inc(x_2017);
x_2018 = lean::cnstr_get(x_1891, 2);
lean::inc(x_2018);
x_2019 = lean::cnstr_get(x_1891, 3);
lean::inc(x_2019);
if (lean::is_exclusive(x_1891)) {
 lean::cnstr_release(x_1891, 0);
 lean::cnstr_release(x_1891, 1);
 lean::cnstr_release(x_1891, 2);
 lean::cnstr_release(x_1891, 3);
 x_2020 = x_1891;
} else {
 lean::dec_ref(x_1891);
 x_2020 = lean::box(0);
}
if (lean::is_scalar(x_2020)) {
 x_2021 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2021 = x_2020;
}
lean::cnstr_set(x_2021, 0, x_2008);
lean::cnstr_set(x_2021, 1, x_2009);
lean::cnstr_set(x_2021, 2, x_2010);
lean::cnstr_set(x_2021, 3, x_2011);
lean::cnstr_set_uint8(x_2021, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
if (lean::is_scalar(x_2015)) {
 x_2022 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2022 = x_2015;
}
lean::cnstr_set(x_2022, 0, x_2021);
lean::cnstr_set(x_2022, 1, x_2006);
lean::cnstr_set(x_2022, 2, x_2007);
lean::cnstr_set(x_2022, 3, x_1265);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2023 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2023 = lean::box(0);
}
lean::cnstr_set_uint8(x_2022, sizeof(void*)*4, x_1940);
if (lean::is_scalar(x_2023)) {
 x_2024 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2024 = x_2023;
}
lean::cnstr_set(x_2024, 0, x_2022);
lean::cnstr_set(x_2024, 1, x_2);
lean::cnstr_set(x_2024, 2, x_3);
lean::cnstr_set(x_2024, 3, x_1890);
lean::cnstr_set_uint8(x_2024, sizeof(void*)*4, x_1833);
if (lean::is_scalar(x_2012)) {
 x_2025 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2025 = x_2012;
}
lean::cnstr_set(x_2025, 0, x_2016);
lean::cnstr_set(x_2025, 1, x_2017);
lean::cnstr_set(x_2025, 2, x_2018);
lean::cnstr_set(x_2025, 3, x_2019);
lean::cnstr_set_uint8(x_2025, sizeof(void*)*4, x_1833);
x_2026 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2026, 0, x_2024);
lean::cnstr_set(x_2026, 1, x_2013);
lean::cnstr_set(x_2026, 2, x_2014);
lean::cnstr_set(x_2026, 3, x_2025);
lean::cnstr_set_uint8(x_2026, sizeof(void*)*4, x_1940);
return x_2026;
}
}
else
{
uint8 x_2027; 
x_2027 = !lean::is_exclusive(x_1891);
if (x_2027 == 0)
{
obj* x_2028; obj* x_2029; obj* x_2030; obj* x_2031; uint8 x_2032; 
x_2028 = lean::cnstr_get(x_1891, 3);
lean::dec(x_2028);
x_2029 = lean::cnstr_get(x_1891, 2);
lean::dec(x_2029);
x_2030 = lean::cnstr_get(x_1891, 1);
lean::dec(x_2030);
x_2031 = lean::cnstr_get(x_1891, 0);
lean::dec(x_2031);
x_2032 = !lean::is_exclusive(x_1);
if (x_2032 == 0)
{
obj* x_2033; obj* x_2034; obj* x_2035; obj* x_2036; uint8 x_2037; 
x_2033 = lean::cnstr_get(x_1, 1);
x_2034 = lean::cnstr_get(x_1, 2);
x_2035 = lean::cnstr_get(x_1, 3);
lean::dec(x_2035);
x_2036 = lean::cnstr_get(x_1, 0);
lean::dec(x_2036);
x_2037 = !lean::is_exclusive(x_234);
if (x_2037 == 0)
{
uint8 x_2038; 
x_2038 = !lean::is_exclusive(x_1265);
if (x_2038 == 0)
{
obj* x_2039; obj* x_2040; obj* x_2041; obj* x_2042; 
x_2039 = lean::cnstr_get(x_234, 0);
x_2040 = lean::cnstr_get(x_234, 1);
x_2041 = lean::cnstr_get(x_234, 2);
x_2042 = lean::cnstr_get(x_234, 3);
lean::cnstr_set(x_1891, 3, x_2042);
lean::cnstr_set(x_1891, 2, x_2041);
lean::cnstr_set(x_1891, 1, x_2040);
lean::cnstr_set(x_1891, 0, x_2039);
lean::cnstr_set_uint8(x_1265, sizeof(void*)*4, x_1940);
lean::cnstr_set(x_234, 3, x_1265);
lean::cnstr_set(x_234, 2, x_2034);
lean::cnstr_set(x_234, 1, x_2033);
lean::cnstr_set(x_234, 0, x_1891);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
else
{
obj* x_2043; obj* x_2044; obj* x_2045; obj* x_2046; obj* x_2047; obj* x_2048; obj* x_2049; obj* x_2050; obj* x_2051; 
x_2043 = lean::cnstr_get(x_234, 0);
x_2044 = lean::cnstr_get(x_234, 1);
x_2045 = lean::cnstr_get(x_234, 2);
x_2046 = lean::cnstr_get(x_234, 3);
x_2047 = lean::cnstr_get(x_1265, 0);
x_2048 = lean::cnstr_get(x_1265, 1);
x_2049 = lean::cnstr_get(x_1265, 2);
x_2050 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2050);
lean::inc(x_2049);
lean::inc(x_2048);
lean::inc(x_2047);
lean::dec(x_1265);
lean::cnstr_set(x_1891, 3, x_2046);
lean::cnstr_set(x_1891, 2, x_2045);
lean::cnstr_set(x_1891, 1, x_2044);
lean::cnstr_set(x_1891, 0, x_2043);
x_2051 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2051, 0, x_2047);
lean::cnstr_set(x_2051, 1, x_2048);
lean::cnstr_set(x_2051, 2, x_2049);
lean::cnstr_set(x_2051, 3, x_2050);
lean::cnstr_set_uint8(x_2051, sizeof(void*)*4, x_1940);
lean::cnstr_set(x_234, 3, x_2051);
lean::cnstr_set(x_234, 2, x_2034);
lean::cnstr_set(x_234, 1, x_2033);
lean::cnstr_set(x_234, 0, x_1891);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
}
else
{
obj* x_2052; obj* x_2053; obj* x_2054; obj* x_2055; obj* x_2056; obj* x_2057; obj* x_2058; obj* x_2059; obj* x_2060; obj* x_2061; obj* x_2062; 
x_2052 = lean::cnstr_get(x_234, 0);
x_2053 = lean::cnstr_get(x_234, 1);
x_2054 = lean::cnstr_get(x_234, 2);
x_2055 = lean::cnstr_get(x_234, 3);
lean::inc(x_2055);
lean::inc(x_2054);
lean::inc(x_2053);
lean::inc(x_2052);
lean::dec(x_234);
x_2056 = lean::cnstr_get(x_1265, 0);
lean::inc(x_2056);
x_2057 = lean::cnstr_get(x_1265, 1);
lean::inc(x_2057);
x_2058 = lean::cnstr_get(x_1265, 2);
lean::inc(x_2058);
x_2059 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2059);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2060 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2060 = lean::box(0);
}
lean::cnstr_set(x_1891, 3, x_2055);
lean::cnstr_set(x_1891, 2, x_2054);
lean::cnstr_set(x_1891, 1, x_2053);
lean::cnstr_set(x_1891, 0, x_2052);
if (lean::is_scalar(x_2060)) {
 x_2061 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2061 = x_2060;
}
lean::cnstr_set(x_2061, 0, x_2056);
lean::cnstr_set(x_2061, 1, x_2057);
lean::cnstr_set(x_2061, 2, x_2058);
lean::cnstr_set(x_2061, 3, x_2059);
lean::cnstr_set_uint8(x_2061, sizeof(void*)*4, x_1940);
x_2062 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2062, 0, x_1891);
lean::cnstr_set(x_2062, 1, x_2033);
lean::cnstr_set(x_2062, 2, x_2034);
lean::cnstr_set(x_2062, 3, x_2061);
lean::cnstr_set_uint8(x_2062, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_2062);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
}
else
{
obj* x_2063; obj* x_2064; obj* x_2065; obj* x_2066; obj* x_2067; obj* x_2068; obj* x_2069; obj* x_2070; obj* x_2071; obj* x_2072; obj* x_2073; obj* x_2074; obj* x_2075; obj* x_2076; obj* x_2077; 
x_2063 = lean::cnstr_get(x_1, 1);
x_2064 = lean::cnstr_get(x_1, 2);
lean::inc(x_2064);
lean::inc(x_2063);
lean::dec(x_1);
x_2065 = lean::cnstr_get(x_234, 0);
lean::inc(x_2065);
x_2066 = lean::cnstr_get(x_234, 1);
lean::inc(x_2066);
x_2067 = lean::cnstr_get(x_234, 2);
lean::inc(x_2067);
x_2068 = lean::cnstr_get(x_234, 3);
lean::inc(x_2068);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_2069 = x_234;
} else {
 lean::dec_ref(x_234);
 x_2069 = lean::box(0);
}
x_2070 = lean::cnstr_get(x_1265, 0);
lean::inc(x_2070);
x_2071 = lean::cnstr_get(x_1265, 1);
lean::inc(x_2071);
x_2072 = lean::cnstr_get(x_1265, 2);
lean::inc(x_2072);
x_2073 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2073);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2074 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2074 = lean::box(0);
}
lean::cnstr_set(x_1891, 3, x_2068);
lean::cnstr_set(x_1891, 2, x_2067);
lean::cnstr_set(x_1891, 1, x_2066);
lean::cnstr_set(x_1891, 0, x_2065);
if (lean::is_scalar(x_2074)) {
 x_2075 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2075 = x_2074;
}
lean::cnstr_set(x_2075, 0, x_2070);
lean::cnstr_set(x_2075, 1, x_2071);
lean::cnstr_set(x_2075, 2, x_2072);
lean::cnstr_set(x_2075, 3, x_2073);
lean::cnstr_set_uint8(x_2075, sizeof(void*)*4, x_1940);
if (lean::is_scalar(x_2069)) {
 x_2076 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2076 = x_2069;
}
lean::cnstr_set(x_2076, 0, x_1891);
lean::cnstr_set(x_2076, 1, x_2063);
lean::cnstr_set(x_2076, 2, x_2064);
lean::cnstr_set(x_2076, 3, x_2075);
lean::cnstr_set_uint8(x_2076, sizeof(void*)*4, x_1889);
x_2077 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2077, 0, x_2076);
lean::cnstr_set(x_2077, 1, x_2);
lean::cnstr_set(x_2077, 2, x_3);
lean::cnstr_set(x_2077, 3, x_4);
lean::cnstr_set_uint8(x_2077, sizeof(void*)*4, x_1940);
return x_2077;
}
}
else
{
obj* x_2078; obj* x_2079; obj* x_2080; obj* x_2081; obj* x_2082; obj* x_2083; obj* x_2084; obj* x_2085; obj* x_2086; obj* x_2087; obj* x_2088; obj* x_2089; obj* x_2090; obj* x_2091; obj* x_2092; obj* x_2093; obj* x_2094; 
lean::dec(x_1891);
x_2078 = lean::cnstr_get(x_1, 1);
lean::inc(x_2078);
x_2079 = lean::cnstr_get(x_1, 2);
lean::inc(x_2079);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_2080 = x_1;
} else {
 lean::dec_ref(x_1);
 x_2080 = lean::box(0);
}
x_2081 = lean::cnstr_get(x_234, 0);
lean::inc(x_2081);
x_2082 = lean::cnstr_get(x_234, 1);
lean::inc(x_2082);
x_2083 = lean::cnstr_get(x_234, 2);
lean::inc(x_2083);
x_2084 = lean::cnstr_get(x_234, 3);
lean::inc(x_2084);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_2085 = x_234;
} else {
 lean::dec_ref(x_234);
 x_2085 = lean::box(0);
}
x_2086 = lean::cnstr_get(x_1265, 0);
lean::inc(x_2086);
x_2087 = lean::cnstr_get(x_1265, 1);
lean::inc(x_2087);
x_2088 = lean::cnstr_get(x_1265, 2);
lean::inc(x_2088);
x_2089 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2089);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2090 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2090 = lean::box(0);
}
x_2091 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2091, 0, x_2081);
lean::cnstr_set(x_2091, 1, x_2082);
lean::cnstr_set(x_2091, 2, x_2083);
lean::cnstr_set(x_2091, 3, x_2084);
lean::cnstr_set_uint8(x_2091, sizeof(void*)*4, x_1940);
if (lean::is_scalar(x_2090)) {
 x_2092 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2092 = x_2090;
}
lean::cnstr_set(x_2092, 0, x_2086);
lean::cnstr_set(x_2092, 1, x_2087);
lean::cnstr_set(x_2092, 2, x_2088);
lean::cnstr_set(x_2092, 3, x_2089);
lean::cnstr_set_uint8(x_2092, sizeof(void*)*4, x_1940);
if (lean::is_scalar(x_2085)) {
 x_2093 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2093 = x_2085;
}
lean::cnstr_set(x_2093, 0, x_2091);
lean::cnstr_set(x_2093, 1, x_2078);
lean::cnstr_set(x_2093, 2, x_2079);
lean::cnstr_set(x_2093, 3, x_2092);
lean::cnstr_set_uint8(x_2093, sizeof(void*)*4, x_1889);
if (lean::is_scalar(x_2080)) {
 x_2094 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2094 = x_2080;
}
lean::cnstr_set(x_2094, 0, x_2093);
lean::cnstr_set(x_2094, 1, x_2);
lean::cnstr_set(x_2094, 2, x_3);
lean::cnstr_set(x_2094, 3, x_4);
lean::cnstr_set_uint8(x_2094, sizeof(void*)*4, x_1940);
return x_2094;
}
}
}
}
else
{
uint8 x_2095; 
x_2095 = lean::cnstr_get_uint8(x_1890, sizeof(void*)*4);
if (x_2095 == 0)
{
obj* x_2096; 
x_2096 = lean::cnstr_get(x_4, 3);
lean::inc(x_2096);
if (lean::obj_tag(x_2096) == 0)
{
uint8 x_2097; 
x_2097 = !lean::is_exclusive(x_1);
if (x_2097 == 0)
{
obj* x_2098; obj* x_2099; obj* x_2100; obj* x_2101; uint8 x_2102; 
x_2098 = lean::cnstr_get(x_1, 1);
x_2099 = lean::cnstr_get(x_1, 2);
x_2100 = lean::cnstr_get(x_1, 3);
lean::dec(x_2100);
x_2101 = lean::cnstr_get(x_1, 0);
lean::dec(x_2101);
x_2102 = !lean::is_exclusive(x_234);
if (x_2102 == 0)
{
uint8 x_2103; 
x_2103 = !lean::is_exclusive(x_4);
if (x_2103 == 0)
{
obj* x_2104; obj* x_2105; obj* x_2106; obj* x_2107; obj* x_2108; obj* x_2109; obj* x_2110; obj* x_2111; uint8 x_2112; 
x_2104 = lean::cnstr_get(x_234, 0);
x_2105 = lean::cnstr_get(x_234, 1);
x_2106 = lean::cnstr_get(x_234, 2);
x_2107 = lean::cnstr_get(x_234, 3);
x_2108 = lean::cnstr_get(x_4, 1);
x_2109 = lean::cnstr_get(x_4, 2);
x_2110 = lean::cnstr_get(x_4, 3);
lean::dec(x_2110);
x_2111 = lean::cnstr_get(x_4, 0);
lean::dec(x_2111);
x_2112 = !lean::is_exclusive(x_1890);
if (x_2112 == 0)
{
obj* x_2113; obj* x_2114; obj* x_2115; obj* x_2116; uint8 x_2117; 
x_2113 = lean::cnstr_get(x_1890, 0);
x_2114 = lean::cnstr_get(x_1890, 1);
x_2115 = lean::cnstr_get(x_1890, 2);
x_2116 = lean::cnstr_get(x_1890, 3);
lean::cnstr_set(x_1890, 3, x_2107);
lean::cnstr_set(x_1890, 2, x_2106);
lean::cnstr_set(x_1890, 1, x_2105);
lean::cnstr_set(x_1890, 0, x_2104);
lean::cnstr_set_uint8(x_1890, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
lean::cnstr_set(x_4, 3, x_1265);
lean::cnstr_set(x_4, 2, x_2099);
lean::cnstr_set(x_4, 1, x_2098);
x_2117 = !lean::is_exclusive(x_1265);
if (x_2117 == 0)
{
obj* x_2118; obj* x_2119; obj* x_2120; obj* x_2121; 
x_2118 = lean::cnstr_get(x_1265, 3);
lean::dec(x_2118);
x_2119 = lean::cnstr_get(x_1265, 2);
lean::dec(x_2119);
x_2120 = lean::cnstr_get(x_1265, 1);
lean::dec(x_2120);
x_2121 = lean::cnstr_get(x_1265, 0);
lean::dec(x_2121);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_1265, 3, x_2113);
lean::cnstr_set(x_1265, 2, x_3);
lean::cnstr_set(x_1265, 1, x_2);
lean::cnstr_set(x_1265, 0, x_4);
lean::cnstr_set(x_234, 3, x_2096);
lean::cnstr_set(x_234, 2, x_2109);
lean::cnstr_set(x_234, 1, x_2108);
lean::cnstr_set(x_234, 0, x_2116);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_2115);
lean::cnstr_set(x_1, 1, x_2114);
lean::cnstr_set(x_1, 0, x_1265);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
else
{
obj* x_2122; 
lean::dec(x_1265);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2095);
x_2122 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2122, 0, x_4);
lean::cnstr_set(x_2122, 1, x_2);
lean::cnstr_set(x_2122, 2, x_3);
lean::cnstr_set(x_2122, 3, x_2113);
lean::cnstr_set_uint8(x_2122, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_234, 3, x_2096);
lean::cnstr_set(x_234, 2, x_2109);
lean::cnstr_set(x_234, 1, x_2108);
lean::cnstr_set(x_234, 0, x_2116);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_2115);
lean::cnstr_set(x_1, 1, x_2114);
lean::cnstr_set(x_1, 0, x_2122);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
}
else
{
obj* x_2123; obj* x_2124; obj* x_2125; obj* x_2126; obj* x_2127; obj* x_2128; obj* x_2129; 
x_2123 = lean::cnstr_get(x_1890, 0);
x_2124 = lean::cnstr_get(x_1890, 1);
x_2125 = lean::cnstr_get(x_1890, 2);
x_2126 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2126);
lean::inc(x_2125);
lean::inc(x_2124);
lean::inc(x_2123);
lean::dec(x_1890);
x_2127 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2127, 0, x_2104);
lean::cnstr_set(x_2127, 1, x_2105);
lean::cnstr_set(x_2127, 2, x_2106);
lean::cnstr_set(x_2127, 3, x_2107);
lean::cnstr_set_uint8(x_2127, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
lean::cnstr_set(x_4, 3, x_1265);
lean::cnstr_set(x_4, 2, x_2099);
lean::cnstr_set(x_4, 1, x_2098);
lean::cnstr_set(x_4, 0, x_2127);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2128 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2128 = lean::box(0);
}
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2095);
if (lean::is_scalar(x_2128)) {
 x_2129 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2129 = x_2128;
}
lean::cnstr_set(x_2129, 0, x_4);
lean::cnstr_set(x_2129, 1, x_2);
lean::cnstr_set(x_2129, 2, x_3);
lean::cnstr_set(x_2129, 3, x_2123);
lean::cnstr_set_uint8(x_2129, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_234, 3, x_2096);
lean::cnstr_set(x_234, 2, x_2109);
lean::cnstr_set(x_234, 1, x_2108);
lean::cnstr_set(x_234, 0, x_2126);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_2125);
lean::cnstr_set(x_1, 1, x_2124);
lean::cnstr_set(x_1, 0, x_2129);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
}
else
{
obj* x_2130; obj* x_2131; obj* x_2132; obj* x_2133; obj* x_2134; obj* x_2135; obj* x_2136; obj* x_2137; obj* x_2138; obj* x_2139; obj* x_2140; obj* x_2141; obj* x_2142; obj* x_2143; obj* x_2144; 
x_2130 = lean::cnstr_get(x_234, 0);
x_2131 = lean::cnstr_get(x_234, 1);
x_2132 = lean::cnstr_get(x_234, 2);
x_2133 = lean::cnstr_get(x_234, 3);
x_2134 = lean::cnstr_get(x_4, 1);
x_2135 = lean::cnstr_get(x_4, 2);
lean::inc(x_2135);
lean::inc(x_2134);
lean::dec(x_4);
x_2136 = lean::cnstr_get(x_1890, 0);
lean::inc(x_2136);
x_2137 = lean::cnstr_get(x_1890, 1);
lean::inc(x_2137);
x_2138 = lean::cnstr_get(x_1890, 2);
lean::inc(x_2138);
x_2139 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2139);
if (lean::is_exclusive(x_1890)) {
 lean::cnstr_release(x_1890, 0);
 lean::cnstr_release(x_1890, 1);
 lean::cnstr_release(x_1890, 2);
 lean::cnstr_release(x_1890, 3);
 x_2140 = x_1890;
} else {
 lean::dec_ref(x_1890);
 x_2140 = lean::box(0);
}
if (lean::is_scalar(x_2140)) {
 x_2141 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2141 = x_2140;
}
lean::cnstr_set(x_2141, 0, x_2130);
lean::cnstr_set(x_2141, 1, x_2131);
lean::cnstr_set(x_2141, 2, x_2132);
lean::cnstr_set(x_2141, 3, x_2133);
lean::cnstr_set_uint8(x_2141, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
x_2142 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2142, 0, x_2141);
lean::cnstr_set(x_2142, 1, x_2098);
lean::cnstr_set(x_2142, 2, x_2099);
lean::cnstr_set(x_2142, 3, x_1265);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2143 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2143 = lean::box(0);
}
lean::cnstr_set_uint8(x_2142, sizeof(void*)*4, x_2095);
if (lean::is_scalar(x_2143)) {
 x_2144 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2144 = x_2143;
}
lean::cnstr_set(x_2144, 0, x_2142);
lean::cnstr_set(x_2144, 1, x_2);
lean::cnstr_set(x_2144, 2, x_3);
lean::cnstr_set(x_2144, 3, x_2136);
lean::cnstr_set_uint8(x_2144, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_234, 3, x_2096);
lean::cnstr_set(x_234, 2, x_2135);
lean::cnstr_set(x_234, 1, x_2134);
lean::cnstr_set(x_234, 0, x_2139);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_2138);
lean::cnstr_set(x_1, 1, x_2137);
lean::cnstr_set(x_1, 0, x_2144);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
}
else
{
obj* x_2145; obj* x_2146; obj* x_2147; obj* x_2148; obj* x_2149; obj* x_2150; obj* x_2151; obj* x_2152; obj* x_2153; obj* x_2154; obj* x_2155; obj* x_2156; obj* x_2157; obj* x_2158; obj* x_2159; obj* x_2160; obj* x_2161; 
x_2145 = lean::cnstr_get(x_234, 0);
x_2146 = lean::cnstr_get(x_234, 1);
x_2147 = lean::cnstr_get(x_234, 2);
x_2148 = lean::cnstr_get(x_234, 3);
lean::inc(x_2148);
lean::inc(x_2147);
lean::inc(x_2146);
lean::inc(x_2145);
lean::dec(x_234);
x_2149 = lean::cnstr_get(x_4, 1);
lean::inc(x_2149);
x_2150 = lean::cnstr_get(x_4, 2);
lean::inc(x_2150);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_2151 = x_4;
} else {
 lean::dec_ref(x_4);
 x_2151 = lean::box(0);
}
x_2152 = lean::cnstr_get(x_1890, 0);
lean::inc(x_2152);
x_2153 = lean::cnstr_get(x_1890, 1);
lean::inc(x_2153);
x_2154 = lean::cnstr_get(x_1890, 2);
lean::inc(x_2154);
x_2155 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2155);
if (lean::is_exclusive(x_1890)) {
 lean::cnstr_release(x_1890, 0);
 lean::cnstr_release(x_1890, 1);
 lean::cnstr_release(x_1890, 2);
 lean::cnstr_release(x_1890, 3);
 x_2156 = x_1890;
} else {
 lean::dec_ref(x_1890);
 x_2156 = lean::box(0);
}
if (lean::is_scalar(x_2156)) {
 x_2157 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2157 = x_2156;
}
lean::cnstr_set(x_2157, 0, x_2145);
lean::cnstr_set(x_2157, 1, x_2146);
lean::cnstr_set(x_2157, 2, x_2147);
lean::cnstr_set(x_2157, 3, x_2148);
lean::cnstr_set_uint8(x_2157, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
if (lean::is_scalar(x_2151)) {
 x_2158 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2158 = x_2151;
}
lean::cnstr_set(x_2158, 0, x_2157);
lean::cnstr_set(x_2158, 1, x_2098);
lean::cnstr_set(x_2158, 2, x_2099);
lean::cnstr_set(x_2158, 3, x_1265);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2159 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2159 = lean::box(0);
}
lean::cnstr_set_uint8(x_2158, sizeof(void*)*4, x_2095);
if (lean::is_scalar(x_2159)) {
 x_2160 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2160 = x_2159;
}
lean::cnstr_set(x_2160, 0, x_2158);
lean::cnstr_set(x_2160, 1, x_2);
lean::cnstr_set(x_2160, 2, x_3);
lean::cnstr_set(x_2160, 3, x_2152);
lean::cnstr_set_uint8(x_2160, sizeof(void*)*4, x_1833);
x_2161 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2161, 0, x_2155);
lean::cnstr_set(x_2161, 1, x_2149);
lean::cnstr_set(x_2161, 2, x_2150);
lean::cnstr_set(x_2161, 3, x_2096);
lean::cnstr_set_uint8(x_2161, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_2161);
lean::cnstr_set(x_1, 2, x_2154);
lean::cnstr_set(x_1, 1, x_2153);
lean::cnstr_set(x_1, 0, x_2160);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
}
else
{
obj* x_2162; obj* x_2163; obj* x_2164; obj* x_2165; obj* x_2166; obj* x_2167; obj* x_2168; obj* x_2169; obj* x_2170; obj* x_2171; obj* x_2172; obj* x_2173; obj* x_2174; obj* x_2175; obj* x_2176; obj* x_2177; obj* x_2178; obj* x_2179; obj* x_2180; obj* x_2181; obj* x_2182; 
x_2162 = lean::cnstr_get(x_1, 1);
x_2163 = lean::cnstr_get(x_1, 2);
lean::inc(x_2163);
lean::inc(x_2162);
lean::dec(x_1);
x_2164 = lean::cnstr_get(x_234, 0);
lean::inc(x_2164);
x_2165 = lean::cnstr_get(x_234, 1);
lean::inc(x_2165);
x_2166 = lean::cnstr_get(x_234, 2);
lean::inc(x_2166);
x_2167 = lean::cnstr_get(x_234, 3);
lean::inc(x_2167);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_2168 = x_234;
} else {
 lean::dec_ref(x_234);
 x_2168 = lean::box(0);
}
x_2169 = lean::cnstr_get(x_4, 1);
lean::inc(x_2169);
x_2170 = lean::cnstr_get(x_4, 2);
lean::inc(x_2170);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_2171 = x_4;
} else {
 lean::dec_ref(x_4);
 x_2171 = lean::box(0);
}
x_2172 = lean::cnstr_get(x_1890, 0);
lean::inc(x_2172);
x_2173 = lean::cnstr_get(x_1890, 1);
lean::inc(x_2173);
x_2174 = lean::cnstr_get(x_1890, 2);
lean::inc(x_2174);
x_2175 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2175);
if (lean::is_exclusive(x_1890)) {
 lean::cnstr_release(x_1890, 0);
 lean::cnstr_release(x_1890, 1);
 lean::cnstr_release(x_1890, 2);
 lean::cnstr_release(x_1890, 3);
 x_2176 = x_1890;
} else {
 lean::dec_ref(x_1890);
 x_2176 = lean::box(0);
}
if (lean::is_scalar(x_2176)) {
 x_2177 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2177 = x_2176;
}
lean::cnstr_set(x_2177, 0, x_2164);
lean::cnstr_set(x_2177, 1, x_2165);
lean::cnstr_set(x_2177, 2, x_2166);
lean::cnstr_set(x_2177, 3, x_2167);
lean::cnstr_set_uint8(x_2177, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
if (lean::is_scalar(x_2171)) {
 x_2178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2178 = x_2171;
}
lean::cnstr_set(x_2178, 0, x_2177);
lean::cnstr_set(x_2178, 1, x_2162);
lean::cnstr_set(x_2178, 2, x_2163);
lean::cnstr_set(x_2178, 3, x_1265);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2179 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2179 = lean::box(0);
}
lean::cnstr_set_uint8(x_2178, sizeof(void*)*4, x_2095);
if (lean::is_scalar(x_2179)) {
 x_2180 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2180 = x_2179;
}
lean::cnstr_set(x_2180, 0, x_2178);
lean::cnstr_set(x_2180, 1, x_2);
lean::cnstr_set(x_2180, 2, x_3);
lean::cnstr_set(x_2180, 3, x_2172);
lean::cnstr_set_uint8(x_2180, sizeof(void*)*4, x_1833);
if (lean::is_scalar(x_2168)) {
 x_2181 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2181 = x_2168;
}
lean::cnstr_set(x_2181, 0, x_2175);
lean::cnstr_set(x_2181, 1, x_2169);
lean::cnstr_set(x_2181, 2, x_2170);
lean::cnstr_set(x_2181, 3, x_2096);
lean::cnstr_set_uint8(x_2181, sizeof(void*)*4, x_1833);
x_2182 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2182, 0, x_2180);
lean::cnstr_set(x_2182, 1, x_2173);
lean::cnstr_set(x_2182, 2, x_2174);
lean::cnstr_set(x_2182, 3, x_2181);
lean::cnstr_set_uint8(x_2182, sizeof(void*)*4, x_2095);
return x_2182;
}
}
else
{
uint8 x_2183; 
x_2183 = lean::cnstr_get_uint8(x_2096, sizeof(void*)*4);
if (x_2183 == 0)
{
uint8 x_2184; 
x_2184 = !lean::is_exclusive(x_1);
if (x_2184 == 0)
{
obj* x_2185; obj* x_2186; obj* x_2187; obj* x_2188; uint8 x_2189; 
x_2185 = lean::cnstr_get(x_1, 1);
x_2186 = lean::cnstr_get(x_1, 2);
x_2187 = lean::cnstr_get(x_1, 3);
lean::dec(x_2187);
x_2188 = lean::cnstr_get(x_1, 0);
lean::dec(x_2188);
x_2189 = !lean::is_exclusive(x_234);
if (x_2189 == 0)
{
uint8 x_2190; 
x_2190 = !lean::is_exclusive(x_4);
if (x_2190 == 0)
{
obj* x_2191; obj* x_2192; obj* x_2193; obj* x_2194; obj* x_2195; obj* x_2196; obj* x_2197; obj* x_2198; uint8 x_2199; 
x_2191 = lean::cnstr_get(x_234, 0);
x_2192 = lean::cnstr_get(x_234, 1);
x_2193 = lean::cnstr_get(x_234, 2);
x_2194 = lean::cnstr_get(x_234, 3);
x_2195 = lean::cnstr_get(x_4, 1);
x_2196 = lean::cnstr_get(x_4, 2);
x_2197 = lean::cnstr_get(x_4, 3);
lean::dec(x_2197);
x_2198 = lean::cnstr_get(x_4, 0);
lean::dec(x_2198);
x_2199 = !lean::is_exclusive(x_1890);
if (x_2199 == 0)
{
uint8 x_2200; 
x_2200 = !lean::is_exclusive(x_2096);
if (x_2200 == 0)
{
obj* x_2201; obj* x_2202; obj* x_2203; obj* x_2204; obj* x_2205; obj* x_2206; obj* x_2207; obj* x_2208; uint8 x_2209; 
x_2201 = lean::cnstr_get(x_1890, 0);
x_2202 = lean::cnstr_get(x_1890, 1);
x_2203 = lean::cnstr_get(x_1890, 2);
x_2204 = lean::cnstr_get(x_1890, 3);
x_2205 = lean::cnstr_get(x_2096, 0);
x_2206 = lean::cnstr_get(x_2096, 1);
x_2207 = lean::cnstr_get(x_2096, 2);
x_2208 = lean::cnstr_get(x_2096, 3);
lean::cnstr_set(x_2096, 3, x_2194);
lean::cnstr_set(x_2096, 2, x_2193);
lean::cnstr_set(x_2096, 1, x_2192);
lean::cnstr_set(x_2096, 0, x_2191);
lean::cnstr_set_uint8(x_2096, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
lean::cnstr_set(x_1890, 3, x_1265);
lean::cnstr_set(x_1890, 2, x_2186);
lean::cnstr_set(x_1890, 1, x_2185);
lean::cnstr_set(x_1890, 0, x_2096);
x_2209 = !lean::is_exclusive(x_1265);
if (x_2209 == 0)
{
obj* x_2210; obj* x_2211; obj* x_2212; obj* x_2213; 
x_2210 = lean::cnstr_get(x_1265, 3);
lean::dec(x_2210);
x_2211 = lean::cnstr_get(x_1265, 2);
lean::dec(x_2211);
x_2212 = lean::cnstr_get(x_1265, 1);
lean::dec(x_2212);
x_2213 = lean::cnstr_get(x_1265, 0);
lean::dec(x_2213);
lean::cnstr_set_uint8(x_1890, sizeof(void*)*4, x_2183);
lean::cnstr_set(x_4, 3, x_2204);
lean::cnstr_set(x_4, 2, x_2203);
lean::cnstr_set(x_4, 1, x_2202);
lean::cnstr_set(x_4, 0, x_2201);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2183);
lean::cnstr_set(x_1265, 3, x_4);
lean::cnstr_set(x_1265, 2, x_3);
lean::cnstr_set(x_1265, 1, x_2);
lean::cnstr_set(x_1265, 0, x_1890);
lean::cnstr_set(x_234, 3, x_2208);
lean::cnstr_set(x_234, 2, x_2207);
lean::cnstr_set(x_234, 1, x_2206);
lean::cnstr_set(x_234, 0, x_2205);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_2196);
lean::cnstr_set(x_1, 1, x_2195);
lean::cnstr_set(x_1, 0, x_1265);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2183);
return x_1;
}
else
{
obj* x_2214; 
lean::dec(x_1265);
lean::cnstr_set_uint8(x_1890, sizeof(void*)*4, x_2183);
lean::cnstr_set(x_4, 3, x_2204);
lean::cnstr_set(x_4, 2, x_2203);
lean::cnstr_set(x_4, 1, x_2202);
lean::cnstr_set(x_4, 0, x_2201);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2183);
x_2214 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2214, 0, x_1890);
lean::cnstr_set(x_2214, 1, x_2);
lean::cnstr_set(x_2214, 2, x_3);
lean::cnstr_set(x_2214, 3, x_4);
lean::cnstr_set_uint8(x_2214, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_234, 3, x_2208);
lean::cnstr_set(x_234, 2, x_2207);
lean::cnstr_set(x_234, 1, x_2206);
lean::cnstr_set(x_234, 0, x_2205);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_2196);
lean::cnstr_set(x_1, 1, x_2195);
lean::cnstr_set(x_1, 0, x_2214);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2183);
return x_1;
}
}
else
{
obj* x_2215; obj* x_2216; obj* x_2217; obj* x_2218; obj* x_2219; obj* x_2220; obj* x_2221; obj* x_2222; obj* x_2223; obj* x_2224; obj* x_2225; 
x_2215 = lean::cnstr_get(x_1890, 0);
x_2216 = lean::cnstr_get(x_1890, 1);
x_2217 = lean::cnstr_get(x_1890, 2);
x_2218 = lean::cnstr_get(x_1890, 3);
x_2219 = lean::cnstr_get(x_2096, 0);
x_2220 = lean::cnstr_get(x_2096, 1);
x_2221 = lean::cnstr_get(x_2096, 2);
x_2222 = lean::cnstr_get(x_2096, 3);
lean::inc(x_2222);
lean::inc(x_2221);
lean::inc(x_2220);
lean::inc(x_2219);
lean::dec(x_2096);
x_2223 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2223, 0, x_2191);
lean::cnstr_set(x_2223, 1, x_2192);
lean::cnstr_set(x_2223, 2, x_2193);
lean::cnstr_set(x_2223, 3, x_2194);
lean::cnstr_set_uint8(x_2223, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
lean::cnstr_set(x_1890, 3, x_1265);
lean::cnstr_set(x_1890, 2, x_2186);
lean::cnstr_set(x_1890, 1, x_2185);
lean::cnstr_set(x_1890, 0, x_2223);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2224 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2224 = lean::box(0);
}
lean::cnstr_set_uint8(x_1890, sizeof(void*)*4, x_2183);
lean::cnstr_set(x_4, 3, x_2218);
lean::cnstr_set(x_4, 2, x_2217);
lean::cnstr_set(x_4, 1, x_2216);
lean::cnstr_set(x_4, 0, x_2215);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2183);
if (lean::is_scalar(x_2224)) {
 x_2225 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2225 = x_2224;
}
lean::cnstr_set(x_2225, 0, x_1890);
lean::cnstr_set(x_2225, 1, x_2);
lean::cnstr_set(x_2225, 2, x_3);
lean::cnstr_set(x_2225, 3, x_4);
lean::cnstr_set_uint8(x_2225, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_234, 3, x_2222);
lean::cnstr_set(x_234, 2, x_2221);
lean::cnstr_set(x_234, 1, x_2220);
lean::cnstr_set(x_234, 0, x_2219);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_2196);
lean::cnstr_set(x_1, 1, x_2195);
lean::cnstr_set(x_1, 0, x_2225);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2183);
return x_1;
}
}
else
{
obj* x_2226; obj* x_2227; obj* x_2228; obj* x_2229; obj* x_2230; obj* x_2231; obj* x_2232; obj* x_2233; obj* x_2234; obj* x_2235; obj* x_2236; obj* x_2237; obj* x_2238; 
x_2226 = lean::cnstr_get(x_1890, 0);
x_2227 = lean::cnstr_get(x_1890, 1);
x_2228 = lean::cnstr_get(x_1890, 2);
x_2229 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2229);
lean::inc(x_2228);
lean::inc(x_2227);
lean::inc(x_2226);
lean::dec(x_1890);
x_2230 = lean::cnstr_get(x_2096, 0);
lean::inc(x_2230);
x_2231 = lean::cnstr_get(x_2096, 1);
lean::inc(x_2231);
x_2232 = lean::cnstr_get(x_2096, 2);
lean::inc(x_2232);
x_2233 = lean::cnstr_get(x_2096, 3);
lean::inc(x_2233);
if (lean::is_exclusive(x_2096)) {
 lean::cnstr_release(x_2096, 0);
 lean::cnstr_release(x_2096, 1);
 lean::cnstr_release(x_2096, 2);
 lean::cnstr_release(x_2096, 3);
 x_2234 = x_2096;
} else {
 lean::dec_ref(x_2096);
 x_2234 = lean::box(0);
}
if (lean::is_scalar(x_2234)) {
 x_2235 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2235 = x_2234;
}
lean::cnstr_set(x_2235, 0, x_2191);
lean::cnstr_set(x_2235, 1, x_2192);
lean::cnstr_set(x_2235, 2, x_2193);
lean::cnstr_set(x_2235, 3, x_2194);
lean::cnstr_set_uint8(x_2235, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
x_2236 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2236, 0, x_2235);
lean::cnstr_set(x_2236, 1, x_2185);
lean::cnstr_set(x_2236, 2, x_2186);
lean::cnstr_set(x_2236, 3, x_1265);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2237 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2237 = lean::box(0);
}
lean::cnstr_set_uint8(x_2236, sizeof(void*)*4, x_2183);
lean::cnstr_set(x_4, 3, x_2229);
lean::cnstr_set(x_4, 2, x_2228);
lean::cnstr_set(x_4, 1, x_2227);
lean::cnstr_set(x_4, 0, x_2226);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2183);
if (lean::is_scalar(x_2237)) {
 x_2238 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2238 = x_2237;
}
lean::cnstr_set(x_2238, 0, x_2236);
lean::cnstr_set(x_2238, 1, x_2);
lean::cnstr_set(x_2238, 2, x_3);
lean::cnstr_set(x_2238, 3, x_4);
lean::cnstr_set_uint8(x_2238, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_234, 3, x_2233);
lean::cnstr_set(x_234, 2, x_2232);
lean::cnstr_set(x_234, 1, x_2231);
lean::cnstr_set(x_234, 0, x_2230);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_2196);
lean::cnstr_set(x_1, 1, x_2195);
lean::cnstr_set(x_1, 0, x_2238);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2183);
return x_1;
}
}
else
{
obj* x_2239; obj* x_2240; obj* x_2241; obj* x_2242; obj* x_2243; obj* x_2244; obj* x_2245; obj* x_2246; obj* x_2247; obj* x_2248; obj* x_2249; obj* x_2250; obj* x_2251; obj* x_2252; obj* x_2253; obj* x_2254; obj* x_2255; obj* x_2256; obj* x_2257; obj* x_2258; obj* x_2259; 
x_2239 = lean::cnstr_get(x_234, 0);
x_2240 = lean::cnstr_get(x_234, 1);
x_2241 = lean::cnstr_get(x_234, 2);
x_2242 = lean::cnstr_get(x_234, 3);
x_2243 = lean::cnstr_get(x_4, 1);
x_2244 = lean::cnstr_get(x_4, 2);
lean::inc(x_2244);
lean::inc(x_2243);
lean::dec(x_4);
x_2245 = lean::cnstr_get(x_1890, 0);
lean::inc(x_2245);
x_2246 = lean::cnstr_get(x_1890, 1);
lean::inc(x_2246);
x_2247 = lean::cnstr_get(x_1890, 2);
lean::inc(x_2247);
x_2248 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2248);
if (lean::is_exclusive(x_1890)) {
 lean::cnstr_release(x_1890, 0);
 lean::cnstr_release(x_1890, 1);
 lean::cnstr_release(x_1890, 2);
 lean::cnstr_release(x_1890, 3);
 x_2249 = x_1890;
} else {
 lean::dec_ref(x_1890);
 x_2249 = lean::box(0);
}
x_2250 = lean::cnstr_get(x_2096, 0);
lean::inc(x_2250);
x_2251 = lean::cnstr_get(x_2096, 1);
lean::inc(x_2251);
x_2252 = lean::cnstr_get(x_2096, 2);
lean::inc(x_2252);
x_2253 = lean::cnstr_get(x_2096, 3);
lean::inc(x_2253);
if (lean::is_exclusive(x_2096)) {
 lean::cnstr_release(x_2096, 0);
 lean::cnstr_release(x_2096, 1);
 lean::cnstr_release(x_2096, 2);
 lean::cnstr_release(x_2096, 3);
 x_2254 = x_2096;
} else {
 lean::dec_ref(x_2096);
 x_2254 = lean::box(0);
}
if (lean::is_scalar(x_2254)) {
 x_2255 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2255 = x_2254;
}
lean::cnstr_set(x_2255, 0, x_2239);
lean::cnstr_set(x_2255, 1, x_2240);
lean::cnstr_set(x_2255, 2, x_2241);
lean::cnstr_set(x_2255, 3, x_2242);
lean::cnstr_set_uint8(x_2255, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
if (lean::is_scalar(x_2249)) {
 x_2256 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2256 = x_2249;
}
lean::cnstr_set(x_2256, 0, x_2255);
lean::cnstr_set(x_2256, 1, x_2185);
lean::cnstr_set(x_2256, 2, x_2186);
lean::cnstr_set(x_2256, 3, x_1265);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2257 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2257 = lean::box(0);
}
lean::cnstr_set_uint8(x_2256, sizeof(void*)*4, x_2183);
x_2258 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2258, 0, x_2245);
lean::cnstr_set(x_2258, 1, x_2246);
lean::cnstr_set(x_2258, 2, x_2247);
lean::cnstr_set(x_2258, 3, x_2248);
lean::cnstr_set_uint8(x_2258, sizeof(void*)*4, x_2183);
if (lean::is_scalar(x_2257)) {
 x_2259 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2259 = x_2257;
}
lean::cnstr_set(x_2259, 0, x_2256);
lean::cnstr_set(x_2259, 1, x_2);
lean::cnstr_set(x_2259, 2, x_3);
lean::cnstr_set(x_2259, 3, x_2258);
lean::cnstr_set_uint8(x_2259, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_234, 3, x_2253);
lean::cnstr_set(x_234, 2, x_2252);
lean::cnstr_set(x_234, 1, x_2251);
lean::cnstr_set(x_234, 0, x_2250);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 2, x_2244);
lean::cnstr_set(x_1, 1, x_2243);
lean::cnstr_set(x_1, 0, x_2259);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2183);
return x_1;
}
}
else
{
obj* x_2260; obj* x_2261; obj* x_2262; obj* x_2263; obj* x_2264; obj* x_2265; obj* x_2266; obj* x_2267; obj* x_2268; obj* x_2269; obj* x_2270; obj* x_2271; obj* x_2272; obj* x_2273; obj* x_2274; obj* x_2275; obj* x_2276; obj* x_2277; obj* x_2278; obj* x_2279; obj* x_2280; obj* x_2281; obj* x_2282; 
x_2260 = lean::cnstr_get(x_234, 0);
x_2261 = lean::cnstr_get(x_234, 1);
x_2262 = lean::cnstr_get(x_234, 2);
x_2263 = lean::cnstr_get(x_234, 3);
lean::inc(x_2263);
lean::inc(x_2262);
lean::inc(x_2261);
lean::inc(x_2260);
lean::dec(x_234);
x_2264 = lean::cnstr_get(x_4, 1);
lean::inc(x_2264);
x_2265 = lean::cnstr_get(x_4, 2);
lean::inc(x_2265);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_2266 = x_4;
} else {
 lean::dec_ref(x_4);
 x_2266 = lean::box(0);
}
x_2267 = lean::cnstr_get(x_1890, 0);
lean::inc(x_2267);
x_2268 = lean::cnstr_get(x_1890, 1);
lean::inc(x_2268);
x_2269 = lean::cnstr_get(x_1890, 2);
lean::inc(x_2269);
x_2270 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2270);
if (lean::is_exclusive(x_1890)) {
 lean::cnstr_release(x_1890, 0);
 lean::cnstr_release(x_1890, 1);
 lean::cnstr_release(x_1890, 2);
 lean::cnstr_release(x_1890, 3);
 x_2271 = x_1890;
} else {
 lean::dec_ref(x_1890);
 x_2271 = lean::box(0);
}
x_2272 = lean::cnstr_get(x_2096, 0);
lean::inc(x_2272);
x_2273 = lean::cnstr_get(x_2096, 1);
lean::inc(x_2273);
x_2274 = lean::cnstr_get(x_2096, 2);
lean::inc(x_2274);
x_2275 = lean::cnstr_get(x_2096, 3);
lean::inc(x_2275);
if (lean::is_exclusive(x_2096)) {
 lean::cnstr_release(x_2096, 0);
 lean::cnstr_release(x_2096, 1);
 lean::cnstr_release(x_2096, 2);
 lean::cnstr_release(x_2096, 3);
 x_2276 = x_2096;
} else {
 lean::dec_ref(x_2096);
 x_2276 = lean::box(0);
}
if (lean::is_scalar(x_2276)) {
 x_2277 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2277 = x_2276;
}
lean::cnstr_set(x_2277, 0, x_2260);
lean::cnstr_set(x_2277, 1, x_2261);
lean::cnstr_set(x_2277, 2, x_2262);
lean::cnstr_set(x_2277, 3, x_2263);
lean::cnstr_set_uint8(x_2277, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
if (lean::is_scalar(x_2271)) {
 x_2278 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2278 = x_2271;
}
lean::cnstr_set(x_2278, 0, x_2277);
lean::cnstr_set(x_2278, 1, x_2185);
lean::cnstr_set(x_2278, 2, x_2186);
lean::cnstr_set(x_2278, 3, x_1265);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2279 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2279 = lean::box(0);
}
lean::cnstr_set_uint8(x_2278, sizeof(void*)*4, x_2183);
if (lean::is_scalar(x_2266)) {
 x_2280 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2280 = x_2266;
}
lean::cnstr_set(x_2280, 0, x_2267);
lean::cnstr_set(x_2280, 1, x_2268);
lean::cnstr_set(x_2280, 2, x_2269);
lean::cnstr_set(x_2280, 3, x_2270);
lean::cnstr_set_uint8(x_2280, sizeof(void*)*4, x_2183);
if (lean::is_scalar(x_2279)) {
 x_2281 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2281 = x_2279;
}
lean::cnstr_set(x_2281, 0, x_2278);
lean::cnstr_set(x_2281, 1, x_2);
lean::cnstr_set(x_2281, 2, x_3);
lean::cnstr_set(x_2281, 3, x_2280);
lean::cnstr_set_uint8(x_2281, sizeof(void*)*4, x_1833);
x_2282 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2282, 0, x_2272);
lean::cnstr_set(x_2282, 1, x_2273);
lean::cnstr_set(x_2282, 2, x_2274);
lean::cnstr_set(x_2282, 3, x_2275);
lean::cnstr_set_uint8(x_2282, sizeof(void*)*4, x_1833);
lean::cnstr_set(x_1, 3, x_2282);
lean::cnstr_set(x_1, 2, x_2265);
lean::cnstr_set(x_1, 1, x_2264);
lean::cnstr_set(x_1, 0, x_2281);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2183);
return x_1;
}
}
else
{
obj* x_2283; obj* x_2284; obj* x_2285; obj* x_2286; obj* x_2287; obj* x_2288; obj* x_2289; obj* x_2290; obj* x_2291; obj* x_2292; obj* x_2293; obj* x_2294; obj* x_2295; obj* x_2296; obj* x_2297; obj* x_2298; obj* x_2299; obj* x_2300; obj* x_2301; obj* x_2302; obj* x_2303; obj* x_2304; obj* x_2305; obj* x_2306; obj* x_2307; obj* x_2308; obj* x_2309; 
x_2283 = lean::cnstr_get(x_1, 1);
x_2284 = lean::cnstr_get(x_1, 2);
lean::inc(x_2284);
lean::inc(x_2283);
lean::dec(x_1);
x_2285 = lean::cnstr_get(x_234, 0);
lean::inc(x_2285);
x_2286 = lean::cnstr_get(x_234, 1);
lean::inc(x_2286);
x_2287 = lean::cnstr_get(x_234, 2);
lean::inc(x_2287);
x_2288 = lean::cnstr_get(x_234, 3);
lean::inc(x_2288);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_2289 = x_234;
} else {
 lean::dec_ref(x_234);
 x_2289 = lean::box(0);
}
x_2290 = lean::cnstr_get(x_4, 1);
lean::inc(x_2290);
x_2291 = lean::cnstr_get(x_4, 2);
lean::inc(x_2291);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_2292 = x_4;
} else {
 lean::dec_ref(x_4);
 x_2292 = lean::box(0);
}
x_2293 = lean::cnstr_get(x_1890, 0);
lean::inc(x_2293);
x_2294 = lean::cnstr_get(x_1890, 1);
lean::inc(x_2294);
x_2295 = lean::cnstr_get(x_1890, 2);
lean::inc(x_2295);
x_2296 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2296);
if (lean::is_exclusive(x_1890)) {
 lean::cnstr_release(x_1890, 0);
 lean::cnstr_release(x_1890, 1);
 lean::cnstr_release(x_1890, 2);
 lean::cnstr_release(x_1890, 3);
 x_2297 = x_1890;
} else {
 lean::dec_ref(x_1890);
 x_2297 = lean::box(0);
}
x_2298 = lean::cnstr_get(x_2096, 0);
lean::inc(x_2298);
x_2299 = lean::cnstr_get(x_2096, 1);
lean::inc(x_2299);
x_2300 = lean::cnstr_get(x_2096, 2);
lean::inc(x_2300);
x_2301 = lean::cnstr_get(x_2096, 3);
lean::inc(x_2301);
if (lean::is_exclusive(x_2096)) {
 lean::cnstr_release(x_2096, 0);
 lean::cnstr_release(x_2096, 1);
 lean::cnstr_release(x_2096, 2);
 lean::cnstr_release(x_2096, 3);
 x_2302 = x_2096;
} else {
 lean::dec_ref(x_2096);
 x_2302 = lean::box(0);
}
if (lean::is_scalar(x_2302)) {
 x_2303 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2303 = x_2302;
}
lean::cnstr_set(x_2303, 0, x_2285);
lean::cnstr_set(x_2303, 1, x_2286);
lean::cnstr_set(x_2303, 2, x_2287);
lean::cnstr_set(x_2303, 3, x_2288);
lean::cnstr_set_uint8(x_2303, sizeof(void*)*4, x_1833);
lean::inc(x_1265);
if (lean::is_scalar(x_2297)) {
 x_2304 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2304 = x_2297;
}
lean::cnstr_set(x_2304, 0, x_2303);
lean::cnstr_set(x_2304, 1, x_2283);
lean::cnstr_set(x_2304, 2, x_2284);
lean::cnstr_set(x_2304, 3, x_1265);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2305 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2305 = lean::box(0);
}
lean::cnstr_set_uint8(x_2304, sizeof(void*)*4, x_2183);
if (lean::is_scalar(x_2292)) {
 x_2306 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2306 = x_2292;
}
lean::cnstr_set(x_2306, 0, x_2293);
lean::cnstr_set(x_2306, 1, x_2294);
lean::cnstr_set(x_2306, 2, x_2295);
lean::cnstr_set(x_2306, 3, x_2296);
lean::cnstr_set_uint8(x_2306, sizeof(void*)*4, x_2183);
if (lean::is_scalar(x_2305)) {
 x_2307 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2307 = x_2305;
}
lean::cnstr_set(x_2307, 0, x_2304);
lean::cnstr_set(x_2307, 1, x_2);
lean::cnstr_set(x_2307, 2, x_3);
lean::cnstr_set(x_2307, 3, x_2306);
lean::cnstr_set_uint8(x_2307, sizeof(void*)*4, x_1833);
if (lean::is_scalar(x_2289)) {
 x_2308 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2308 = x_2289;
}
lean::cnstr_set(x_2308, 0, x_2298);
lean::cnstr_set(x_2308, 1, x_2299);
lean::cnstr_set(x_2308, 2, x_2300);
lean::cnstr_set(x_2308, 3, x_2301);
lean::cnstr_set_uint8(x_2308, sizeof(void*)*4, x_1833);
x_2309 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2309, 0, x_2307);
lean::cnstr_set(x_2309, 1, x_2290);
lean::cnstr_set(x_2309, 2, x_2291);
lean::cnstr_set(x_2309, 3, x_2308);
lean::cnstr_set_uint8(x_2309, sizeof(void*)*4, x_2183);
return x_2309;
}
}
else
{
uint8 x_2310; 
x_2310 = !lean::is_exclusive(x_1);
if (x_2310 == 0)
{
obj* x_2311; obj* x_2312; obj* x_2313; obj* x_2314; uint8 x_2315; 
x_2311 = lean::cnstr_get(x_1, 1);
x_2312 = lean::cnstr_get(x_1, 2);
x_2313 = lean::cnstr_get(x_1, 3);
lean::dec(x_2313);
x_2314 = lean::cnstr_get(x_1, 0);
lean::dec(x_2314);
x_2315 = !lean::is_exclusive(x_234);
if (x_2315 == 0)
{
uint8 x_2316; 
x_2316 = !lean::is_exclusive(x_1265);
if (x_2316 == 0)
{
uint8 x_2317; 
x_2317 = !lean::is_exclusive(x_4);
if (x_2317 == 0)
{
obj* x_2318; obj* x_2319; obj* x_2320; obj* x_2321; obj* x_2322; obj* x_2323; obj* x_2324; obj* x_2325; obj* x_2326; obj* x_2327; obj* x_2328; obj* x_2329; uint8 x_2330; 
x_2318 = lean::cnstr_get(x_234, 0);
x_2319 = lean::cnstr_get(x_234, 1);
x_2320 = lean::cnstr_get(x_234, 2);
x_2321 = lean::cnstr_get(x_234, 3);
x_2322 = lean::cnstr_get(x_1265, 0);
x_2323 = lean::cnstr_get(x_1265, 1);
x_2324 = lean::cnstr_get(x_1265, 2);
x_2325 = lean::cnstr_get(x_1265, 3);
x_2326 = lean::cnstr_get(x_4, 1);
x_2327 = lean::cnstr_get(x_4, 2);
x_2328 = lean::cnstr_get(x_4, 3);
lean::dec(x_2328);
x_2329 = lean::cnstr_get(x_4, 0);
lean::dec(x_2329);
x_2330 = !lean::is_exclusive(x_1890);
if (x_2330 == 0)
{
obj* x_2331; obj* x_2332; obj* x_2333; obj* x_2334; obj* x_2335; 
x_2331 = lean::cnstr_get(x_1890, 0);
x_2332 = lean::cnstr_get(x_1890, 1);
x_2333 = lean::cnstr_get(x_1890, 2);
x_2334 = lean::cnstr_get(x_1890, 3);
lean::cnstr_set(x_1890, 3, x_2321);
lean::cnstr_set(x_1890, 2, x_2320);
lean::cnstr_set(x_1890, 1, x_2319);
lean::cnstr_set(x_1890, 0, x_2318);
lean::cnstr_set_uint8(x_1890, sizeof(void*)*4, x_2183);
lean::cnstr_set(x_4, 3, x_2325);
lean::cnstr_set(x_4, 2, x_2324);
lean::cnstr_set(x_4, 1, x_2323);
lean::cnstr_set(x_4, 0, x_2322);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2183);
lean::cnstr_set(x_1265, 3, x_4);
lean::cnstr_set(x_1265, 2, x_2312);
lean::cnstr_set(x_1265, 1, x_2311);
lean::cnstr_set(x_1265, 0, x_1890);
lean::cnstr_set_uint8(x_1265, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_234, 3, x_2331);
lean::cnstr_set(x_234, 2, x_3);
lean::cnstr_set(x_234, 1, x_2);
lean::cnstr_set(x_234, 0, x_1265);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_2183);
lean::cnstr_set(x_1, 3, x_2096);
lean::cnstr_set(x_1, 2, x_2327);
lean::cnstr_set(x_1, 1, x_2326);
lean::cnstr_set(x_1, 0, x_2334);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2183);
x_2335 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2335, 0, x_234);
lean::cnstr_set(x_2335, 1, x_2332);
lean::cnstr_set(x_2335, 2, x_2333);
lean::cnstr_set(x_2335, 3, x_1);
lean::cnstr_set_uint8(x_2335, sizeof(void*)*4, x_2095);
return x_2335;
}
else
{
obj* x_2336; obj* x_2337; obj* x_2338; obj* x_2339; obj* x_2340; obj* x_2341; 
x_2336 = lean::cnstr_get(x_1890, 0);
x_2337 = lean::cnstr_get(x_1890, 1);
x_2338 = lean::cnstr_get(x_1890, 2);
x_2339 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2339);
lean::inc(x_2338);
lean::inc(x_2337);
lean::inc(x_2336);
lean::dec(x_1890);
x_2340 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2340, 0, x_2318);
lean::cnstr_set(x_2340, 1, x_2319);
lean::cnstr_set(x_2340, 2, x_2320);
lean::cnstr_set(x_2340, 3, x_2321);
lean::cnstr_set_uint8(x_2340, sizeof(void*)*4, x_2183);
lean::cnstr_set(x_4, 3, x_2325);
lean::cnstr_set(x_4, 2, x_2324);
lean::cnstr_set(x_4, 1, x_2323);
lean::cnstr_set(x_4, 0, x_2322);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2183);
lean::cnstr_set(x_1265, 3, x_4);
lean::cnstr_set(x_1265, 2, x_2312);
lean::cnstr_set(x_1265, 1, x_2311);
lean::cnstr_set(x_1265, 0, x_2340);
lean::cnstr_set_uint8(x_1265, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_234, 3, x_2336);
lean::cnstr_set(x_234, 2, x_3);
lean::cnstr_set(x_234, 1, x_2);
lean::cnstr_set(x_234, 0, x_1265);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_2183);
lean::cnstr_set(x_1, 3, x_2096);
lean::cnstr_set(x_1, 2, x_2327);
lean::cnstr_set(x_1, 1, x_2326);
lean::cnstr_set(x_1, 0, x_2339);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2183);
x_2341 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2341, 0, x_234);
lean::cnstr_set(x_2341, 1, x_2337);
lean::cnstr_set(x_2341, 2, x_2338);
lean::cnstr_set(x_2341, 3, x_1);
lean::cnstr_set_uint8(x_2341, sizeof(void*)*4, x_2095);
return x_2341;
}
}
else
{
obj* x_2342; obj* x_2343; obj* x_2344; obj* x_2345; obj* x_2346; obj* x_2347; obj* x_2348; obj* x_2349; obj* x_2350; obj* x_2351; obj* x_2352; obj* x_2353; obj* x_2354; obj* x_2355; obj* x_2356; obj* x_2357; obj* x_2358; obj* x_2359; 
x_2342 = lean::cnstr_get(x_234, 0);
x_2343 = lean::cnstr_get(x_234, 1);
x_2344 = lean::cnstr_get(x_234, 2);
x_2345 = lean::cnstr_get(x_234, 3);
x_2346 = lean::cnstr_get(x_1265, 0);
x_2347 = lean::cnstr_get(x_1265, 1);
x_2348 = lean::cnstr_get(x_1265, 2);
x_2349 = lean::cnstr_get(x_1265, 3);
x_2350 = lean::cnstr_get(x_4, 1);
x_2351 = lean::cnstr_get(x_4, 2);
lean::inc(x_2351);
lean::inc(x_2350);
lean::dec(x_4);
x_2352 = lean::cnstr_get(x_1890, 0);
lean::inc(x_2352);
x_2353 = lean::cnstr_get(x_1890, 1);
lean::inc(x_2353);
x_2354 = lean::cnstr_get(x_1890, 2);
lean::inc(x_2354);
x_2355 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2355);
if (lean::is_exclusive(x_1890)) {
 lean::cnstr_release(x_1890, 0);
 lean::cnstr_release(x_1890, 1);
 lean::cnstr_release(x_1890, 2);
 lean::cnstr_release(x_1890, 3);
 x_2356 = x_1890;
} else {
 lean::dec_ref(x_1890);
 x_2356 = lean::box(0);
}
if (lean::is_scalar(x_2356)) {
 x_2357 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2357 = x_2356;
}
lean::cnstr_set(x_2357, 0, x_2342);
lean::cnstr_set(x_2357, 1, x_2343);
lean::cnstr_set(x_2357, 2, x_2344);
lean::cnstr_set(x_2357, 3, x_2345);
lean::cnstr_set_uint8(x_2357, sizeof(void*)*4, x_2183);
x_2358 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2358, 0, x_2346);
lean::cnstr_set(x_2358, 1, x_2347);
lean::cnstr_set(x_2358, 2, x_2348);
lean::cnstr_set(x_2358, 3, x_2349);
lean::cnstr_set_uint8(x_2358, sizeof(void*)*4, x_2183);
lean::cnstr_set(x_1265, 3, x_2358);
lean::cnstr_set(x_1265, 2, x_2312);
lean::cnstr_set(x_1265, 1, x_2311);
lean::cnstr_set(x_1265, 0, x_2357);
lean::cnstr_set_uint8(x_1265, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_234, 3, x_2352);
lean::cnstr_set(x_234, 2, x_3);
lean::cnstr_set(x_234, 1, x_2);
lean::cnstr_set(x_234, 0, x_1265);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_2183);
lean::cnstr_set(x_1, 3, x_2096);
lean::cnstr_set(x_1, 2, x_2351);
lean::cnstr_set(x_1, 1, x_2350);
lean::cnstr_set(x_1, 0, x_2355);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2183);
x_2359 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2359, 0, x_234);
lean::cnstr_set(x_2359, 1, x_2353);
lean::cnstr_set(x_2359, 2, x_2354);
lean::cnstr_set(x_2359, 3, x_1);
lean::cnstr_set_uint8(x_2359, sizeof(void*)*4, x_2095);
return x_2359;
}
}
else
{
obj* x_2360; obj* x_2361; obj* x_2362; obj* x_2363; obj* x_2364; obj* x_2365; obj* x_2366; obj* x_2367; obj* x_2368; obj* x_2369; obj* x_2370; obj* x_2371; obj* x_2372; obj* x_2373; obj* x_2374; obj* x_2375; obj* x_2376; obj* x_2377; obj* x_2378; obj* x_2379; 
x_2360 = lean::cnstr_get(x_234, 0);
x_2361 = lean::cnstr_get(x_234, 1);
x_2362 = lean::cnstr_get(x_234, 2);
x_2363 = lean::cnstr_get(x_234, 3);
x_2364 = lean::cnstr_get(x_1265, 0);
x_2365 = lean::cnstr_get(x_1265, 1);
x_2366 = lean::cnstr_get(x_1265, 2);
x_2367 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2367);
lean::inc(x_2366);
lean::inc(x_2365);
lean::inc(x_2364);
lean::dec(x_1265);
x_2368 = lean::cnstr_get(x_4, 1);
lean::inc(x_2368);
x_2369 = lean::cnstr_get(x_4, 2);
lean::inc(x_2369);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_2370 = x_4;
} else {
 lean::dec_ref(x_4);
 x_2370 = lean::box(0);
}
x_2371 = lean::cnstr_get(x_1890, 0);
lean::inc(x_2371);
x_2372 = lean::cnstr_get(x_1890, 1);
lean::inc(x_2372);
x_2373 = lean::cnstr_get(x_1890, 2);
lean::inc(x_2373);
x_2374 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2374);
if (lean::is_exclusive(x_1890)) {
 lean::cnstr_release(x_1890, 0);
 lean::cnstr_release(x_1890, 1);
 lean::cnstr_release(x_1890, 2);
 lean::cnstr_release(x_1890, 3);
 x_2375 = x_1890;
} else {
 lean::dec_ref(x_1890);
 x_2375 = lean::box(0);
}
if (lean::is_scalar(x_2375)) {
 x_2376 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2376 = x_2375;
}
lean::cnstr_set(x_2376, 0, x_2360);
lean::cnstr_set(x_2376, 1, x_2361);
lean::cnstr_set(x_2376, 2, x_2362);
lean::cnstr_set(x_2376, 3, x_2363);
lean::cnstr_set_uint8(x_2376, sizeof(void*)*4, x_2183);
if (lean::is_scalar(x_2370)) {
 x_2377 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2377 = x_2370;
}
lean::cnstr_set(x_2377, 0, x_2364);
lean::cnstr_set(x_2377, 1, x_2365);
lean::cnstr_set(x_2377, 2, x_2366);
lean::cnstr_set(x_2377, 3, x_2367);
lean::cnstr_set_uint8(x_2377, sizeof(void*)*4, x_2183);
x_2378 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2378, 0, x_2376);
lean::cnstr_set(x_2378, 1, x_2311);
lean::cnstr_set(x_2378, 2, x_2312);
lean::cnstr_set(x_2378, 3, x_2377);
lean::cnstr_set_uint8(x_2378, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_234, 3, x_2371);
lean::cnstr_set(x_234, 2, x_3);
lean::cnstr_set(x_234, 1, x_2);
lean::cnstr_set(x_234, 0, x_2378);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_2183);
lean::cnstr_set(x_1, 3, x_2096);
lean::cnstr_set(x_1, 2, x_2369);
lean::cnstr_set(x_1, 1, x_2368);
lean::cnstr_set(x_1, 0, x_2374);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2183);
x_2379 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2379, 0, x_234);
lean::cnstr_set(x_2379, 1, x_2372);
lean::cnstr_set(x_2379, 2, x_2373);
lean::cnstr_set(x_2379, 3, x_1);
lean::cnstr_set_uint8(x_2379, sizeof(void*)*4, x_2095);
return x_2379;
}
}
else
{
obj* x_2380; obj* x_2381; obj* x_2382; obj* x_2383; obj* x_2384; obj* x_2385; obj* x_2386; obj* x_2387; obj* x_2388; obj* x_2389; obj* x_2390; obj* x_2391; obj* x_2392; obj* x_2393; obj* x_2394; obj* x_2395; obj* x_2396; obj* x_2397; obj* x_2398; obj* x_2399; obj* x_2400; obj* x_2401; 
x_2380 = lean::cnstr_get(x_234, 0);
x_2381 = lean::cnstr_get(x_234, 1);
x_2382 = lean::cnstr_get(x_234, 2);
x_2383 = lean::cnstr_get(x_234, 3);
lean::inc(x_2383);
lean::inc(x_2382);
lean::inc(x_2381);
lean::inc(x_2380);
lean::dec(x_234);
x_2384 = lean::cnstr_get(x_1265, 0);
lean::inc(x_2384);
x_2385 = lean::cnstr_get(x_1265, 1);
lean::inc(x_2385);
x_2386 = lean::cnstr_get(x_1265, 2);
lean::inc(x_2386);
x_2387 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2387);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2388 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2388 = lean::box(0);
}
x_2389 = lean::cnstr_get(x_4, 1);
lean::inc(x_2389);
x_2390 = lean::cnstr_get(x_4, 2);
lean::inc(x_2390);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_2391 = x_4;
} else {
 lean::dec_ref(x_4);
 x_2391 = lean::box(0);
}
x_2392 = lean::cnstr_get(x_1890, 0);
lean::inc(x_2392);
x_2393 = lean::cnstr_get(x_1890, 1);
lean::inc(x_2393);
x_2394 = lean::cnstr_get(x_1890, 2);
lean::inc(x_2394);
x_2395 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2395);
if (lean::is_exclusive(x_1890)) {
 lean::cnstr_release(x_1890, 0);
 lean::cnstr_release(x_1890, 1);
 lean::cnstr_release(x_1890, 2);
 lean::cnstr_release(x_1890, 3);
 x_2396 = x_1890;
} else {
 lean::dec_ref(x_1890);
 x_2396 = lean::box(0);
}
if (lean::is_scalar(x_2396)) {
 x_2397 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2397 = x_2396;
}
lean::cnstr_set(x_2397, 0, x_2380);
lean::cnstr_set(x_2397, 1, x_2381);
lean::cnstr_set(x_2397, 2, x_2382);
lean::cnstr_set(x_2397, 3, x_2383);
lean::cnstr_set_uint8(x_2397, sizeof(void*)*4, x_2183);
if (lean::is_scalar(x_2391)) {
 x_2398 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2398 = x_2391;
}
lean::cnstr_set(x_2398, 0, x_2384);
lean::cnstr_set(x_2398, 1, x_2385);
lean::cnstr_set(x_2398, 2, x_2386);
lean::cnstr_set(x_2398, 3, x_2387);
lean::cnstr_set_uint8(x_2398, sizeof(void*)*4, x_2183);
if (lean::is_scalar(x_2388)) {
 x_2399 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2399 = x_2388;
}
lean::cnstr_set(x_2399, 0, x_2397);
lean::cnstr_set(x_2399, 1, x_2311);
lean::cnstr_set(x_2399, 2, x_2312);
lean::cnstr_set(x_2399, 3, x_2398);
lean::cnstr_set_uint8(x_2399, sizeof(void*)*4, x_2095);
x_2400 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2400, 0, x_2399);
lean::cnstr_set(x_2400, 1, x_2);
lean::cnstr_set(x_2400, 2, x_3);
lean::cnstr_set(x_2400, 3, x_2392);
lean::cnstr_set_uint8(x_2400, sizeof(void*)*4, x_2183);
lean::cnstr_set(x_1, 3, x_2096);
lean::cnstr_set(x_1, 2, x_2390);
lean::cnstr_set(x_1, 1, x_2389);
lean::cnstr_set(x_1, 0, x_2395);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2183);
x_2401 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2401, 0, x_2400);
lean::cnstr_set(x_2401, 1, x_2393);
lean::cnstr_set(x_2401, 2, x_2394);
lean::cnstr_set(x_2401, 3, x_1);
lean::cnstr_set_uint8(x_2401, sizeof(void*)*4, x_2095);
return x_2401;
}
}
else
{
obj* x_2402; obj* x_2403; obj* x_2404; obj* x_2405; obj* x_2406; obj* x_2407; obj* x_2408; obj* x_2409; obj* x_2410; obj* x_2411; obj* x_2412; obj* x_2413; obj* x_2414; obj* x_2415; obj* x_2416; obj* x_2417; obj* x_2418; obj* x_2419; obj* x_2420; obj* x_2421; obj* x_2422; obj* x_2423; obj* x_2424; obj* x_2425; obj* x_2426; obj* x_2427; 
x_2402 = lean::cnstr_get(x_1, 1);
x_2403 = lean::cnstr_get(x_1, 2);
lean::inc(x_2403);
lean::inc(x_2402);
lean::dec(x_1);
x_2404 = lean::cnstr_get(x_234, 0);
lean::inc(x_2404);
x_2405 = lean::cnstr_get(x_234, 1);
lean::inc(x_2405);
x_2406 = lean::cnstr_get(x_234, 2);
lean::inc(x_2406);
x_2407 = lean::cnstr_get(x_234, 3);
lean::inc(x_2407);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_2408 = x_234;
} else {
 lean::dec_ref(x_234);
 x_2408 = lean::box(0);
}
x_2409 = lean::cnstr_get(x_1265, 0);
lean::inc(x_2409);
x_2410 = lean::cnstr_get(x_1265, 1);
lean::inc(x_2410);
x_2411 = lean::cnstr_get(x_1265, 2);
lean::inc(x_2411);
x_2412 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2412);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2413 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2413 = lean::box(0);
}
x_2414 = lean::cnstr_get(x_4, 1);
lean::inc(x_2414);
x_2415 = lean::cnstr_get(x_4, 2);
lean::inc(x_2415);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_2416 = x_4;
} else {
 lean::dec_ref(x_4);
 x_2416 = lean::box(0);
}
x_2417 = lean::cnstr_get(x_1890, 0);
lean::inc(x_2417);
x_2418 = lean::cnstr_get(x_1890, 1);
lean::inc(x_2418);
x_2419 = lean::cnstr_get(x_1890, 2);
lean::inc(x_2419);
x_2420 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2420);
if (lean::is_exclusive(x_1890)) {
 lean::cnstr_release(x_1890, 0);
 lean::cnstr_release(x_1890, 1);
 lean::cnstr_release(x_1890, 2);
 lean::cnstr_release(x_1890, 3);
 x_2421 = x_1890;
} else {
 lean::dec_ref(x_1890);
 x_2421 = lean::box(0);
}
if (lean::is_scalar(x_2421)) {
 x_2422 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2422 = x_2421;
}
lean::cnstr_set(x_2422, 0, x_2404);
lean::cnstr_set(x_2422, 1, x_2405);
lean::cnstr_set(x_2422, 2, x_2406);
lean::cnstr_set(x_2422, 3, x_2407);
lean::cnstr_set_uint8(x_2422, sizeof(void*)*4, x_2183);
if (lean::is_scalar(x_2416)) {
 x_2423 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2423 = x_2416;
}
lean::cnstr_set(x_2423, 0, x_2409);
lean::cnstr_set(x_2423, 1, x_2410);
lean::cnstr_set(x_2423, 2, x_2411);
lean::cnstr_set(x_2423, 3, x_2412);
lean::cnstr_set_uint8(x_2423, sizeof(void*)*4, x_2183);
if (lean::is_scalar(x_2413)) {
 x_2424 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2424 = x_2413;
}
lean::cnstr_set(x_2424, 0, x_2422);
lean::cnstr_set(x_2424, 1, x_2402);
lean::cnstr_set(x_2424, 2, x_2403);
lean::cnstr_set(x_2424, 3, x_2423);
lean::cnstr_set_uint8(x_2424, sizeof(void*)*4, x_2095);
if (lean::is_scalar(x_2408)) {
 x_2425 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2425 = x_2408;
}
lean::cnstr_set(x_2425, 0, x_2424);
lean::cnstr_set(x_2425, 1, x_2);
lean::cnstr_set(x_2425, 2, x_3);
lean::cnstr_set(x_2425, 3, x_2417);
lean::cnstr_set_uint8(x_2425, sizeof(void*)*4, x_2183);
x_2426 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2426, 0, x_2420);
lean::cnstr_set(x_2426, 1, x_2414);
lean::cnstr_set(x_2426, 2, x_2415);
lean::cnstr_set(x_2426, 3, x_2096);
lean::cnstr_set_uint8(x_2426, sizeof(void*)*4, x_2183);
x_2427 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2427, 0, x_2425);
lean::cnstr_set(x_2427, 1, x_2418);
lean::cnstr_set(x_2427, 2, x_2419);
lean::cnstr_set(x_2427, 3, x_2426);
lean::cnstr_set_uint8(x_2427, sizeof(void*)*4, x_2095);
return x_2427;
}
}
}
}
else
{
obj* x_2428; 
x_2428 = lean::cnstr_get(x_4, 3);
lean::inc(x_2428);
if (lean::obj_tag(x_2428) == 0)
{
uint8 x_2429; 
x_2429 = !lean::is_exclusive(x_1890);
if (x_2429 == 0)
{
obj* x_2430; obj* x_2431; obj* x_2432; obj* x_2433; uint8 x_2434; 
x_2430 = lean::cnstr_get(x_1890, 3);
lean::dec(x_2430);
x_2431 = lean::cnstr_get(x_1890, 2);
lean::dec(x_2431);
x_2432 = lean::cnstr_get(x_1890, 1);
lean::dec(x_2432);
x_2433 = lean::cnstr_get(x_1890, 0);
lean::dec(x_2433);
x_2434 = !lean::is_exclusive(x_1);
if (x_2434 == 0)
{
obj* x_2435; obj* x_2436; obj* x_2437; obj* x_2438; uint8 x_2439; 
x_2435 = lean::cnstr_get(x_1, 1);
x_2436 = lean::cnstr_get(x_1, 2);
x_2437 = lean::cnstr_get(x_1, 3);
lean::dec(x_2437);
x_2438 = lean::cnstr_get(x_1, 0);
lean::dec(x_2438);
x_2439 = !lean::is_exclusive(x_234);
if (x_2439 == 0)
{
uint8 x_2440; 
x_2440 = !lean::is_exclusive(x_1265);
if (x_2440 == 0)
{
obj* x_2441; obj* x_2442; obj* x_2443; obj* x_2444; 
x_2441 = lean::cnstr_get(x_234, 0);
x_2442 = lean::cnstr_get(x_234, 1);
x_2443 = lean::cnstr_get(x_234, 2);
x_2444 = lean::cnstr_get(x_234, 3);
lean::cnstr_set(x_1890, 3, x_2444);
lean::cnstr_set(x_1890, 2, x_2443);
lean::cnstr_set(x_1890, 1, x_2442);
lean::cnstr_set(x_1890, 0, x_2441);
lean::cnstr_set_uint8(x_1265, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_234, 3, x_1265);
lean::cnstr_set(x_234, 2, x_2436);
lean::cnstr_set(x_234, 1, x_2435);
lean::cnstr_set(x_234, 0, x_1890);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
else
{
obj* x_2445; obj* x_2446; obj* x_2447; obj* x_2448; obj* x_2449; obj* x_2450; obj* x_2451; obj* x_2452; obj* x_2453; 
x_2445 = lean::cnstr_get(x_234, 0);
x_2446 = lean::cnstr_get(x_234, 1);
x_2447 = lean::cnstr_get(x_234, 2);
x_2448 = lean::cnstr_get(x_234, 3);
x_2449 = lean::cnstr_get(x_1265, 0);
x_2450 = lean::cnstr_get(x_1265, 1);
x_2451 = lean::cnstr_get(x_1265, 2);
x_2452 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2452);
lean::inc(x_2451);
lean::inc(x_2450);
lean::inc(x_2449);
lean::dec(x_1265);
lean::cnstr_set(x_1890, 3, x_2448);
lean::cnstr_set(x_1890, 2, x_2447);
lean::cnstr_set(x_1890, 1, x_2446);
lean::cnstr_set(x_1890, 0, x_2445);
x_2453 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2453, 0, x_2449);
lean::cnstr_set(x_2453, 1, x_2450);
lean::cnstr_set(x_2453, 2, x_2451);
lean::cnstr_set(x_2453, 3, x_2452);
lean::cnstr_set_uint8(x_2453, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_234, 3, x_2453);
lean::cnstr_set(x_234, 2, x_2436);
lean::cnstr_set(x_234, 1, x_2435);
lean::cnstr_set(x_234, 0, x_1890);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
}
else
{
obj* x_2454; obj* x_2455; obj* x_2456; obj* x_2457; obj* x_2458; obj* x_2459; obj* x_2460; obj* x_2461; obj* x_2462; obj* x_2463; obj* x_2464; 
x_2454 = lean::cnstr_get(x_234, 0);
x_2455 = lean::cnstr_get(x_234, 1);
x_2456 = lean::cnstr_get(x_234, 2);
x_2457 = lean::cnstr_get(x_234, 3);
lean::inc(x_2457);
lean::inc(x_2456);
lean::inc(x_2455);
lean::inc(x_2454);
lean::dec(x_234);
x_2458 = lean::cnstr_get(x_1265, 0);
lean::inc(x_2458);
x_2459 = lean::cnstr_get(x_1265, 1);
lean::inc(x_2459);
x_2460 = lean::cnstr_get(x_1265, 2);
lean::inc(x_2460);
x_2461 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2461);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2462 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2462 = lean::box(0);
}
lean::cnstr_set(x_1890, 3, x_2457);
lean::cnstr_set(x_1890, 2, x_2456);
lean::cnstr_set(x_1890, 1, x_2455);
lean::cnstr_set(x_1890, 0, x_2454);
if (lean::is_scalar(x_2462)) {
 x_2463 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2463 = x_2462;
}
lean::cnstr_set(x_2463, 0, x_2458);
lean::cnstr_set(x_2463, 1, x_2459);
lean::cnstr_set(x_2463, 2, x_2460);
lean::cnstr_set(x_2463, 3, x_2461);
lean::cnstr_set_uint8(x_2463, sizeof(void*)*4, x_2095);
x_2464 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2464, 0, x_1890);
lean::cnstr_set(x_2464, 1, x_2435);
lean::cnstr_set(x_2464, 2, x_2436);
lean::cnstr_set(x_2464, 3, x_2463);
lean::cnstr_set_uint8(x_2464, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_2464);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
}
else
{
obj* x_2465; obj* x_2466; obj* x_2467; obj* x_2468; obj* x_2469; obj* x_2470; obj* x_2471; obj* x_2472; obj* x_2473; obj* x_2474; obj* x_2475; obj* x_2476; obj* x_2477; obj* x_2478; obj* x_2479; 
x_2465 = lean::cnstr_get(x_1, 1);
x_2466 = lean::cnstr_get(x_1, 2);
lean::inc(x_2466);
lean::inc(x_2465);
lean::dec(x_1);
x_2467 = lean::cnstr_get(x_234, 0);
lean::inc(x_2467);
x_2468 = lean::cnstr_get(x_234, 1);
lean::inc(x_2468);
x_2469 = lean::cnstr_get(x_234, 2);
lean::inc(x_2469);
x_2470 = lean::cnstr_get(x_234, 3);
lean::inc(x_2470);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_2471 = x_234;
} else {
 lean::dec_ref(x_234);
 x_2471 = lean::box(0);
}
x_2472 = lean::cnstr_get(x_1265, 0);
lean::inc(x_2472);
x_2473 = lean::cnstr_get(x_1265, 1);
lean::inc(x_2473);
x_2474 = lean::cnstr_get(x_1265, 2);
lean::inc(x_2474);
x_2475 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2475);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2476 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2476 = lean::box(0);
}
lean::cnstr_set(x_1890, 3, x_2470);
lean::cnstr_set(x_1890, 2, x_2469);
lean::cnstr_set(x_1890, 1, x_2468);
lean::cnstr_set(x_1890, 0, x_2467);
if (lean::is_scalar(x_2476)) {
 x_2477 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2477 = x_2476;
}
lean::cnstr_set(x_2477, 0, x_2472);
lean::cnstr_set(x_2477, 1, x_2473);
lean::cnstr_set(x_2477, 2, x_2474);
lean::cnstr_set(x_2477, 3, x_2475);
lean::cnstr_set_uint8(x_2477, sizeof(void*)*4, x_2095);
if (lean::is_scalar(x_2471)) {
 x_2478 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2478 = x_2471;
}
lean::cnstr_set(x_2478, 0, x_1890);
lean::cnstr_set(x_2478, 1, x_2465);
lean::cnstr_set(x_2478, 2, x_2466);
lean::cnstr_set(x_2478, 3, x_2477);
lean::cnstr_set_uint8(x_2478, sizeof(void*)*4, x_1889);
x_2479 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2479, 0, x_2478);
lean::cnstr_set(x_2479, 1, x_2);
lean::cnstr_set(x_2479, 2, x_3);
lean::cnstr_set(x_2479, 3, x_4);
lean::cnstr_set_uint8(x_2479, sizeof(void*)*4, x_2095);
return x_2479;
}
}
else
{
obj* x_2480; obj* x_2481; obj* x_2482; obj* x_2483; obj* x_2484; obj* x_2485; obj* x_2486; obj* x_2487; obj* x_2488; obj* x_2489; obj* x_2490; obj* x_2491; obj* x_2492; obj* x_2493; obj* x_2494; obj* x_2495; obj* x_2496; 
lean::dec(x_1890);
x_2480 = lean::cnstr_get(x_1, 1);
lean::inc(x_2480);
x_2481 = lean::cnstr_get(x_1, 2);
lean::inc(x_2481);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_2482 = x_1;
} else {
 lean::dec_ref(x_1);
 x_2482 = lean::box(0);
}
x_2483 = lean::cnstr_get(x_234, 0);
lean::inc(x_2483);
x_2484 = lean::cnstr_get(x_234, 1);
lean::inc(x_2484);
x_2485 = lean::cnstr_get(x_234, 2);
lean::inc(x_2485);
x_2486 = lean::cnstr_get(x_234, 3);
lean::inc(x_2486);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_2487 = x_234;
} else {
 lean::dec_ref(x_234);
 x_2487 = lean::box(0);
}
x_2488 = lean::cnstr_get(x_1265, 0);
lean::inc(x_2488);
x_2489 = lean::cnstr_get(x_1265, 1);
lean::inc(x_2489);
x_2490 = lean::cnstr_get(x_1265, 2);
lean::inc(x_2490);
x_2491 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2491);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2492 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2492 = lean::box(0);
}
x_2493 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2493, 0, x_2483);
lean::cnstr_set(x_2493, 1, x_2484);
lean::cnstr_set(x_2493, 2, x_2485);
lean::cnstr_set(x_2493, 3, x_2486);
lean::cnstr_set_uint8(x_2493, sizeof(void*)*4, x_2095);
if (lean::is_scalar(x_2492)) {
 x_2494 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2494 = x_2492;
}
lean::cnstr_set(x_2494, 0, x_2488);
lean::cnstr_set(x_2494, 1, x_2489);
lean::cnstr_set(x_2494, 2, x_2490);
lean::cnstr_set(x_2494, 3, x_2491);
lean::cnstr_set_uint8(x_2494, sizeof(void*)*4, x_2095);
if (lean::is_scalar(x_2487)) {
 x_2495 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2495 = x_2487;
}
lean::cnstr_set(x_2495, 0, x_2493);
lean::cnstr_set(x_2495, 1, x_2480);
lean::cnstr_set(x_2495, 2, x_2481);
lean::cnstr_set(x_2495, 3, x_2494);
lean::cnstr_set_uint8(x_2495, sizeof(void*)*4, x_1889);
if (lean::is_scalar(x_2482)) {
 x_2496 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2496 = x_2482;
}
lean::cnstr_set(x_2496, 0, x_2495);
lean::cnstr_set(x_2496, 1, x_2);
lean::cnstr_set(x_2496, 2, x_3);
lean::cnstr_set(x_2496, 3, x_4);
lean::cnstr_set_uint8(x_2496, sizeof(void*)*4, x_2095);
return x_2496;
}
}
else
{
uint8 x_2497; 
x_2497 = lean::cnstr_get_uint8(x_2428, sizeof(void*)*4);
if (x_2497 == 0)
{
uint8 x_2498; 
x_2498 = !lean::is_exclusive(x_1);
if (x_2498 == 0)
{
obj* x_2499; obj* x_2500; obj* x_2501; obj* x_2502; uint8 x_2503; 
x_2499 = lean::cnstr_get(x_1, 1);
x_2500 = lean::cnstr_get(x_1, 2);
x_2501 = lean::cnstr_get(x_1, 3);
lean::dec(x_2501);
x_2502 = lean::cnstr_get(x_1, 0);
lean::dec(x_2502);
x_2503 = !lean::is_exclusive(x_234);
if (x_2503 == 0)
{
uint8 x_2504; 
x_2504 = !lean::is_exclusive(x_1265);
if (x_2504 == 0)
{
uint8 x_2505; 
x_2505 = !lean::is_exclusive(x_4);
if (x_2505 == 0)
{
obj* x_2506; obj* x_2507; obj* x_2508; obj* x_2509; obj* x_2510; obj* x_2511; obj* x_2512; obj* x_2513; obj* x_2514; obj* x_2515; obj* x_2516; obj* x_2517; uint8 x_2518; 
x_2506 = lean::cnstr_get(x_234, 0);
x_2507 = lean::cnstr_get(x_234, 1);
x_2508 = lean::cnstr_get(x_234, 2);
x_2509 = lean::cnstr_get(x_234, 3);
x_2510 = lean::cnstr_get(x_1265, 0);
x_2511 = lean::cnstr_get(x_1265, 1);
x_2512 = lean::cnstr_get(x_1265, 2);
x_2513 = lean::cnstr_get(x_1265, 3);
x_2514 = lean::cnstr_get(x_4, 1);
x_2515 = lean::cnstr_get(x_4, 2);
x_2516 = lean::cnstr_get(x_4, 3);
lean::dec(x_2516);
x_2517 = lean::cnstr_get(x_4, 0);
lean::dec(x_2517);
x_2518 = !lean::is_exclusive(x_2428);
if (x_2518 == 0)
{
obj* x_2519; obj* x_2520; obj* x_2521; obj* x_2522; obj* x_2523; 
x_2519 = lean::cnstr_get(x_2428, 0);
x_2520 = lean::cnstr_get(x_2428, 1);
x_2521 = lean::cnstr_get(x_2428, 2);
x_2522 = lean::cnstr_get(x_2428, 3);
lean::cnstr_set(x_2428, 3, x_2509);
lean::cnstr_set(x_2428, 2, x_2508);
lean::cnstr_set(x_2428, 1, x_2507);
lean::cnstr_set(x_2428, 0, x_2506);
lean::cnstr_set_uint8(x_2428, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_4, 3, x_2513);
lean::cnstr_set(x_4, 2, x_2512);
lean::cnstr_set(x_4, 1, x_2511);
lean::cnstr_set(x_4, 0, x_2510);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_1265, 3, x_4);
lean::cnstr_set(x_1265, 2, x_2500);
lean::cnstr_set(x_1265, 1, x_2499);
lean::cnstr_set(x_1265, 0, x_2428);
lean::cnstr_set_uint8(x_1265, sizeof(void*)*4, x_2497);
lean::cnstr_set(x_234, 3, x_1890);
lean::cnstr_set(x_234, 2, x_3);
lean::cnstr_set(x_234, 1, x_2);
lean::cnstr_set(x_234, 0, x_1265);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_1, 3, x_2522);
lean::cnstr_set(x_1, 2, x_2521);
lean::cnstr_set(x_1, 1, x_2520);
lean::cnstr_set(x_1, 0, x_2519);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2095);
x_2523 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2523, 0, x_234);
lean::cnstr_set(x_2523, 1, x_2514);
lean::cnstr_set(x_2523, 2, x_2515);
lean::cnstr_set(x_2523, 3, x_1);
lean::cnstr_set_uint8(x_2523, sizeof(void*)*4, x_2497);
return x_2523;
}
else
{
obj* x_2524; obj* x_2525; obj* x_2526; obj* x_2527; obj* x_2528; obj* x_2529; 
x_2524 = lean::cnstr_get(x_2428, 0);
x_2525 = lean::cnstr_get(x_2428, 1);
x_2526 = lean::cnstr_get(x_2428, 2);
x_2527 = lean::cnstr_get(x_2428, 3);
lean::inc(x_2527);
lean::inc(x_2526);
lean::inc(x_2525);
lean::inc(x_2524);
lean::dec(x_2428);
x_2528 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2528, 0, x_2506);
lean::cnstr_set(x_2528, 1, x_2507);
lean::cnstr_set(x_2528, 2, x_2508);
lean::cnstr_set(x_2528, 3, x_2509);
lean::cnstr_set_uint8(x_2528, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_4, 3, x_2513);
lean::cnstr_set(x_4, 2, x_2512);
lean::cnstr_set(x_4, 1, x_2511);
lean::cnstr_set(x_4, 0, x_2510);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_1265, 3, x_4);
lean::cnstr_set(x_1265, 2, x_2500);
lean::cnstr_set(x_1265, 1, x_2499);
lean::cnstr_set(x_1265, 0, x_2528);
lean::cnstr_set_uint8(x_1265, sizeof(void*)*4, x_2497);
lean::cnstr_set(x_234, 3, x_1890);
lean::cnstr_set(x_234, 2, x_3);
lean::cnstr_set(x_234, 1, x_2);
lean::cnstr_set(x_234, 0, x_1265);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_1, 3, x_2527);
lean::cnstr_set(x_1, 2, x_2526);
lean::cnstr_set(x_1, 1, x_2525);
lean::cnstr_set(x_1, 0, x_2524);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2095);
x_2529 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2529, 0, x_234);
lean::cnstr_set(x_2529, 1, x_2514);
lean::cnstr_set(x_2529, 2, x_2515);
lean::cnstr_set(x_2529, 3, x_1);
lean::cnstr_set_uint8(x_2529, sizeof(void*)*4, x_2497);
return x_2529;
}
}
else
{
obj* x_2530; obj* x_2531; obj* x_2532; obj* x_2533; obj* x_2534; obj* x_2535; obj* x_2536; obj* x_2537; obj* x_2538; obj* x_2539; obj* x_2540; obj* x_2541; obj* x_2542; obj* x_2543; obj* x_2544; obj* x_2545; obj* x_2546; obj* x_2547; 
x_2530 = lean::cnstr_get(x_234, 0);
x_2531 = lean::cnstr_get(x_234, 1);
x_2532 = lean::cnstr_get(x_234, 2);
x_2533 = lean::cnstr_get(x_234, 3);
x_2534 = lean::cnstr_get(x_1265, 0);
x_2535 = lean::cnstr_get(x_1265, 1);
x_2536 = lean::cnstr_get(x_1265, 2);
x_2537 = lean::cnstr_get(x_1265, 3);
x_2538 = lean::cnstr_get(x_4, 1);
x_2539 = lean::cnstr_get(x_4, 2);
lean::inc(x_2539);
lean::inc(x_2538);
lean::dec(x_4);
x_2540 = lean::cnstr_get(x_2428, 0);
lean::inc(x_2540);
x_2541 = lean::cnstr_get(x_2428, 1);
lean::inc(x_2541);
x_2542 = lean::cnstr_get(x_2428, 2);
lean::inc(x_2542);
x_2543 = lean::cnstr_get(x_2428, 3);
lean::inc(x_2543);
if (lean::is_exclusive(x_2428)) {
 lean::cnstr_release(x_2428, 0);
 lean::cnstr_release(x_2428, 1);
 lean::cnstr_release(x_2428, 2);
 lean::cnstr_release(x_2428, 3);
 x_2544 = x_2428;
} else {
 lean::dec_ref(x_2428);
 x_2544 = lean::box(0);
}
if (lean::is_scalar(x_2544)) {
 x_2545 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2545 = x_2544;
}
lean::cnstr_set(x_2545, 0, x_2530);
lean::cnstr_set(x_2545, 1, x_2531);
lean::cnstr_set(x_2545, 2, x_2532);
lean::cnstr_set(x_2545, 3, x_2533);
lean::cnstr_set_uint8(x_2545, sizeof(void*)*4, x_2095);
x_2546 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2546, 0, x_2534);
lean::cnstr_set(x_2546, 1, x_2535);
lean::cnstr_set(x_2546, 2, x_2536);
lean::cnstr_set(x_2546, 3, x_2537);
lean::cnstr_set_uint8(x_2546, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_1265, 3, x_2546);
lean::cnstr_set(x_1265, 2, x_2500);
lean::cnstr_set(x_1265, 1, x_2499);
lean::cnstr_set(x_1265, 0, x_2545);
lean::cnstr_set_uint8(x_1265, sizeof(void*)*4, x_2497);
lean::cnstr_set(x_234, 3, x_1890);
lean::cnstr_set(x_234, 2, x_3);
lean::cnstr_set(x_234, 1, x_2);
lean::cnstr_set(x_234, 0, x_1265);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_1, 3, x_2543);
lean::cnstr_set(x_1, 2, x_2542);
lean::cnstr_set(x_1, 1, x_2541);
lean::cnstr_set(x_1, 0, x_2540);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2095);
x_2547 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2547, 0, x_234);
lean::cnstr_set(x_2547, 1, x_2538);
lean::cnstr_set(x_2547, 2, x_2539);
lean::cnstr_set(x_2547, 3, x_1);
lean::cnstr_set_uint8(x_2547, sizeof(void*)*4, x_2497);
return x_2547;
}
}
else
{
obj* x_2548; obj* x_2549; obj* x_2550; obj* x_2551; obj* x_2552; obj* x_2553; obj* x_2554; obj* x_2555; obj* x_2556; obj* x_2557; obj* x_2558; obj* x_2559; obj* x_2560; obj* x_2561; obj* x_2562; obj* x_2563; obj* x_2564; obj* x_2565; obj* x_2566; obj* x_2567; 
x_2548 = lean::cnstr_get(x_234, 0);
x_2549 = lean::cnstr_get(x_234, 1);
x_2550 = lean::cnstr_get(x_234, 2);
x_2551 = lean::cnstr_get(x_234, 3);
x_2552 = lean::cnstr_get(x_1265, 0);
x_2553 = lean::cnstr_get(x_1265, 1);
x_2554 = lean::cnstr_get(x_1265, 2);
x_2555 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2555);
lean::inc(x_2554);
lean::inc(x_2553);
lean::inc(x_2552);
lean::dec(x_1265);
x_2556 = lean::cnstr_get(x_4, 1);
lean::inc(x_2556);
x_2557 = lean::cnstr_get(x_4, 2);
lean::inc(x_2557);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_2558 = x_4;
} else {
 lean::dec_ref(x_4);
 x_2558 = lean::box(0);
}
x_2559 = lean::cnstr_get(x_2428, 0);
lean::inc(x_2559);
x_2560 = lean::cnstr_get(x_2428, 1);
lean::inc(x_2560);
x_2561 = lean::cnstr_get(x_2428, 2);
lean::inc(x_2561);
x_2562 = lean::cnstr_get(x_2428, 3);
lean::inc(x_2562);
if (lean::is_exclusive(x_2428)) {
 lean::cnstr_release(x_2428, 0);
 lean::cnstr_release(x_2428, 1);
 lean::cnstr_release(x_2428, 2);
 lean::cnstr_release(x_2428, 3);
 x_2563 = x_2428;
} else {
 lean::dec_ref(x_2428);
 x_2563 = lean::box(0);
}
if (lean::is_scalar(x_2563)) {
 x_2564 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2564 = x_2563;
}
lean::cnstr_set(x_2564, 0, x_2548);
lean::cnstr_set(x_2564, 1, x_2549);
lean::cnstr_set(x_2564, 2, x_2550);
lean::cnstr_set(x_2564, 3, x_2551);
lean::cnstr_set_uint8(x_2564, sizeof(void*)*4, x_2095);
if (lean::is_scalar(x_2558)) {
 x_2565 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2565 = x_2558;
}
lean::cnstr_set(x_2565, 0, x_2552);
lean::cnstr_set(x_2565, 1, x_2553);
lean::cnstr_set(x_2565, 2, x_2554);
lean::cnstr_set(x_2565, 3, x_2555);
lean::cnstr_set_uint8(x_2565, sizeof(void*)*4, x_2095);
x_2566 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2566, 0, x_2564);
lean::cnstr_set(x_2566, 1, x_2499);
lean::cnstr_set(x_2566, 2, x_2500);
lean::cnstr_set(x_2566, 3, x_2565);
lean::cnstr_set_uint8(x_2566, sizeof(void*)*4, x_2497);
lean::cnstr_set(x_234, 3, x_1890);
lean::cnstr_set(x_234, 2, x_3);
lean::cnstr_set(x_234, 1, x_2);
lean::cnstr_set(x_234, 0, x_2566);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_1, 3, x_2562);
lean::cnstr_set(x_1, 2, x_2561);
lean::cnstr_set(x_1, 1, x_2560);
lean::cnstr_set(x_1, 0, x_2559);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2095);
x_2567 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2567, 0, x_234);
lean::cnstr_set(x_2567, 1, x_2556);
lean::cnstr_set(x_2567, 2, x_2557);
lean::cnstr_set(x_2567, 3, x_1);
lean::cnstr_set_uint8(x_2567, sizeof(void*)*4, x_2497);
return x_2567;
}
}
else
{
obj* x_2568; obj* x_2569; obj* x_2570; obj* x_2571; obj* x_2572; obj* x_2573; obj* x_2574; obj* x_2575; obj* x_2576; obj* x_2577; obj* x_2578; obj* x_2579; obj* x_2580; obj* x_2581; obj* x_2582; obj* x_2583; obj* x_2584; obj* x_2585; obj* x_2586; obj* x_2587; obj* x_2588; obj* x_2589; 
x_2568 = lean::cnstr_get(x_234, 0);
x_2569 = lean::cnstr_get(x_234, 1);
x_2570 = lean::cnstr_get(x_234, 2);
x_2571 = lean::cnstr_get(x_234, 3);
lean::inc(x_2571);
lean::inc(x_2570);
lean::inc(x_2569);
lean::inc(x_2568);
lean::dec(x_234);
x_2572 = lean::cnstr_get(x_1265, 0);
lean::inc(x_2572);
x_2573 = lean::cnstr_get(x_1265, 1);
lean::inc(x_2573);
x_2574 = lean::cnstr_get(x_1265, 2);
lean::inc(x_2574);
x_2575 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2575);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2576 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2576 = lean::box(0);
}
x_2577 = lean::cnstr_get(x_4, 1);
lean::inc(x_2577);
x_2578 = lean::cnstr_get(x_4, 2);
lean::inc(x_2578);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_2579 = x_4;
} else {
 lean::dec_ref(x_4);
 x_2579 = lean::box(0);
}
x_2580 = lean::cnstr_get(x_2428, 0);
lean::inc(x_2580);
x_2581 = lean::cnstr_get(x_2428, 1);
lean::inc(x_2581);
x_2582 = lean::cnstr_get(x_2428, 2);
lean::inc(x_2582);
x_2583 = lean::cnstr_get(x_2428, 3);
lean::inc(x_2583);
if (lean::is_exclusive(x_2428)) {
 lean::cnstr_release(x_2428, 0);
 lean::cnstr_release(x_2428, 1);
 lean::cnstr_release(x_2428, 2);
 lean::cnstr_release(x_2428, 3);
 x_2584 = x_2428;
} else {
 lean::dec_ref(x_2428);
 x_2584 = lean::box(0);
}
if (lean::is_scalar(x_2584)) {
 x_2585 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2585 = x_2584;
}
lean::cnstr_set(x_2585, 0, x_2568);
lean::cnstr_set(x_2585, 1, x_2569);
lean::cnstr_set(x_2585, 2, x_2570);
lean::cnstr_set(x_2585, 3, x_2571);
lean::cnstr_set_uint8(x_2585, sizeof(void*)*4, x_2095);
if (lean::is_scalar(x_2579)) {
 x_2586 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2586 = x_2579;
}
lean::cnstr_set(x_2586, 0, x_2572);
lean::cnstr_set(x_2586, 1, x_2573);
lean::cnstr_set(x_2586, 2, x_2574);
lean::cnstr_set(x_2586, 3, x_2575);
lean::cnstr_set_uint8(x_2586, sizeof(void*)*4, x_2095);
if (lean::is_scalar(x_2576)) {
 x_2587 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2587 = x_2576;
}
lean::cnstr_set(x_2587, 0, x_2585);
lean::cnstr_set(x_2587, 1, x_2499);
lean::cnstr_set(x_2587, 2, x_2500);
lean::cnstr_set(x_2587, 3, x_2586);
lean::cnstr_set_uint8(x_2587, sizeof(void*)*4, x_2497);
x_2588 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2588, 0, x_2587);
lean::cnstr_set(x_2588, 1, x_2);
lean::cnstr_set(x_2588, 2, x_3);
lean::cnstr_set(x_2588, 3, x_1890);
lean::cnstr_set_uint8(x_2588, sizeof(void*)*4, x_2095);
lean::cnstr_set(x_1, 3, x_2583);
lean::cnstr_set(x_1, 2, x_2582);
lean::cnstr_set(x_1, 1, x_2581);
lean::cnstr_set(x_1, 0, x_2580);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2095);
x_2589 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2589, 0, x_2588);
lean::cnstr_set(x_2589, 1, x_2577);
lean::cnstr_set(x_2589, 2, x_2578);
lean::cnstr_set(x_2589, 3, x_1);
lean::cnstr_set_uint8(x_2589, sizeof(void*)*4, x_2497);
return x_2589;
}
}
else
{
obj* x_2590; obj* x_2591; obj* x_2592; obj* x_2593; obj* x_2594; obj* x_2595; obj* x_2596; obj* x_2597; obj* x_2598; obj* x_2599; obj* x_2600; obj* x_2601; obj* x_2602; obj* x_2603; obj* x_2604; obj* x_2605; obj* x_2606; obj* x_2607; obj* x_2608; obj* x_2609; obj* x_2610; obj* x_2611; obj* x_2612; obj* x_2613; obj* x_2614; obj* x_2615; 
x_2590 = lean::cnstr_get(x_1, 1);
x_2591 = lean::cnstr_get(x_1, 2);
lean::inc(x_2591);
lean::inc(x_2590);
lean::dec(x_1);
x_2592 = lean::cnstr_get(x_234, 0);
lean::inc(x_2592);
x_2593 = lean::cnstr_get(x_234, 1);
lean::inc(x_2593);
x_2594 = lean::cnstr_get(x_234, 2);
lean::inc(x_2594);
x_2595 = lean::cnstr_get(x_234, 3);
lean::inc(x_2595);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_2596 = x_234;
} else {
 lean::dec_ref(x_234);
 x_2596 = lean::box(0);
}
x_2597 = lean::cnstr_get(x_1265, 0);
lean::inc(x_2597);
x_2598 = lean::cnstr_get(x_1265, 1);
lean::inc(x_2598);
x_2599 = lean::cnstr_get(x_1265, 2);
lean::inc(x_2599);
x_2600 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2600);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2601 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2601 = lean::box(0);
}
x_2602 = lean::cnstr_get(x_4, 1);
lean::inc(x_2602);
x_2603 = lean::cnstr_get(x_4, 2);
lean::inc(x_2603);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_2604 = x_4;
} else {
 lean::dec_ref(x_4);
 x_2604 = lean::box(0);
}
x_2605 = lean::cnstr_get(x_2428, 0);
lean::inc(x_2605);
x_2606 = lean::cnstr_get(x_2428, 1);
lean::inc(x_2606);
x_2607 = lean::cnstr_get(x_2428, 2);
lean::inc(x_2607);
x_2608 = lean::cnstr_get(x_2428, 3);
lean::inc(x_2608);
if (lean::is_exclusive(x_2428)) {
 lean::cnstr_release(x_2428, 0);
 lean::cnstr_release(x_2428, 1);
 lean::cnstr_release(x_2428, 2);
 lean::cnstr_release(x_2428, 3);
 x_2609 = x_2428;
} else {
 lean::dec_ref(x_2428);
 x_2609 = lean::box(0);
}
if (lean::is_scalar(x_2609)) {
 x_2610 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2610 = x_2609;
}
lean::cnstr_set(x_2610, 0, x_2592);
lean::cnstr_set(x_2610, 1, x_2593);
lean::cnstr_set(x_2610, 2, x_2594);
lean::cnstr_set(x_2610, 3, x_2595);
lean::cnstr_set_uint8(x_2610, sizeof(void*)*4, x_2095);
if (lean::is_scalar(x_2604)) {
 x_2611 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2611 = x_2604;
}
lean::cnstr_set(x_2611, 0, x_2597);
lean::cnstr_set(x_2611, 1, x_2598);
lean::cnstr_set(x_2611, 2, x_2599);
lean::cnstr_set(x_2611, 3, x_2600);
lean::cnstr_set_uint8(x_2611, sizeof(void*)*4, x_2095);
if (lean::is_scalar(x_2601)) {
 x_2612 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2612 = x_2601;
}
lean::cnstr_set(x_2612, 0, x_2610);
lean::cnstr_set(x_2612, 1, x_2590);
lean::cnstr_set(x_2612, 2, x_2591);
lean::cnstr_set(x_2612, 3, x_2611);
lean::cnstr_set_uint8(x_2612, sizeof(void*)*4, x_2497);
if (lean::is_scalar(x_2596)) {
 x_2613 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2613 = x_2596;
}
lean::cnstr_set(x_2613, 0, x_2612);
lean::cnstr_set(x_2613, 1, x_2);
lean::cnstr_set(x_2613, 2, x_3);
lean::cnstr_set(x_2613, 3, x_1890);
lean::cnstr_set_uint8(x_2613, sizeof(void*)*4, x_2095);
x_2614 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2614, 0, x_2605);
lean::cnstr_set(x_2614, 1, x_2606);
lean::cnstr_set(x_2614, 2, x_2607);
lean::cnstr_set(x_2614, 3, x_2608);
lean::cnstr_set_uint8(x_2614, sizeof(void*)*4, x_2095);
x_2615 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2615, 0, x_2613);
lean::cnstr_set(x_2615, 1, x_2602);
lean::cnstr_set(x_2615, 2, x_2603);
lean::cnstr_set(x_2615, 3, x_2614);
lean::cnstr_set_uint8(x_2615, sizeof(void*)*4, x_2497);
return x_2615;
}
}
else
{
uint8 x_2616; 
x_2616 = !lean::is_exclusive(x_1);
if (x_2616 == 0)
{
obj* x_2617; obj* x_2618; obj* x_2619; obj* x_2620; uint8 x_2621; 
x_2617 = lean::cnstr_get(x_1, 1);
x_2618 = lean::cnstr_get(x_1, 2);
x_2619 = lean::cnstr_get(x_1, 3);
lean::dec(x_2619);
x_2620 = lean::cnstr_get(x_1, 0);
lean::dec(x_2620);
x_2621 = !lean::is_exclusive(x_234);
if (x_2621 == 0)
{
uint8 x_2622; 
x_2622 = !lean::is_exclusive(x_1265);
if (x_2622 == 0)
{
uint8 x_2623; 
x_2623 = !lean::is_exclusive(x_4);
if (x_2623 == 0)
{
obj* x_2624; obj* x_2625; obj* x_2626; obj* x_2627; obj* x_2628; obj* x_2629; obj* x_2630; obj* x_2631; obj* x_2632; obj* x_2633; obj* x_2634; obj* x_2635; uint8 x_2636; 
x_2624 = lean::cnstr_get(x_234, 0);
x_2625 = lean::cnstr_get(x_234, 1);
x_2626 = lean::cnstr_get(x_234, 2);
x_2627 = lean::cnstr_get(x_234, 3);
x_2628 = lean::cnstr_get(x_1265, 0);
x_2629 = lean::cnstr_get(x_1265, 1);
x_2630 = lean::cnstr_get(x_1265, 2);
x_2631 = lean::cnstr_get(x_1265, 3);
x_2632 = lean::cnstr_get(x_4, 1);
x_2633 = lean::cnstr_get(x_4, 2);
x_2634 = lean::cnstr_get(x_4, 3);
lean::dec(x_2634);
x_2635 = lean::cnstr_get(x_4, 0);
lean::dec(x_2635);
x_2636 = !lean::is_exclusive(x_1890);
if (x_2636 == 0)
{
obj* x_2637; obj* x_2638; obj* x_2639; obj* x_2640; obj* x_2641; 
x_2637 = lean::cnstr_get(x_1890, 0);
x_2638 = lean::cnstr_get(x_1890, 1);
x_2639 = lean::cnstr_get(x_1890, 2);
x_2640 = lean::cnstr_get(x_1890, 3);
lean::cnstr_set(x_1890, 3, x_2627);
lean::cnstr_set(x_1890, 2, x_2626);
lean::cnstr_set(x_1890, 1, x_2625);
lean::cnstr_set(x_1890, 0, x_2624);
lean::cnstr_set_uint8(x_1890, sizeof(void*)*4, x_2497);
lean::cnstr_set(x_4, 3, x_2631);
lean::cnstr_set(x_4, 2, x_2630);
lean::cnstr_set(x_4, 1, x_2629);
lean::cnstr_set(x_4, 0, x_2628);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2497);
lean::cnstr_set(x_1265, 3, x_4);
lean::cnstr_set(x_1265, 2, x_2618);
lean::cnstr_set(x_1265, 1, x_2617);
lean::cnstr_set(x_1265, 0, x_1890);
lean::cnstr_set_uint8(x_1265, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_234, 3, x_2640);
lean::cnstr_set(x_234, 2, x_2639);
lean::cnstr_set(x_234, 1, x_2638);
lean::cnstr_set(x_234, 0, x_2637);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_2497);
lean::cnstr_set(x_1, 3, x_2428);
lean::cnstr_set(x_1, 2, x_2633);
lean::cnstr_set(x_1, 1, x_2632);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_2641 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2641, 0, x_1265);
lean::cnstr_set(x_2641, 1, x_2);
lean::cnstr_set(x_2641, 2, x_3);
lean::cnstr_set(x_2641, 3, x_1);
lean::cnstr_set_uint8(x_2641, sizeof(void*)*4, x_2497);
return x_2641;
}
else
{
obj* x_2642; obj* x_2643; obj* x_2644; obj* x_2645; obj* x_2646; obj* x_2647; 
x_2642 = lean::cnstr_get(x_1890, 0);
x_2643 = lean::cnstr_get(x_1890, 1);
x_2644 = lean::cnstr_get(x_1890, 2);
x_2645 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2645);
lean::inc(x_2644);
lean::inc(x_2643);
lean::inc(x_2642);
lean::dec(x_1890);
x_2646 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2646, 0, x_2624);
lean::cnstr_set(x_2646, 1, x_2625);
lean::cnstr_set(x_2646, 2, x_2626);
lean::cnstr_set(x_2646, 3, x_2627);
lean::cnstr_set_uint8(x_2646, sizeof(void*)*4, x_2497);
lean::cnstr_set(x_4, 3, x_2631);
lean::cnstr_set(x_4, 2, x_2630);
lean::cnstr_set(x_4, 1, x_2629);
lean::cnstr_set(x_4, 0, x_2628);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2497);
lean::cnstr_set(x_1265, 3, x_4);
lean::cnstr_set(x_1265, 2, x_2618);
lean::cnstr_set(x_1265, 1, x_2617);
lean::cnstr_set(x_1265, 0, x_2646);
lean::cnstr_set_uint8(x_1265, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_234, 3, x_2645);
lean::cnstr_set(x_234, 2, x_2644);
lean::cnstr_set(x_234, 1, x_2643);
lean::cnstr_set(x_234, 0, x_2642);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_2497);
lean::cnstr_set(x_1, 3, x_2428);
lean::cnstr_set(x_1, 2, x_2633);
lean::cnstr_set(x_1, 1, x_2632);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_2647 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2647, 0, x_1265);
lean::cnstr_set(x_2647, 1, x_2);
lean::cnstr_set(x_2647, 2, x_3);
lean::cnstr_set(x_2647, 3, x_1);
lean::cnstr_set_uint8(x_2647, sizeof(void*)*4, x_2497);
return x_2647;
}
}
else
{
obj* x_2648; obj* x_2649; obj* x_2650; obj* x_2651; obj* x_2652; obj* x_2653; obj* x_2654; obj* x_2655; obj* x_2656; obj* x_2657; obj* x_2658; obj* x_2659; obj* x_2660; obj* x_2661; obj* x_2662; obj* x_2663; obj* x_2664; obj* x_2665; 
x_2648 = lean::cnstr_get(x_234, 0);
x_2649 = lean::cnstr_get(x_234, 1);
x_2650 = lean::cnstr_get(x_234, 2);
x_2651 = lean::cnstr_get(x_234, 3);
x_2652 = lean::cnstr_get(x_1265, 0);
x_2653 = lean::cnstr_get(x_1265, 1);
x_2654 = lean::cnstr_get(x_1265, 2);
x_2655 = lean::cnstr_get(x_1265, 3);
x_2656 = lean::cnstr_get(x_4, 1);
x_2657 = lean::cnstr_get(x_4, 2);
lean::inc(x_2657);
lean::inc(x_2656);
lean::dec(x_4);
x_2658 = lean::cnstr_get(x_1890, 0);
lean::inc(x_2658);
x_2659 = lean::cnstr_get(x_1890, 1);
lean::inc(x_2659);
x_2660 = lean::cnstr_get(x_1890, 2);
lean::inc(x_2660);
x_2661 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2661);
if (lean::is_exclusive(x_1890)) {
 lean::cnstr_release(x_1890, 0);
 lean::cnstr_release(x_1890, 1);
 lean::cnstr_release(x_1890, 2);
 lean::cnstr_release(x_1890, 3);
 x_2662 = x_1890;
} else {
 lean::dec_ref(x_1890);
 x_2662 = lean::box(0);
}
if (lean::is_scalar(x_2662)) {
 x_2663 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2663 = x_2662;
}
lean::cnstr_set(x_2663, 0, x_2648);
lean::cnstr_set(x_2663, 1, x_2649);
lean::cnstr_set(x_2663, 2, x_2650);
lean::cnstr_set(x_2663, 3, x_2651);
lean::cnstr_set_uint8(x_2663, sizeof(void*)*4, x_2497);
x_2664 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2664, 0, x_2652);
lean::cnstr_set(x_2664, 1, x_2653);
lean::cnstr_set(x_2664, 2, x_2654);
lean::cnstr_set(x_2664, 3, x_2655);
lean::cnstr_set_uint8(x_2664, sizeof(void*)*4, x_2497);
lean::cnstr_set(x_1265, 3, x_2664);
lean::cnstr_set(x_1265, 2, x_2618);
lean::cnstr_set(x_1265, 1, x_2617);
lean::cnstr_set(x_1265, 0, x_2663);
lean::cnstr_set_uint8(x_1265, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_234, 3, x_2661);
lean::cnstr_set(x_234, 2, x_2660);
lean::cnstr_set(x_234, 1, x_2659);
lean::cnstr_set(x_234, 0, x_2658);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_2497);
lean::cnstr_set(x_1, 3, x_2428);
lean::cnstr_set(x_1, 2, x_2657);
lean::cnstr_set(x_1, 1, x_2656);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_2665 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2665, 0, x_1265);
lean::cnstr_set(x_2665, 1, x_2);
lean::cnstr_set(x_2665, 2, x_3);
lean::cnstr_set(x_2665, 3, x_1);
lean::cnstr_set_uint8(x_2665, sizeof(void*)*4, x_2497);
return x_2665;
}
}
else
{
obj* x_2666; obj* x_2667; obj* x_2668; obj* x_2669; obj* x_2670; obj* x_2671; obj* x_2672; obj* x_2673; obj* x_2674; obj* x_2675; obj* x_2676; obj* x_2677; obj* x_2678; obj* x_2679; obj* x_2680; obj* x_2681; obj* x_2682; obj* x_2683; obj* x_2684; obj* x_2685; 
x_2666 = lean::cnstr_get(x_234, 0);
x_2667 = lean::cnstr_get(x_234, 1);
x_2668 = lean::cnstr_get(x_234, 2);
x_2669 = lean::cnstr_get(x_234, 3);
x_2670 = lean::cnstr_get(x_1265, 0);
x_2671 = lean::cnstr_get(x_1265, 1);
x_2672 = lean::cnstr_get(x_1265, 2);
x_2673 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2673);
lean::inc(x_2672);
lean::inc(x_2671);
lean::inc(x_2670);
lean::dec(x_1265);
x_2674 = lean::cnstr_get(x_4, 1);
lean::inc(x_2674);
x_2675 = lean::cnstr_get(x_4, 2);
lean::inc(x_2675);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_2676 = x_4;
} else {
 lean::dec_ref(x_4);
 x_2676 = lean::box(0);
}
x_2677 = lean::cnstr_get(x_1890, 0);
lean::inc(x_2677);
x_2678 = lean::cnstr_get(x_1890, 1);
lean::inc(x_2678);
x_2679 = lean::cnstr_get(x_1890, 2);
lean::inc(x_2679);
x_2680 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2680);
if (lean::is_exclusive(x_1890)) {
 lean::cnstr_release(x_1890, 0);
 lean::cnstr_release(x_1890, 1);
 lean::cnstr_release(x_1890, 2);
 lean::cnstr_release(x_1890, 3);
 x_2681 = x_1890;
} else {
 lean::dec_ref(x_1890);
 x_2681 = lean::box(0);
}
if (lean::is_scalar(x_2681)) {
 x_2682 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2682 = x_2681;
}
lean::cnstr_set(x_2682, 0, x_2666);
lean::cnstr_set(x_2682, 1, x_2667);
lean::cnstr_set(x_2682, 2, x_2668);
lean::cnstr_set(x_2682, 3, x_2669);
lean::cnstr_set_uint8(x_2682, sizeof(void*)*4, x_2497);
if (lean::is_scalar(x_2676)) {
 x_2683 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2683 = x_2676;
}
lean::cnstr_set(x_2683, 0, x_2670);
lean::cnstr_set(x_2683, 1, x_2671);
lean::cnstr_set(x_2683, 2, x_2672);
lean::cnstr_set(x_2683, 3, x_2673);
lean::cnstr_set_uint8(x_2683, sizeof(void*)*4, x_2497);
x_2684 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2684, 0, x_2682);
lean::cnstr_set(x_2684, 1, x_2617);
lean::cnstr_set(x_2684, 2, x_2618);
lean::cnstr_set(x_2684, 3, x_2683);
lean::cnstr_set_uint8(x_2684, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_234, 3, x_2680);
lean::cnstr_set(x_234, 2, x_2679);
lean::cnstr_set(x_234, 1, x_2678);
lean::cnstr_set(x_234, 0, x_2677);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_2497);
lean::cnstr_set(x_1, 3, x_2428);
lean::cnstr_set(x_1, 2, x_2675);
lean::cnstr_set(x_1, 1, x_2674);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_2685 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2685, 0, x_2684);
lean::cnstr_set(x_2685, 1, x_2);
lean::cnstr_set(x_2685, 2, x_3);
lean::cnstr_set(x_2685, 3, x_1);
lean::cnstr_set_uint8(x_2685, sizeof(void*)*4, x_2497);
return x_2685;
}
}
else
{
obj* x_2686; obj* x_2687; obj* x_2688; obj* x_2689; obj* x_2690; obj* x_2691; obj* x_2692; obj* x_2693; obj* x_2694; obj* x_2695; obj* x_2696; obj* x_2697; obj* x_2698; obj* x_2699; obj* x_2700; obj* x_2701; obj* x_2702; obj* x_2703; obj* x_2704; obj* x_2705; obj* x_2706; obj* x_2707; 
x_2686 = lean::cnstr_get(x_234, 0);
x_2687 = lean::cnstr_get(x_234, 1);
x_2688 = lean::cnstr_get(x_234, 2);
x_2689 = lean::cnstr_get(x_234, 3);
lean::inc(x_2689);
lean::inc(x_2688);
lean::inc(x_2687);
lean::inc(x_2686);
lean::dec(x_234);
x_2690 = lean::cnstr_get(x_1265, 0);
lean::inc(x_2690);
x_2691 = lean::cnstr_get(x_1265, 1);
lean::inc(x_2691);
x_2692 = lean::cnstr_get(x_1265, 2);
lean::inc(x_2692);
x_2693 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2693);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2694 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2694 = lean::box(0);
}
x_2695 = lean::cnstr_get(x_4, 1);
lean::inc(x_2695);
x_2696 = lean::cnstr_get(x_4, 2);
lean::inc(x_2696);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_2697 = x_4;
} else {
 lean::dec_ref(x_4);
 x_2697 = lean::box(0);
}
x_2698 = lean::cnstr_get(x_1890, 0);
lean::inc(x_2698);
x_2699 = lean::cnstr_get(x_1890, 1);
lean::inc(x_2699);
x_2700 = lean::cnstr_get(x_1890, 2);
lean::inc(x_2700);
x_2701 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2701);
if (lean::is_exclusive(x_1890)) {
 lean::cnstr_release(x_1890, 0);
 lean::cnstr_release(x_1890, 1);
 lean::cnstr_release(x_1890, 2);
 lean::cnstr_release(x_1890, 3);
 x_2702 = x_1890;
} else {
 lean::dec_ref(x_1890);
 x_2702 = lean::box(0);
}
if (lean::is_scalar(x_2702)) {
 x_2703 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2703 = x_2702;
}
lean::cnstr_set(x_2703, 0, x_2686);
lean::cnstr_set(x_2703, 1, x_2687);
lean::cnstr_set(x_2703, 2, x_2688);
lean::cnstr_set(x_2703, 3, x_2689);
lean::cnstr_set_uint8(x_2703, sizeof(void*)*4, x_2497);
if (lean::is_scalar(x_2697)) {
 x_2704 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2704 = x_2697;
}
lean::cnstr_set(x_2704, 0, x_2690);
lean::cnstr_set(x_2704, 1, x_2691);
lean::cnstr_set(x_2704, 2, x_2692);
lean::cnstr_set(x_2704, 3, x_2693);
lean::cnstr_set_uint8(x_2704, sizeof(void*)*4, x_2497);
if (lean::is_scalar(x_2694)) {
 x_2705 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2705 = x_2694;
}
lean::cnstr_set(x_2705, 0, x_2703);
lean::cnstr_set(x_2705, 1, x_2617);
lean::cnstr_set(x_2705, 2, x_2618);
lean::cnstr_set(x_2705, 3, x_2704);
lean::cnstr_set_uint8(x_2705, sizeof(void*)*4, x_1889);
x_2706 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2706, 0, x_2698);
lean::cnstr_set(x_2706, 1, x_2699);
lean::cnstr_set(x_2706, 2, x_2700);
lean::cnstr_set(x_2706, 3, x_2701);
lean::cnstr_set_uint8(x_2706, sizeof(void*)*4, x_2497);
lean::cnstr_set(x_1, 3, x_2428);
lean::cnstr_set(x_1, 2, x_2696);
lean::cnstr_set(x_1, 1, x_2695);
lean::cnstr_set(x_1, 0, x_2706);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_2707 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2707, 0, x_2705);
lean::cnstr_set(x_2707, 1, x_2);
lean::cnstr_set(x_2707, 2, x_3);
lean::cnstr_set(x_2707, 3, x_1);
lean::cnstr_set_uint8(x_2707, sizeof(void*)*4, x_2497);
return x_2707;
}
}
else
{
obj* x_2708; obj* x_2709; obj* x_2710; obj* x_2711; obj* x_2712; obj* x_2713; obj* x_2714; obj* x_2715; obj* x_2716; obj* x_2717; obj* x_2718; obj* x_2719; obj* x_2720; obj* x_2721; obj* x_2722; obj* x_2723; obj* x_2724; obj* x_2725; obj* x_2726; obj* x_2727; obj* x_2728; obj* x_2729; obj* x_2730; obj* x_2731; obj* x_2732; obj* x_2733; 
x_2708 = lean::cnstr_get(x_1, 1);
x_2709 = lean::cnstr_get(x_1, 2);
lean::inc(x_2709);
lean::inc(x_2708);
lean::dec(x_1);
x_2710 = lean::cnstr_get(x_234, 0);
lean::inc(x_2710);
x_2711 = lean::cnstr_get(x_234, 1);
lean::inc(x_2711);
x_2712 = lean::cnstr_get(x_234, 2);
lean::inc(x_2712);
x_2713 = lean::cnstr_get(x_234, 3);
lean::inc(x_2713);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_2714 = x_234;
} else {
 lean::dec_ref(x_234);
 x_2714 = lean::box(0);
}
x_2715 = lean::cnstr_get(x_1265, 0);
lean::inc(x_2715);
x_2716 = lean::cnstr_get(x_1265, 1);
lean::inc(x_2716);
x_2717 = lean::cnstr_get(x_1265, 2);
lean::inc(x_2717);
x_2718 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2718);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2719 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2719 = lean::box(0);
}
x_2720 = lean::cnstr_get(x_4, 1);
lean::inc(x_2720);
x_2721 = lean::cnstr_get(x_4, 2);
lean::inc(x_2721);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_2722 = x_4;
} else {
 lean::dec_ref(x_4);
 x_2722 = lean::box(0);
}
x_2723 = lean::cnstr_get(x_1890, 0);
lean::inc(x_2723);
x_2724 = lean::cnstr_get(x_1890, 1);
lean::inc(x_2724);
x_2725 = lean::cnstr_get(x_1890, 2);
lean::inc(x_2725);
x_2726 = lean::cnstr_get(x_1890, 3);
lean::inc(x_2726);
if (lean::is_exclusive(x_1890)) {
 lean::cnstr_release(x_1890, 0);
 lean::cnstr_release(x_1890, 1);
 lean::cnstr_release(x_1890, 2);
 lean::cnstr_release(x_1890, 3);
 x_2727 = x_1890;
} else {
 lean::dec_ref(x_1890);
 x_2727 = lean::box(0);
}
if (lean::is_scalar(x_2727)) {
 x_2728 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2728 = x_2727;
}
lean::cnstr_set(x_2728, 0, x_2710);
lean::cnstr_set(x_2728, 1, x_2711);
lean::cnstr_set(x_2728, 2, x_2712);
lean::cnstr_set(x_2728, 3, x_2713);
lean::cnstr_set_uint8(x_2728, sizeof(void*)*4, x_2497);
if (lean::is_scalar(x_2722)) {
 x_2729 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2729 = x_2722;
}
lean::cnstr_set(x_2729, 0, x_2715);
lean::cnstr_set(x_2729, 1, x_2716);
lean::cnstr_set(x_2729, 2, x_2717);
lean::cnstr_set(x_2729, 3, x_2718);
lean::cnstr_set_uint8(x_2729, sizeof(void*)*4, x_2497);
if (lean::is_scalar(x_2719)) {
 x_2730 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2730 = x_2719;
}
lean::cnstr_set(x_2730, 0, x_2728);
lean::cnstr_set(x_2730, 1, x_2708);
lean::cnstr_set(x_2730, 2, x_2709);
lean::cnstr_set(x_2730, 3, x_2729);
lean::cnstr_set_uint8(x_2730, sizeof(void*)*4, x_1889);
if (lean::is_scalar(x_2714)) {
 x_2731 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2731 = x_2714;
}
lean::cnstr_set(x_2731, 0, x_2723);
lean::cnstr_set(x_2731, 1, x_2724);
lean::cnstr_set(x_2731, 2, x_2725);
lean::cnstr_set(x_2731, 3, x_2726);
lean::cnstr_set_uint8(x_2731, sizeof(void*)*4, x_2497);
x_2732 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2732, 0, x_2731);
lean::cnstr_set(x_2732, 1, x_2720);
lean::cnstr_set(x_2732, 2, x_2721);
lean::cnstr_set(x_2732, 3, x_2428);
lean::cnstr_set_uint8(x_2732, sizeof(void*)*4, x_1889);
x_2733 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2733, 0, x_2730);
lean::cnstr_set(x_2733, 1, x_2);
lean::cnstr_set(x_2733, 2, x_3);
lean::cnstr_set(x_2733, 3, x_2732);
lean::cnstr_set_uint8(x_2733, sizeof(void*)*4, x_2497);
return x_2733;
}
}
}
}
}
}
else
{
uint8 x_2734; 
x_2734 = !lean::is_exclusive(x_1);
if (x_2734 == 0)
{
obj* x_2735; obj* x_2736; uint8 x_2737; 
x_2735 = lean::cnstr_get(x_1, 3);
lean::dec(x_2735);
x_2736 = lean::cnstr_get(x_1, 0);
lean::dec(x_2736);
x_2737 = !lean::is_exclusive(x_234);
if (x_2737 == 0)
{
uint8 x_2738; 
x_2738 = !lean::is_exclusive(x_1265);
if (x_2738 == 0)
{
obj* x_2739; obj* x_2740; obj* x_2741; obj* x_2742; obj* x_2743; obj* x_2744; obj* x_2745; obj* x_2746; obj* x_2747; 
x_2739 = lean::cnstr_get(x_234, 0);
x_2740 = lean::cnstr_get(x_234, 1);
x_2741 = lean::cnstr_get(x_234, 2);
x_2742 = lean::cnstr_get(x_234, 3);
x_2743 = lean::cnstr_get(x_1265, 0);
x_2744 = lean::cnstr_get(x_1265, 1);
x_2745 = lean::cnstr_get(x_1265, 2);
x_2746 = lean::cnstr_get(x_1265, 3);
lean::cnstr_set(x_1265, 3, x_2742);
lean::cnstr_set(x_1265, 2, x_2741);
lean::cnstr_set(x_1265, 1, x_2740);
lean::cnstr_set(x_1265, 0, x_2739);
lean::cnstr_set_uint8(x_1265, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_234, 3, x_2746);
lean::cnstr_set(x_234, 2, x_2745);
lean::cnstr_set(x_234, 1, x_2744);
lean::cnstr_set(x_234, 0, x_2743);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 0, x_1265);
x_2747 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2747, 0, x_1);
lean::cnstr_set(x_2747, 1, x_2);
lean::cnstr_set(x_2747, 2, x_3);
lean::cnstr_set(x_2747, 3, x_4);
lean::cnstr_set_uint8(x_2747, sizeof(void*)*4, x_1889);
return x_2747;
}
else
{
obj* x_2748; obj* x_2749; obj* x_2750; obj* x_2751; obj* x_2752; obj* x_2753; obj* x_2754; obj* x_2755; obj* x_2756; obj* x_2757; 
x_2748 = lean::cnstr_get(x_234, 0);
x_2749 = lean::cnstr_get(x_234, 1);
x_2750 = lean::cnstr_get(x_234, 2);
x_2751 = lean::cnstr_get(x_234, 3);
x_2752 = lean::cnstr_get(x_1265, 0);
x_2753 = lean::cnstr_get(x_1265, 1);
x_2754 = lean::cnstr_get(x_1265, 2);
x_2755 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2755);
lean::inc(x_2754);
lean::inc(x_2753);
lean::inc(x_2752);
lean::dec(x_1265);
x_2756 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2756, 0, x_2748);
lean::cnstr_set(x_2756, 1, x_2749);
lean::cnstr_set(x_2756, 2, x_2750);
lean::cnstr_set(x_2756, 3, x_2751);
lean::cnstr_set_uint8(x_2756, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_234, 3, x_2755);
lean::cnstr_set(x_234, 2, x_2754);
lean::cnstr_set(x_234, 1, x_2753);
lean::cnstr_set(x_234, 0, x_2752);
lean::cnstr_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_1, 3, x_234);
lean::cnstr_set(x_1, 0, x_2756);
x_2757 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2757, 0, x_1);
lean::cnstr_set(x_2757, 1, x_2);
lean::cnstr_set(x_2757, 2, x_3);
lean::cnstr_set(x_2757, 3, x_4);
lean::cnstr_set_uint8(x_2757, sizeof(void*)*4, x_1889);
return x_2757;
}
}
else
{
obj* x_2758; obj* x_2759; obj* x_2760; obj* x_2761; obj* x_2762; obj* x_2763; obj* x_2764; obj* x_2765; obj* x_2766; obj* x_2767; obj* x_2768; obj* x_2769; 
x_2758 = lean::cnstr_get(x_234, 0);
x_2759 = lean::cnstr_get(x_234, 1);
x_2760 = lean::cnstr_get(x_234, 2);
x_2761 = lean::cnstr_get(x_234, 3);
lean::inc(x_2761);
lean::inc(x_2760);
lean::inc(x_2759);
lean::inc(x_2758);
lean::dec(x_234);
x_2762 = lean::cnstr_get(x_1265, 0);
lean::inc(x_2762);
x_2763 = lean::cnstr_get(x_1265, 1);
lean::inc(x_2763);
x_2764 = lean::cnstr_get(x_1265, 2);
lean::inc(x_2764);
x_2765 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2765);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2766 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2766 = lean::box(0);
}
if (lean::is_scalar(x_2766)) {
 x_2767 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2767 = x_2766;
}
lean::cnstr_set(x_2767, 0, x_2758);
lean::cnstr_set(x_2767, 1, x_2759);
lean::cnstr_set(x_2767, 2, x_2760);
lean::cnstr_set(x_2767, 3, x_2761);
lean::cnstr_set_uint8(x_2767, sizeof(void*)*4, x_1889);
x_2768 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2768, 0, x_2762);
lean::cnstr_set(x_2768, 1, x_2763);
lean::cnstr_set(x_2768, 2, x_2764);
lean::cnstr_set(x_2768, 3, x_2765);
lean::cnstr_set_uint8(x_2768, sizeof(void*)*4, x_1889);
lean::cnstr_set(x_1, 3, x_2768);
lean::cnstr_set(x_1, 0, x_2767);
x_2769 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2769, 0, x_1);
lean::cnstr_set(x_2769, 1, x_2);
lean::cnstr_set(x_2769, 2, x_3);
lean::cnstr_set(x_2769, 3, x_4);
lean::cnstr_set_uint8(x_2769, sizeof(void*)*4, x_1889);
return x_2769;
}
}
else
{
obj* x_2770; obj* x_2771; obj* x_2772; obj* x_2773; obj* x_2774; obj* x_2775; obj* x_2776; obj* x_2777; obj* x_2778; obj* x_2779; obj* x_2780; obj* x_2781; obj* x_2782; obj* x_2783; obj* x_2784; obj* x_2785; 
x_2770 = lean::cnstr_get(x_1, 1);
x_2771 = lean::cnstr_get(x_1, 2);
lean::inc(x_2771);
lean::inc(x_2770);
lean::dec(x_1);
x_2772 = lean::cnstr_get(x_234, 0);
lean::inc(x_2772);
x_2773 = lean::cnstr_get(x_234, 1);
lean::inc(x_2773);
x_2774 = lean::cnstr_get(x_234, 2);
lean::inc(x_2774);
x_2775 = lean::cnstr_get(x_234, 3);
lean::inc(x_2775);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 lean::cnstr_release(x_234, 1);
 lean::cnstr_release(x_234, 2);
 lean::cnstr_release(x_234, 3);
 x_2776 = x_234;
} else {
 lean::dec_ref(x_234);
 x_2776 = lean::box(0);
}
x_2777 = lean::cnstr_get(x_1265, 0);
lean::inc(x_2777);
x_2778 = lean::cnstr_get(x_1265, 1);
lean::inc(x_2778);
x_2779 = lean::cnstr_get(x_1265, 2);
lean::inc(x_2779);
x_2780 = lean::cnstr_get(x_1265, 3);
lean::inc(x_2780);
if (lean::is_exclusive(x_1265)) {
 lean::cnstr_release(x_1265, 0);
 lean::cnstr_release(x_1265, 1);
 lean::cnstr_release(x_1265, 2);
 lean::cnstr_release(x_1265, 3);
 x_2781 = x_1265;
} else {
 lean::dec_ref(x_1265);
 x_2781 = lean::box(0);
}
if (lean::is_scalar(x_2781)) {
 x_2782 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2782 = x_2781;
}
lean::cnstr_set(x_2782, 0, x_2772);
lean::cnstr_set(x_2782, 1, x_2773);
lean::cnstr_set(x_2782, 2, x_2774);
lean::cnstr_set(x_2782, 3, x_2775);
lean::cnstr_set_uint8(x_2782, sizeof(void*)*4, x_1889);
if (lean::is_scalar(x_2776)) {
 x_2783 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2783 = x_2776;
}
lean::cnstr_set(x_2783, 0, x_2777);
lean::cnstr_set(x_2783, 1, x_2778);
lean::cnstr_set(x_2783, 2, x_2779);
lean::cnstr_set(x_2783, 3, x_2780);
lean::cnstr_set_uint8(x_2783, sizeof(void*)*4, x_1889);
x_2784 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2784, 0, x_2782);
lean::cnstr_set(x_2784, 1, x_2770);
lean::cnstr_set(x_2784, 2, x_2771);
lean::cnstr_set(x_2784, 3, x_2783);
lean::cnstr_set_uint8(x_2784, sizeof(void*)*4, x_233);
x_2785 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2785, 0, x_2784);
lean::cnstr_set(x_2785, 1, x_2);
lean::cnstr_set(x_2785, 2, x_3);
lean::cnstr_set(x_2785, 3, x_4);
lean::cnstr_set_uint8(x_2785, sizeof(void*)*4, x_1889);
return x_2785;
}
}
}
}
}
}
}
}
else
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_2786; 
x_2786 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2786, 0, x_1);
lean::cnstr_set(x_2786, 1, x_2);
lean::cnstr_set(x_2786, 2, x_3);
lean::cnstr_set(x_2786, 3, x_4);
lean::cnstr_set_uint8(x_2786, sizeof(void*)*4, x_233);
return x_2786;
}
else
{
uint8 x_2787; 
x_2787 = lean::cnstr_get_uint8(x_4, sizeof(void*)*4);
if (x_2787 == 0)
{
obj* x_2788; 
x_2788 = lean::cnstr_get(x_4, 0);
lean::inc(x_2788);
if (lean::obj_tag(x_2788) == 0)
{
obj* x_2789; 
x_2789 = lean::cnstr_get(x_4, 3);
lean::inc(x_2789);
if (lean::obj_tag(x_2789) == 0)
{
uint8 x_2790; 
x_2790 = !lean::is_exclusive(x_4);
if (x_2790 == 0)
{
obj* x_2791; obj* x_2792; obj* x_2793; 
x_2791 = lean::cnstr_get(x_4, 3);
lean::dec(x_2791);
x_2792 = lean::cnstr_get(x_4, 0);
lean::dec(x_2792);
lean::cnstr_set(x_4, 0, x_2789);
x_2793 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2793, 0, x_1);
lean::cnstr_set(x_2793, 1, x_2);
lean::cnstr_set(x_2793, 2, x_3);
lean::cnstr_set(x_2793, 3, x_4);
lean::cnstr_set_uint8(x_2793, sizeof(void*)*4, x_233);
return x_2793;
}
else
{
obj* x_2794; obj* x_2795; obj* x_2796; obj* x_2797; 
x_2794 = lean::cnstr_get(x_4, 1);
x_2795 = lean::cnstr_get(x_4, 2);
lean::inc(x_2795);
lean::inc(x_2794);
lean::dec(x_4);
x_2796 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2796, 0, x_2789);
lean::cnstr_set(x_2796, 1, x_2794);
lean::cnstr_set(x_2796, 2, x_2795);
lean::cnstr_set(x_2796, 3, x_2789);
lean::cnstr_set_uint8(x_2796, sizeof(void*)*4, x_2787);
x_2797 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2797, 0, x_1);
lean::cnstr_set(x_2797, 1, x_2);
lean::cnstr_set(x_2797, 2, x_3);
lean::cnstr_set(x_2797, 3, x_2796);
lean::cnstr_set_uint8(x_2797, sizeof(void*)*4, x_233);
return x_2797;
}
}
else
{
uint8 x_2798; 
x_2798 = lean::cnstr_get_uint8(x_2789, sizeof(void*)*4);
if (x_2798 == 0)
{
uint8 x_2799; 
x_2799 = !lean::is_exclusive(x_4);
if (x_2799 == 0)
{
obj* x_2800; obj* x_2801; obj* x_2802; obj* x_2803; uint8 x_2804; 
x_2800 = lean::cnstr_get(x_4, 1);
x_2801 = lean::cnstr_get(x_4, 2);
x_2802 = lean::cnstr_get(x_4, 3);
lean::dec(x_2802);
x_2803 = lean::cnstr_get(x_4, 0);
lean::dec(x_2803);
x_2804 = !lean::is_exclusive(x_2789);
if (x_2804 == 0)
{
obj* x_2805; obj* x_2806; obj* x_2807; obj* x_2808; uint8 x_2809; 
x_2805 = lean::cnstr_get(x_2789, 0);
x_2806 = lean::cnstr_get(x_2789, 1);
x_2807 = lean::cnstr_get(x_2789, 2);
x_2808 = lean::cnstr_get(x_2789, 3);
lean::inc(x_1);
lean::cnstr_set(x_2789, 3, x_2788);
lean::cnstr_set(x_2789, 2, x_3);
lean::cnstr_set(x_2789, 1, x_2);
lean::cnstr_set(x_2789, 0, x_1);
x_2809 = !lean::is_exclusive(x_1);
if (x_2809 == 0)
{
obj* x_2810; obj* x_2811; obj* x_2812; obj* x_2813; 
x_2810 = lean::cnstr_get(x_1, 3);
lean::dec(x_2810);
x_2811 = lean::cnstr_get(x_1, 2);
lean::dec(x_2811);
x_2812 = lean::cnstr_get(x_1, 1);
lean::dec(x_2812);
x_2813 = lean::cnstr_get(x_1, 0);
lean::dec(x_2813);
lean::cnstr_set_uint8(x_2789, sizeof(void*)*4, x_233);
lean::cnstr_set(x_4, 3, x_2808);
lean::cnstr_set(x_4, 2, x_2807);
lean::cnstr_set(x_4, 1, x_2806);
lean::cnstr_set(x_4, 0, x_2805);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_233);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_2801);
lean::cnstr_set(x_1, 1, x_2800);
lean::cnstr_set(x_1, 0, x_2789);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2798);
return x_1;
}
else
{
obj* x_2814; 
lean::dec(x_1);
lean::cnstr_set_uint8(x_2789, sizeof(void*)*4, x_233);
lean::cnstr_set(x_4, 3, x_2808);
lean::cnstr_set(x_4, 2, x_2807);
lean::cnstr_set(x_4, 1, x_2806);
lean::cnstr_set(x_4, 0, x_2805);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_233);
x_2814 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2814, 0, x_2789);
lean::cnstr_set(x_2814, 1, x_2800);
lean::cnstr_set(x_2814, 2, x_2801);
lean::cnstr_set(x_2814, 3, x_4);
lean::cnstr_set_uint8(x_2814, sizeof(void*)*4, x_2798);
return x_2814;
}
}
else
{
obj* x_2815; obj* x_2816; obj* x_2817; obj* x_2818; obj* x_2819; obj* x_2820; obj* x_2821; 
x_2815 = lean::cnstr_get(x_2789, 0);
x_2816 = lean::cnstr_get(x_2789, 1);
x_2817 = lean::cnstr_get(x_2789, 2);
x_2818 = lean::cnstr_get(x_2789, 3);
lean::inc(x_2818);
lean::inc(x_2817);
lean::inc(x_2816);
lean::inc(x_2815);
lean::dec(x_2789);
lean::inc(x_1);
x_2819 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2819, 0, x_1);
lean::cnstr_set(x_2819, 1, x_2);
lean::cnstr_set(x_2819, 2, x_3);
lean::cnstr_set(x_2819, 3, x_2788);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_2820 = x_1;
} else {
 lean::dec_ref(x_1);
 x_2820 = lean::box(0);
}
lean::cnstr_set_uint8(x_2819, sizeof(void*)*4, x_233);
lean::cnstr_set(x_4, 3, x_2818);
lean::cnstr_set(x_4, 2, x_2817);
lean::cnstr_set(x_4, 1, x_2816);
lean::cnstr_set(x_4, 0, x_2815);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_233);
if (lean::is_scalar(x_2820)) {
 x_2821 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2821 = x_2820;
}
lean::cnstr_set(x_2821, 0, x_2819);
lean::cnstr_set(x_2821, 1, x_2800);
lean::cnstr_set(x_2821, 2, x_2801);
lean::cnstr_set(x_2821, 3, x_4);
lean::cnstr_set_uint8(x_2821, sizeof(void*)*4, x_2798);
return x_2821;
}
}
else
{
obj* x_2822; obj* x_2823; obj* x_2824; obj* x_2825; obj* x_2826; obj* x_2827; obj* x_2828; obj* x_2829; obj* x_2830; obj* x_2831; obj* x_2832; 
x_2822 = lean::cnstr_get(x_4, 1);
x_2823 = lean::cnstr_get(x_4, 2);
lean::inc(x_2823);
lean::inc(x_2822);
lean::dec(x_4);
x_2824 = lean::cnstr_get(x_2789, 0);
lean::inc(x_2824);
x_2825 = lean::cnstr_get(x_2789, 1);
lean::inc(x_2825);
x_2826 = lean::cnstr_get(x_2789, 2);
lean::inc(x_2826);
x_2827 = lean::cnstr_get(x_2789, 3);
lean::inc(x_2827);
if (lean::is_exclusive(x_2789)) {
 lean::cnstr_release(x_2789, 0);
 lean::cnstr_release(x_2789, 1);
 lean::cnstr_release(x_2789, 2);
 lean::cnstr_release(x_2789, 3);
 x_2828 = x_2789;
} else {
 lean::dec_ref(x_2789);
 x_2828 = lean::box(0);
}
lean::inc(x_1);
if (lean::is_scalar(x_2828)) {
 x_2829 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2829 = x_2828;
}
lean::cnstr_set(x_2829, 0, x_1);
lean::cnstr_set(x_2829, 1, x_2);
lean::cnstr_set(x_2829, 2, x_3);
lean::cnstr_set(x_2829, 3, x_2788);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_2830 = x_1;
} else {
 lean::dec_ref(x_1);
 x_2830 = lean::box(0);
}
lean::cnstr_set_uint8(x_2829, sizeof(void*)*4, x_233);
x_2831 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2831, 0, x_2824);
lean::cnstr_set(x_2831, 1, x_2825);
lean::cnstr_set(x_2831, 2, x_2826);
lean::cnstr_set(x_2831, 3, x_2827);
lean::cnstr_set_uint8(x_2831, sizeof(void*)*4, x_233);
if (lean::is_scalar(x_2830)) {
 x_2832 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2832 = x_2830;
}
lean::cnstr_set(x_2832, 0, x_2829);
lean::cnstr_set(x_2832, 1, x_2822);
lean::cnstr_set(x_2832, 2, x_2823);
lean::cnstr_set(x_2832, 3, x_2831);
lean::cnstr_set_uint8(x_2832, sizeof(void*)*4, x_2798);
return x_2832;
}
}
else
{
uint8 x_2833; 
x_2833 = !lean::is_exclusive(x_2789);
if (x_2833 == 0)
{
obj* x_2834; obj* x_2835; obj* x_2836; obj* x_2837; uint8 x_2838; 
x_2834 = lean::cnstr_get(x_2789, 3);
lean::dec(x_2834);
x_2835 = lean::cnstr_get(x_2789, 2);
lean::dec(x_2835);
x_2836 = lean::cnstr_get(x_2789, 1);
lean::dec(x_2836);
x_2837 = lean::cnstr_get(x_2789, 0);
lean::dec(x_2837);
x_2838 = !lean::is_exclusive(x_1);
if (x_2838 == 0)
{
obj* x_2839; obj* x_2840; obj* x_2841; obj* x_2842; 
x_2839 = lean::cnstr_get(x_1, 0);
x_2840 = lean::cnstr_get(x_1, 1);
x_2841 = lean::cnstr_get(x_1, 2);
x_2842 = lean::cnstr_get(x_1, 3);
lean::cnstr_set(x_2789, 3, x_2842);
lean::cnstr_set(x_2789, 2, x_2841);
lean::cnstr_set(x_2789, 1, x_2840);
lean::cnstr_set(x_2789, 0, x_2839);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_2789);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2798);
return x_1;
}
else
{
obj* x_2843; obj* x_2844; obj* x_2845; obj* x_2846; obj* x_2847; 
x_2843 = lean::cnstr_get(x_1, 0);
x_2844 = lean::cnstr_get(x_1, 1);
x_2845 = lean::cnstr_get(x_1, 2);
x_2846 = lean::cnstr_get(x_1, 3);
lean::inc(x_2846);
lean::inc(x_2845);
lean::inc(x_2844);
lean::inc(x_2843);
lean::dec(x_1);
lean::cnstr_set(x_2789, 3, x_2846);
lean::cnstr_set(x_2789, 2, x_2845);
lean::cnstr_set(x_2789, 1, x_2844);
lean::cnstr_set(x_2789, 0, x_2843);
x_2847 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2847, 0, x_2789);
lean::cnstr_set(x_2847, 1, x_2);
lean::cnstr_set(x_2847, 2, x_3);
lean::cnstr_set(x_2847, 3, x_4);
lean::cnstr_set_uint8(x_2847, sizeof(void*)*4, x_2798);
return x_2847;
}
}
else
{
obj* x_2848; obj* x_2849; obj* x_2850; obj* x_2851; obj* x_2852; obj* x_2853; obj* x_2854; 
lean::dec(x_2789);
x_2848 = lean::cnstr_get(x_1, 0);
lean::inc(x_2848);
x_2849 = lean::cnstr_get(x_1, 1);
lean::inc(x_2849);
x_2850 = lean::cnstr_get(x_1, 2);
lean::inc(x_2850);
x_2851 = lean::cnstr_get(x_1, 3);
lean::inc(x_2851);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_2852 = x_1;
} else {
 lean::dec_ref(x_1);
 x_2852 = lean::box(0);
}
x_2853 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2853, 0, x_2848);
lean::cnstr_set(x_2853, 1, x_2849);
lean::cnstr_set(x_2853, 2, x_2850);
lean::cnstr_set(x_2853, 3, x_2851);
lean::cnstr_set_uint8(x_2853, sizeof(void*)*4, x_2798);
if (lean::is_scalar(x_2852)) {
 x_2854 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2854 = x_2852;
}
lean::cnstr_set(x_2854, 0, x_2853);
lean::cnstr_set(x_2854, 1, x_2);
lean::cnstr_set(x_2854, 2, x_3);
lean::cnstr_set(x_2854, 3, x_4);
lean::cnstr_set_uint8(x_2854, sizeof(void*)*4, x_2798);
return x_2854;
}
}
}
}
else
{
uint8 x_2855; 
x_2855 = lean::cnstr_get_uint8(x_2788, sizeof(void*)*4);
if (x_2855 == 0)
{
obj* x_2856; 
x_2856 = lean::cnstr_get(x_4, 3);
lean::inc(x_2856);
if (lean::obj_tag(x_2856) == 0)
{
uint8 x_2857; 
x_2857 = !lean::is_exclusive(x_4);
if (x_2857 == 0)
{
obj* x_2858; obj* x_2859; uint8 x_2860; 
x_2858 = lean::cnstr_get(x_4, 3);
lean::dec(x_2858);
x_2859 = lean::cnstr_get(x_4, 0);
lean::dec(x_2859);
x_2860 = !lean::is_exclusive(x_2788);
if (x_2860 == 0)
{
obj* x_2861; obj* x_2862; obj* x_2863; obj* x_2864; uint8 x_2865; 
x_2861 = lean::cnstr_get(x_2788, 0);
x_2862 = lean::cnstr_get(x_2788, 1);
x_2863 = lean::cnstr_get(x_2788, 2);
x_2864 = lean::cnstr_get(x_2788, 3);
lean::inc(x_1);
lean::cnstr_set(x_2788, 3, x_2861);
lean::cnstr_set(x_2788, 2, x_3);
lean::cnstr_set(x_2788, 1, x_2);
lean::cnstr_set(x_2788, 0, x_1);
x_2865 = !lean::is_exclusive(x_1);
if (x_2865 == 0)
{
obj* x_2866; obj* x_2867; obj* x_2868; obj* x_2869; 
x_2866 = lean::cnstr_get(x_1, 3);
lean::dec(x_2866);
x_2867 = lean::cnstr_get(x_1, 2);
lean::dec(x_2867);
x_2868 = lean::cnstr_get(x_1, 1);
lean::dec(x_2868);
x_2869 = lean::cnstr_get(x_1, 0);
lean::dec(x_2869);
lean::cnstr_set_uint8(x_2788, sizeof(void*)*4, x_233);
lean::cnstr_set(x_4, 0, x_2864);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_233);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_2863);
lean::cnstr_set(x_1, 1, x_2862);
lean::cnstr_set(x_1, 0, x_2788);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2855);
return x_1;
}
else
{
obj* x_2870; 
lean::dec(x_1);
lean::cnstr_set_uint8(x_2788, sizeof(void*)*4, x_233);
lean::cnstr_set(x_4, 0, x_2864);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_233);
x_2870 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2870, 0, x_2788);
lean::cnstr_set(x_2870, 1, x_2862);
lean::cnstr_set(x_2870, 2, x_2863);
lean::cnstr_set(x_2870, 3, x_4);
lean::cnstr_set_uint8(x_2870, sizeof(void*)*4, x_2855);
return x_2870;
}
}
else
{
obj* x_2871; obj* x_2872; obj* x_2873; obj* x_2874; obj* x_2875; obj* x_2876; obj* x_2877; 
x_2871 = lean::cnstr_get(x_2788, 0);
x_2872 = lean::cnstr_get(x_2788, 1);
x_2873 = lean::cnstr_get(x_2788, 2);
x_2874 = lean::cnstr_get(x_2788, 3);
lean::inc(x_2874);
lean::inc(x_2873);
lean::inc(x_2872);
lean::inc(x_2871);
lean::dec(x_2788);
lean::inc(x_1);
x_2875 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2875, 0, x_1);
lean::cnstr_set(x_2875, 1, x_2);
lean::cnstr_set(x_2875, 2, x_3);
lean::cnstr_set(x_2875, 3, x_2871);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_2876 = x_1;
} else {
 lean::dec_ref(x_1);
 x_2876 = lean::box(0);
}
lean::cnstr_set_uint8(x_2875, sizeof(void*)*4, x_233);
lean::cnstr_set(x_4, 0, x_2874);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_233);
if (lean::is_scalar(x_2876)) {
 x_2877 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2877 = x_2876;
}
lean::cnstr_set(x_2877, 0, x_2875);
lean::cnstr_set(x_2877, 1, x_2872);
lean::cnstr_set(x_2877, 2, x_2873);
lean::cnstr_set(x_2877, 3, x_4);
lean::cnstr_set_uint8(x_2877, sizeof(void*)*4, x_2855);
return x_2877;
}
}
else
{
obj* x_2878; obj* x_2879; obj* x_2880; obj* x_2881; obj* x_2882; obj* x_2883; obj* x_2884; obj* x_2885; obj* x_2886; obj* x_2887; obj* x_2888; 
x_2878 = lean::cnstr_get(x_4, 1);
x_2879 = lean::cnstr_get(x_4, 2);
lean::inc(x_2879);
lean::inc(x_2878);
lean::dec(x_4);
x_2880 = lean::cnstr_get(x_2788, 0);
lean::inc(x_2880);
x_2881 = lean::cnstr_get(x_2788, 1);
lean::inc(x_2881);
x_2882 = lean::cnstr_get(x_2788, 2);
lean::inc(x_2882);
x_2883 = lean::cnstr_get(x_2788, 3);
lean::inc(x_2883);
if (lean::is_exclusive(x_2788)) {
 lean::cnstr_release(x_2788, 0);
 lean::cnstr_release(x_2788, 1);
 lean::cnstr_release(x_2788, 2);
 lean::cnstr_release(x_2788, 3);
 x_2884 = x_2788;
} else {
 lean::dec_ref(x_2788);
 x_2884 = lean::box(0);
}
lean::inc(x_1);
if (lean::is_scalar(x_2884)) {
 x_2885 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2885 = x_2884;
}
lean::cnstr_set(x_2885, 0, x_1);
lean::cnstr_set(x_2885, 1, x_2);
lean::cnstr_set(x_2885, 2, x_3);
lean::cnstr_set(x_2885, 3, x_2880);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_2886 = x_1;
} else {
 lean::dec_ref(x_1);
 x_2886 = lean::box(0);
}
lean::cnstr_set_uint8(x_2885, sizeof(void*)*4, x_233);
x_2887 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2887, 0, x_2883);
lean::cnstr_set(x_2887, 1, x_2878);
lean::cnstr_set(x_2887, 2, x_2879);
lean::cnstr_set(x_2887, 3, x_2856);
lean::cnstr_set_uint8(x_2887, sizeof(void*)*4, x_233);
if (lean::is_scalar(x_2886)) {
 x_2888 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2888 = x_2886;
}
lean::cnstr_set(x_2888, 0, x_2885);
lean::cnstr_set(x_2888, 1, x_2881);
lean::cnstr_set(x_2888, 2, x_2882);
lean::cnstr_set(x_2888, 3, x_2887);
lean::cnstr_set_uint8(x_2888, sizeof(void*)*4, x_2855);
return x_2888;
}
}
else
{
uint8 x_2889; 
x_2889 = lean::cnstr_get_uint8(x_2856, sizeof(void*)*4);
if (x_2889 == 0)
{
uint8 x_2890; 
x_2890 = !lean::is_exclusive(x_4);
if (x_2890 == 0)
{
obj* x_2891; obj* x_2892; obj* x_2893; obj* x_2894; uint8 x_2895; 
x_2891 = lean::cnstr_get(x_4, 1);
x_2892 = lean::cnstr_get(x_4, 2);
x_2893 = lean::cnstr_get(x_4, 3);
lean::dec(x_2893);
x_2894 = lean::cnstr_get(x_4, 0);
lean::dec(x_2894);
x_2895 = !lean::is_exclusive(x_2788);
if (x_2895 == 0)
{
uint8 x_2896; 
x_2896 = !lean::is_exclusive(x_2856);
if (x_2896 == 0)
{
obj* x_2897; obj* x_2898; obj* x_2899; obj* x_2900; obj* x_2901; obj* x_2902; obj* x_2903; obj* x_2904; uint8 x_2905; 
x_2897 = lean::cnstr_get(x_2788, 0);
x_2898 = lean::cnstr_get(x_2788, 1);
x_2899 = lean::cnstr_get(x_2788, 2);
x_2900 = lean::cnstr_get(x_2788, 3);
x_2901 = lean::cnstr_get(x_2856, 0);
x_2902 = lean::cnstr_get(x_2856, 1);
x_2903 = lean::cnstr_get(x_2856, 2);
x_2904 = lean::cnstr_get(x_2856, 3);
lean::cnstr_set(x_2856, 3, x_2900);
lean::cnstr_set(x_2856, 2, x_2899);
lean::cnstr_set(x_2856, 1, x_2898);
lean::cnstr_set(x_2856, 0, x_2897);
lean::inc(x_1);
lean::cnstr_set(x_2788, 3, x_2856);
lean::cnstr_set(x_2788, 2, x_3);
lean::cnstr_set(x_2788, 1, x_2);
lean::cnstr_set(x_2788, 0, x_1);
x_2905 = !lean::is_exclusive(x_1);
if (x_2905 == 0)
{
obj* x_2906; obj* x_2907; obj* x_2908; obj* x_2909; 
x_2906 = lean::cnstr_get(x_1, 3);
lean::dec(x_2906);
x_2907 = lean::cnstr_get(x_1, 2);
lean::dec(x_2907);
x_2908 = lean::cnstr_get(x_1, 1);
lean::dec(x_2908);
x_2909 = lean::cnstr_get(x_1, 0);
lean::dec(x_2909);
lean::cnstr_set_uint8(x_2788, sizeof(void*)*4, x_233);
lean::cnstr_set(x_4, 3, x_2904);
lean::cnstr_set(x_4, 2, x_2903);
lean::cnstr_set(x_4, 1, x_2902);
lean::cnstr_set(x_4, 0, x_2901);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_233);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_2892);
lean::cnstr_set(x_1, 1, x_2891);
lean::cnstr_set(x_1, 0, x_2788);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2889);
return x_1;
}
else
{
obj* x_2910; 
lean::dec(x_1);
lean::cnstr_set_uint8(x_2788, sizeof(void*)*4, x_233);
lean::cnstr_set(x_4, 3, x_2904);
lean::cnstr_set(x_4, 2, x_2903);
lean::cnstr_set(x_4, 1, x_2902);
lean::cnstr_set(x_4, 0, x_2901);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_233);
x_2910 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2910, 0, x_2788);
lean::cnstr_set(x_2910, 1, x_2891);
lean::cnstr_set(x_2910, 2, x_2892);
lean::cnstr_set(x_2910, 3, x_4);
lean::cnstr_set_uint8(x_2910, sizeof(void*)*4, x_2889);
return x_2910;
}
}
else
{
obj* x_2911; obj* x_2912; obj* x_2913; obj* x_2914; obj* x_2915; obj* x_2916; obj* x_2917; obj* x_2918; obj* x_2919; obj* x_2920; obj* x_2921; 
x_2911 = lean::cnstr_get(x_2788, 0);
x_2912 = lean::cnstr_get(x_2788, 1);
x_2913 = lean::cnstr_get(x_2788, 2);
x_2914 = lean::cnstr_get(x_2788, 3);
x_2915 = lean::cnstr_get(x_2856, 0);
x_2916 = lean::cnstr_get(x_2856, 1);
x_2917 = lean::cnstr_get(x_2856, 2);
x_2918 = lean::cnstr_get(x_2856, 3);
lean::inc(x_2918);
lean::inc(x_2917);
lean::inc(x_2916);
lean::inc(x_2915);
lean::dec(x_2856);
x_2919 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2919, 0, x_2911);
lean::cnstr_set(x_2919, 1, x_2912);
lean::cnstr_set(x_2919, 2, x_2913);
lean::cnstr_set(x_2919, 3, x_2914);
lean::cnstr_set_uint8(x_2919, sizeof(void*)*4, x_2889);
lean::inc(x_1);
lean::cnstr_set(x_2788, 3, x_2919);
lean::cnstr_set(x_2788, 2, x_3);
lean::cnstr_set(x_2788, 1, x_2);
lean::cnstr_set(x_2788, 0, x_1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_2920 = x_1;
} else {
 lean::dec_ref(x_1);
 x_2920 = lean::box(0);
}
lean::cnstr_set_uint8(x_2788, sizeof(void*)*4, x_233);
lean::cnstr_set(x_4, 3, x_2918);
lean::cnstr_set(x_4, 2, x_2917);
lean::cnstr_set(x_4, 1, x_2916);
lean::cnstr_set(x_4, 0, x_2915);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_233);
if (lean::is_scalar(x_2920)) {
 x_2921 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2921 = x_2920;
}
lean::cnstr_set(x_2921, 0, x_2788);
lean::cnstr_set(x_2921, 1, x_2891);
lean::cnstr_set(x_2921, 2, x_2892);
lean::cnstr_set(x_2921, 3, x_4);
lean::cnstr_set_uint8(x_2921, sizeof(void*)*4, x_2889);
return x_2921;
}
}
else
{
obj* x_2922; obj* x_2923; obj* x_2924; obj* x_2925; obj* x_2926; obj* x_2927; obj* x_2928; obj* x_2929; obj* x_2930; obj* x_2931; obj* x_2932; obj* x_2933; obj* x_2934; 
x_2922 = lean::cnstr_get(x_2788, 0);
x_2923 = lean::cnstr_get(x_2788, 1);
x_2924 = lean::cnstr_get(x_2788, 2);
x_2925 = lean::cnstr_get(x_2788, 3);
lean::inc(x_2925);
lean::inc(x_2924);
lean::inc(x_2923);
lean::inc(x_2922);
lean::dec(x_2788);
x_2926 = lean::cnstr_get(x_2856, 0);
lean::inc(x_2926);
x_2927 = lean::cnstr_get(x_2856, 1);
lean::inc(x_2927);
x_2928 = lean::cnstr_get(x_2856, 2);
lean::inc(x_2928);
x_2929 = lean::cnstr_get(x_2856, 3);
lean::inc(x_2929);
if (lean::is_exclusive(x_2856)) {
 lean::cnstr_release(x_2856, 0);
 lean::cnstr_release(x_2856, 1);
 lean::cnstr_release(x_2856, 2);
 lean::cnstr_release(x_2856, 3);
 x_2930 = x_2856;
} else {
 lean::dec_ref(x_2856);
 x_2930 = lean::box(0);
}
if (lean::is_scalar(x_2930)) {
 x_2931 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2931 = x_2930;
}
lean::cnstr_set(x_2931, 0, x_2922);
lean::cnstr_set(x_2931, 1, x_2923);
lean::cnstr_set(x_2931, 2, x_2924);
lean::cnstr_set(x_2931, 3, x_2925);
lean::cnstr_set_uint8(x_2931, sizeof(void*)*4, x_2889);
lean::inc(x_1);
x_2932 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2932, 0, x_1);
lean::cnstr_set(x_2932, 1, x_2);
lean::cnstr_set(x_2932, 2, x_3);
lean::cnstr_set(x_2932, 3, x_2931);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_2933 = x_1;
} else {
 lean::dec_ref(x_1);
 x_2933 = lean::box(0);
}
lean::cnstr_set_uint8(x_2932, sizeof(void*)*4, x_233);
lean::cnstr_set(x_4, 3, x_2929);
lean::cnstr_set(x_4, 2, x_2928);
lean::cnstr_set(x_4, 1, x_2927);
lean::cnstr_set(x_4, 0, x_2926);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_233);
if (lean::is_scalar(x_2933)) {
 x_2934 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2934 = x_2933;
}
lean::cnstr_set(x_2934, 0, x_2932);
lean::cnstr_set(x_2934, 1, x_2891);
lean::cnstr_set(x_2934, 2, x_2892);
lean::cnstr_set(x_2934, 3, x_4);
lean::cnstr_set_uint8(x_2934, sizeof(void*)*4, x_2889);
return x_2934;
}
}
else
{
obj* x_2935; obj* x_2936; obj* x_2937; obj* x_2938; obj* x_2939; obj* x_2940; obj* x_2941; obj* x_2942; obj* x_2943; obj* x_2944; obj* x_2945; obj* x_2946; obj* x_2947; obj* x_2948; obj* x_2949; obj* x_2950; obj* x_2951; 
x_2935 = lean::cnstr_get(x_4, 1);
x_2936 = lean::cnstr_get(x_4, 2);
lean::inc(x_2936);
lean::inc(x_2935);
lean::dec(x_4);
x_2937 = lean::cnstr_get(x_2788, 0);
lean::inc(x_2937);
x_2938 = lean::cnstr_get(x_2788, 1);
lean::inc(x_2938);
x_2939 = lean::cnstr_get(x_2788, 2);
lean::inc(x_2939);
x_2940 = lean::cnstr_get(x_2788, 3);
lean::inc(x_2940);
if (lean::is_exclusive(x_2788)) {
 lean::cnstr_release(x_2788, 0);
 lean::cnstr_release(x_2788, 1);
 lean::cnstr_release(x_2788, 2);
 lean::cnstr_release(x_2788, 3);
 x_2941 = x_2788;
} else {
 lean::dec_ref(x_2788);
 x_2941 = lean::box(0);
}
x_2942 = lean::cnstr_get(x_2856, 0);
lean::inc(x_2942);
x_2943 = lean::cnstr_get(x_2856, 1);
lean::inc(x_2943);
x_2944 = lean::cnstr_get(x_2856, 2);
lean::inc(x_2944);
x_2945 = lean::cnstr_get(x_2856, 3);
lean::inc(x_2945);
if (lean::is_exclusive(x_2856)) {
 lean::cnstr_release(x_2856, 0);
 lean::cnstr_release(x_2856, 1);
 lean::cnstr_release(x_2856, 2);
 lean::cnstr_release(x_2856, 3);
 x_2946 = x_2856;
} else {
 lean::dec_ref(x_2856);
 x_2946 = lean::box(0);
}
if (lean::is_scalar(x_2946)) {
 x_2947 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2947 = x_2946;
}
lean::cnstr_set(x_2947, 0, x_2937);
lean::cnstr_set(x_2947, 1, x_2938);
lean::cnstr_set(x_2947, 2, x_2939);
lean::cnstr_set(x_2947, 3, x_2940);
lean::cnstr_set_uint8(x_2947, sizeof(void*)*4, x_2889);
lean::inc(x_1);
if (lean::is_scalar(x_2941)) {
 x_2948 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2948 = x_2941;
}
lean::cnstr_set(x_2948, 0, x_1);
lean::cnstr_set(x_2948, 1, x_2);
lean::cnstr_set(x_2948, 2, x_3);
lean::cnstr_set(x_2948, 3, x_2947);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_2949 = x_1;
} else {
 lean::dec_ref(x_1);
 x_2949 = lean::box(0);
}
lean::cnstr_set_uint8(x_2948, sizeof(void*)*4, x_233);
x_2950 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2950, 0, x_2942);
lean::cnstr_set(x_2950, 1, x_2943);
lean::cnstr_set(x_2950, 2, x_2944);
lean::cnstr_set(x_2950, 3, x_2945);
lean::cnstr_set_uint8(x_2950, sizeof(void*)*4, x_233);
if (lean::is_scalar(x_2949)) {
 x_2951 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2951 = x_2949;
}
lean::cnstr_set(x_2951, 0, x_2948);
lean::cnstr_set(x_2951, 1, x_2935);
lean::cnstr_set(x_2951, 2, x_2936);
lean::cnstr_set(x_2951, 3, x_2950);
lean::cnstr_set_uint8(x_2951, sizeof(void*)*4, x_2889);
return x_2951;
}
}
else
{
uint8 x_2952; 
x_2952 = !lean::is_exclusive(x_1);
if (x_2952 == 0)
{
uint8 x_2953; 
x_2953 = !lean::is_exclusive(x_4);
if (x_2953 == 0)
{
obj* x_2954; obj* x_2955; obj* x_2956; obj* x_2957; obj* x_2958; obj* x_2959; obj* x_2960; obj* x_2961; uint8 x_2962; 
x_2954 = lean::cnstr_get(x_1, 0);
x_2955 = lean::cnstr_get(x_1, 1);
x_2956 = lean::cnstr_get(x_1, 2);
x_2957 = lean::cnstr_get(x_1, 3);
x_2958 = lean::cnstr_get(x_4, 1);
x_2959 = lean::cnstr_get(x_4, 2);
x_2960 = lean::cnstr_get(x_4, 3);
lean::dec(x_2960);
x_2961 = lean::cnstr_get(x_4, 0);
lean::dec(x_2961);
x_2962 = !lean::is_exclusive(x_2788);
if (x_2962 == 0)
{
obj* x_2963; obj* x_2964; obj* x_2965; obj* x_2966; obj* x_2967; 
x_2963 = lean::cnstr_get(x_2788, 0);
x_2964 = lean::cnstr_get(x_2788, 1);
x_2965 = lean::cnstr_get(x_2788, 2);
x_2966 = lean::cnstr_get(x_2788, 3);
lean::cnstr_set(x_2788, 3, x_2957);
lean::cnstr_set(x_2788, 2, x_2956);
lean::cnstr_set(x_2788, 1, x_2955);
lean::cnstr_set(x_2788, 0, x_2954);
lean::cnstr_set_uint8(x_2788, sizeof(void*)*4, x_2889);
lean::cnstr_set(x_4, 3, x_2963);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2889);
lean::cnstr_set(x_1, 3, x_2856);
lean::cnstr_set(x_1, 2, x_2959);
lean::cnstr_set(x_1, 1, x_2958);
lean::cnstr_set(x_1, 0, x_2966);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2889);
x_2967 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2967, 0, x_4);
lean::cnstr_set(x_2967, 1, x_2964);
lean::cnstr_set(x_2967, 2, x_2965);
lean::cnstr_set(x_2967, 3, x_1);
lean::cnstr_set_uint8(x_2967, sizeof(void*)*4, x_2855);
return x_2967;
}
else
{
obj* x_2968; obj* x_2969; obj* x_2970; obj* x_2971; obj* x_2972; obj* x_2973; 
x_2968 = lean::cnstr_get(x_2788, 0);
x_2969 = lean::cnstr_get(x_2788, 1);
x_2970 = lean::cnstr_get(x_2788, 2);
x_2971 = lean::cnstr_get(x_2788, 3);
lean::inc(x_2971);
lean::inc(x_2970);
lean::inc(x_2969);
lean::inc(x_2968);
lean::dec(x_2788);
x_2972 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2972, 0, x_2954);
lean::cnstr_set(x_2972, 1, x_2955);
lean::cnstr_set(x_2972, 2, x_2956);
lean::cnstr_set(x_2972, 3, x_2957);
lean::cnstr_set_uint8(x_2972, sizeof(void*)*4, x_2889);
lean::cnstr_set(x_4, 3, x_2968);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_2972);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2889);
lean::cnstr_set(x_1, 3, x_2856);
lean::cnstr_set(x_1, 2, x_2959);
lean::cnstr_set(x_1, 1, x_2958);
lean::cnstr_set(x_1, 0, x_2971);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2889);
x_2973 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2973, 0, x_4);
lean::cnstr_set(x_2973, 1, x_2969);
lean::cnstr_set(x_2973, 2, x_2970);
lean::cnstr_set(x_2973, 3, x_1);
lean::cnstr_set_uint8(x_2973, sizeof(void*)*4, x_2855);
return x_2973;
}
}
else
{
obj* x_2974; obj* x_2975; obj* x_2976; obj* x_2977; obj* x_2978; obj* x_2979; obj* x_2980; obj* x_2981; obj* x_2982; obj* x_2983; obj* x_2984; obj* x_2985; obj* x_2986; obj* x_2987; 
x_2974 = lean::cnstr_get(x_1, 0);
x_2975 = lean::cnstr_get(x_1, 1);
x_2976 = lean::cnstr_get(x_1, 2);
x_2977 = lean::cnstr_get(x_1, 3);
x_2978 = lean::cnstr_get(x_4, 1);
x_2979 = lean::cnstr_get(x_4, 2);
lean::inc(x_2979);
lean::inc(x_2978);
lean::dec(x_4);
x_2980 = lean::cnstr_get(x_2788, 0);
lean::inc(x_2980);
x_2981 = lean::cnstr_get(x_2788, 1);
lean::inc(x_2981);
x_2982 = lean::cnstr_get(x_2788, 2);
lean::inc(x_2982);
x_2983 = lean::cnstr_get(x_2788, 3);
lean::inc(x_2983);
if (lean::is_exclusive(x_2788)) {
 lean::cnstr_release(x_2788, 0);
 lean::cnstr_release(x_2788, 1);
 lean::cnstr_release(x_2788, 2);
 lean::cnstr_release(x_2788, 3);
 x_2984 = x_2788;
} else {
 lean::dec_ref(x_2788);
 x_2984 = lean::box(0);
}
if (lean::is_scalar(x_2984)) {
 x_2985 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_2985 = x_2984;
}
lean::cnstr_set(x_2985, 0, x_2974);
lean::cnstr_set(x_2985, 1, x_2975);
lean::cnstr_set(x_2985, 2, x_2976);
lean::cnstr_set(x_2985, 3, x_2977);
lean::cnstr_set_uint8(x_2985, sizeof(void*)*4, x_2889);
x_2986 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2986, 0, x_2985);
lean::cnstr_set(x_2986, 1, x_2);
lean::cnstr_set(x_2986, 2, x_3);
lean::cnstr_set(x_2986, 3, x_2980);
lean::cnstr_set_uint8(x_2986, sizeof(void*)*4, x_2889);
lean::cnstr_set(x_1, 3, x_2856);
lean::cnstr_set(x_1, 2, x_2979);
lean::cnstr_set(x_1, 1, x_2978);
lean::cnstr_set(x_1, 0, x_2983);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2889);
x_2987 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_2987, 0, x_2986);
lean::cnstr_set(x_2987, 1, x_2981);
lean::cnstr_set(x_2987, 2, x_2982);
lean::cnstr_set(x_2987, 3, x_1);
lean::cnstr_set_uint8(x_2987, sizeof(void*)*4, x_2855);
return x_2987;
}
}
else
{
obj* x_2988; obj* x_2989; obj* x_2990; obj* x_2991; obj* x_2992; obj* x_2993; obj* x_2994; obj* x_2995; obj* x_2996; obj* x_2997; obj* x_2998; obj* x_2999; obj* x_3000; obj* x_3001; obj* x_3002; obj* x_3003; 
x_2988 = lean::cnstr_get(x_1, 0);
x_2989 = lean::cnstr_get(x_1, 1);
x_2990 = lean::cnstr_get(x_1, 2);
x_2991 = lean::cnstr_get(x_1, 3);
lean::inc(x_2991);
lean::inc(x_2990);
lean::inc(x_2989);
lean::inc(x_2988);
lean::dec(x_1);
x_2992 = lean::cnstr_get(x_4, 1);
lean::inc(x_2992);
x_2993 = lean::cnstr_get(x_4, 2);
lean::inc(x_2993);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_2994 = x_4;
} else {
 lean::dec_ref(x_4);
 x_2994 = lean::box(0);
}
x_2995 = lean::cnstr_get(x_2788, 0);
lean::inc(x_2995);
x_2996 = lean::cnstr_get(x_2788, 1);
lean::inc(x_2996);
x_2997 = lean::cnstr_get(x_2788, 2);
lean::inc(x_2997);
x_2998 = lean::cnstr_get(x_2788, 3);
lean::inc(x_2998);
if (lean::is_exclusive(x_2788)) {
 lean::cnstr_release(x_2788, 0);
 lean::cnstr_release(x_2788, 1);
 lean::cnstr_release(x_2788, 2);
 lean::cnstr_release(x_2788, 3);
 x_2999 = x_2788;
} else {
 lean::dec_ref(x_2788);
 x_2999 = lean::box(0);
}
if (lean::is_scalar(x_2999)) {
 x_3000 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_3000 = x_2999;
}
lean::cnstr_set(x_3000, 0, x_2988);
lean::cnstr_set(x_3000, 1, x_2989);
lean::cnstr_set(x_3000, 2, x_2990);
lean::cnstr_set(x_3000, 3, x_2991);
lean::cnstr_set_uint8(x_3000, sizeof(void*)*4, x_2889);
if (lean::is_scalar(x_2994)) {
 x_3001 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_3001 = x_2994;
}
lean::cnstr_set(x_3001, 0, x_3000);
lean::cnstr_set(x_3001, 1, x_2);
lean::cnstr_set(x_3001, 2, x_3);
lean::cnstr_set(x_3001, 3, x_2995);
lean::cnstr_set_uint8(x_3001, sizeof(void*)*4, x_2889);
x_3002 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3002, 0, x_2998);
lean::cnstr_set(x_3002, 1, x_2992);
lean::cnstr_set(x_3002, 2, x_2993);
lean::cnstr_set(x_3002, 3, x_2856);
lean::cnstr_set_uint8(x_3002, sizeof(void*)*4, x_2889);
x_3003 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3003, 0, x_3001);
lean::cnstr_set(x_3003, 1, x_2996);
lean::cnstr_set(x_3003, 2, x_2997);
lean::cnstr_set(x_3003, 3, x_3002);
lean::cnstr_set_uint8(x_3003, sizeof(void*)*4, x_2855);
return x_3003;
}
}
}
}
else
{
obj* x_3004; 
x_3004 = lean::cnstr_get(x_4, 3);
lean::inc(x_3004);
if (lean::obj_tag(x_3004) == 0)
{
uint8 x_3005; 
x_3005 = !lean::is_exclusive(x_2788);
if (x_3005 == 0)
{
obj* x_3006; obj* x_3007; obj* x_3008; obj* x_3009; uint8 x_3010; 
x_3006 = lean::cnstr_get(x_2788, 3);
lean::dec(x_3006);
x_3007 = lean::cnstr_get(x_2788, 2);
lean::dec(x_3007);
x_3008 = lean::cnstr_get(x_2788, 1);
lean::dec(x_3008);
x_3009 = lean::cnstr_get(x_2788, 0);
lean::dec(x_3009);
x_3010 = !lean::is_exclusive(x_1);
if (x_3010 == 0)
{
obj* x_3011; obj* x_3012; obj* x_3013; obj* x_3014; 
x_3011 = lean::cnstr_get(x_1, 0);
x_3012 = lean::cnstr_get(x_1, 1);
x_3013 = lean::cnstr_get(x_1, 2);
x_3014 = lean::cnstr_get(x_1, 3);
lean::cnstr_set(x_2788, 3, x_3014);
lean::cnstr_set(x_2788, 2, x_3013);
lean::cnstr_set(x_2788, 1, x_3012);
lean::cnstr_set(x_2788, 0, x_3011);
lean::cnstr_set(x_1, 3, x_4);
lean::cnstr_set(x_1, 2, x_3);
lean::cnstr_set(x_1, 1, x_2);
lean::cnstr_set(x_1, 0, x_2788);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2855);
return x_1;
}
else
{
obj* x_3015; obj* x_3016; obj* x_3017; obj* x_3018; obj* x_3019; 
x_3015 = lean::cnstr_get(x_1, 0);
x_3016 = lean::cnstr_get(x_1, 1);
x_3017 = lean::cnstr_get(x_1, 2);
x_3018 = lean::cnstr_get(x_1, 3);
lean::inc(x_3018);
lean::inc(x_3017);
lean::inc(x_3016);
lean::inc(x_3015);
lean::dec(x_1);
lean::cnstr_set(x_2788, 3, x_3018);
lean::cnstr_set(x_2788, 2, x_3017);
lean::cnstr_set(x_2788, 1, x_3016);
lean::cnstr_set(x_2788, 0, x_3015);
x_3019 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3019, 0, x_2788);
lean::cnstr_set(x_3019, 1, x_2);
lean::cnstr_set(x_3019, 2, x_3);
lean::cnstr_set(x_3019, 3, x_4);
lean::cnstr_set_uint8(x_3019, sizeof(void*)*4, x_2855);
return x_3019;
}
}
else
{
obj* x_3020; obj* x_3021; obj* x_3022; obj* x_3023; obj* x_3024; obj* x_3025; obj* x_3026; 
lean::dec(x_2788);
x_3020 = lean::cnstr_get(x_1, 0);
lean::inc(x_3020);
x_3021 = lean::cnstr_get(x_1, 1);
lean::inc(x_3021);
x_3022 = lean::cnstr_get(x_1, 2);
lean::inc(x_3022);
x_3023 = lean::cnstr_get(x_1, 3);
lean::inc(x_3023);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_3024 = x_1;
} else {
 lean::dec_ref(x_1);
 x_3024 = lean::box(0);
}
x_3025 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3025, 0, x_3020);
lean::cnstr_set(x_3025, 1, x_3021);
lean::cnstr_set(x_3025, 2, x_3022);
lean::cnstr_set(x_3025, 3, x_3023);
lean::cnstr_set_uint8(x_3025, sizeof(void*)*4, x_2855);
if (lean::is_scalar(x_3024)) {
 x_3026 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_3026 = x_3024;
}
lean::cnstr_set(x_3026, 0, x_3025);
lean::cnstr_set(x_3026, 1, x_2);
lean::cnstr_set(x_3026, 2, x_3);
lean::cnstr_set(x_3026, 3, x_4);
lean::cnstr_set_uint8(x_3026, sizeof(void*)*4, x_2855);
return x_3026;
}
}
else
{
uint8 x_3027; 
x_3027 = lean::cnstr_get_uint8(x_3004, sizeof(void*)*4);
if (x_3027 == 0)
{
uint8 x_3028; 
x_3028 = !lean::is_exclusive(x_1);
if (x_3028 == 0)
{
uint8 x_3029; 
x_3029 = !lean::is_exclusive(x_4);
if (x_3029 == 0)
{
obj* x_3030; obj* x_3031; obj* x_3032; obj* x_3033; obj* x_3034; obj* x_3035; obj* x_3036; obj* x_3037; uint8 x_3038; 
x_3030 = lean::cnstr_get(x_1, 0);
x_3031 = lean::cnstr_get(x_1, 1);
x_3032 = lean::cnstr_get(x_1, 2);
x_3033 = lean::cnstr_get(x_1, 3);
x_3034 = lean::cnstr_get(x_4, 1);
x_3035 = lean::cnstr_get(x_4, 2);
x_3036 = lean::cnstr_get(x_4, 3);
lean::dec(x_3036);
x_3037 = lean::cnstr_get(x_4, 0);
lean::dec(x_3037);
x_3038 = !lean::is_exclusive(x_3004);
if (x_3038 == 0)
{
obj* x_3039; obj* x_3040; obj* x_3041; obj* x_3042; obj* x_3043; 
x_3039 = lean::cnstr_get(x_3004, 0);
x_3040 = lean::cnstr_get(x_3004, 1);
x_3041 = lean::cnstr_get(x_3004, 2);
x_3042 = lean::cnstr_get(x_3004, 3);
lean::cnstr_set(x_3004, 3, x_3033);
lean::cnstr_set(x_3004, 2, x_3032);
lean::cnstr_set(x_3004, 1, x_3031);
lean::cnstr_set(x_3004, 0, x_3030);
lean::cnstr_set_uint8(x_3004, sizeof(void*)*4, x_2855);
lean::cnstr_set(x_4, 3, x_2788);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_3004);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2855);
lean::cnstr_set(x_1, 3, x_3042);
lean::cnstr_set(x_1, 2, x_3041);
lean::cnstr_set(x_1, 1, x_3040);
lean::cnstr_set(x_1, 0, x_3039);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2855);
x_3043 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3043, 0, x_4);
lean::cnstr_set(x_3043, 1, x_3034);
lean::cnstr_set(x_3043, 2, x_3035);
lean::cnstr_set(x_3043, 3, x_1);
lean::cnstr_set_uint8(x_3043, sizeof(void*)*4, x_3027);
return x_3043;
}
else
{
obj* x_3044; obj* x_3045; obj* x_3046; obj* x_3047; obj* x_3048; obj* x_3049; 
x_3044 = lean::cnstr_get(x_3004, 0);
x_3045 = lean::cnstr_get(x_3004, 1);
x_3046 = lean::cnstr_get(x_3004, 2);
x_3047 = lean::cnstr_get(x_3004, 3);
lean::inc(x_3047);
lean::inc(x_3046);
lean::inc(x_3045);
lean::inc(x_3044);
lean::dec(x_3004);
x_3048 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3048, 0, x_3030);
lean::cnstr_set(x_3048, 1, x_3031);
lean::cnstr_set(x_3048, 2, x_3032);
lean::cnstr_set(x_3048, 3, x_3033);
lean::cnstr_set_uint8(x_3048, sizeof(void*)*4, x_2855);
lean::cnstr_set(x_4, 3, x_2788);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_3048);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_2855);
lean::cnstr_set(x_1, 3, x_3047);
lean::cnstr_set(x_1, 2, x_3046);
lean::cnstr_set(x_1, 1, x_3045);
lean::cnstr_set(x_1, 0, x_3044);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2855);
x_3049 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3049, 0, x_4);
lean::cnstr_set(x_3049, 1, x_3034);
lean::cnstr_set(x_3049, 2, x_3035);
lean::cnstr_set(x_3049, 3, x_1);
lean::cnstr_set_uint8(x_3049, sizeof(void*)*4, x_3027);
return x_3049;
}
}
else
{
obj* x_3050; obj* x_3051; obj* x_3052; obj* x_3053; obj* x_3054; obj* x_3055; obj* x_3056; obj* x_3057; obj* x_3058; obj* x_3059; obj* x_3060; obj* x_3061; obj* x_3062; obj* x_3063; 
x_3050 = lean::cnstr_get(x_1, 0);
x_3051 = lean::cnstr_get(x_1, 1);
x_3052 = lean::cnstr_get(x_1, 2);
x_3053 = lean::cnstr_get(x_1, 3);
x_3054 = lean::cnstr_get(x_4, 1);
x_3055 = lean::cnstr_get(x_4, 2);
lean::inc(x_3055);
lean::inc(x_3054);
lean::dec(x_4);
x_3056 = lean::cnstr_get(x_3004, 0);
lean::inc(x_3056);
x_3057 = lean::cnstr_get(x_3004, 1);
lean::inc(x_3057);
x_3058 = lean::cnstr_get(x_3004, 2);
lean::inc(x_3058);
x_3059 = lean::cnstr_get(x_3004, 3);
lean::inc(x_3059);
if (lean::is_exclusive(x_3004)) {
 lean::cnstr_release(x_3004, 0);
 lean::cnstr_release(x_3004, 1);
 lean::cnstr_release(x_3004, 2);
 lean::cnstr_release(x_3004, 3);
 x_3060 = x_3004;
} else {
 lean::dec_ref(x_3004);
 x_3060 = lean::box(0);
}
if (lean::is_scalar(x_3060)) {
 x_3061 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_3061 = x_3060;
}
lean::cnstr_set(x_3061, 0, x_3050);
lean::cnstr_set(x_3061, 1, x_3051);
lean::cnstr_set(x_3061, 2, x_3052);
lean::cnstr_set(x_3061, 3, x_3053);
lean::cnstr_set_uint8(x_3061, sizeof(void*)*4, x_2855);
x_3062 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3062, 0, x_3061);
lean::cnstr_set(x_3062, 1, x_2);
lean::cnstr_set(x_3062, 2, x_3);
lean::cnstr_set(x_3062, 3, x_2788);
lean::cnstr_set_uint8(x_3062, sizeof(void*)*4, x_2855);
lean::cnstr_set(x_1, 3, x_3059);
lean::cnstr_set(x_1, 2, x_3058);
lean::cnstr_set(x_1, 1, x_3057);
lean::cnstr_set(x_1, 0, x_3056);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2855);
x_3063 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3063, 0, x_3062);
lean::cnstr_set(x_3063, 1, x_3054);
lean::cnstr_set(x_3063, 2, x_3055);
lean::cnstr_set(x_3063, 3, x_1);
lean::cnstr_set_uint8(x_3063, sizeof(void*)*4, x_3027);
return x_3063;
}
}
else
{
obj* x_3064; obj* x_3065; obj* x_3066; obj* x_3067; obj* x_3068; obj* x_3069; obj* x_3070; obj* x_3071; obj* x_3072; obj* x_3073; obj* x_3074; obj* x_3075; obj* x_3076; obj* x_3077; obj* x_3078; obj* x_3079; 
x_3064 = lean::cnstr_get(x_1, 0);
x_3065 = lean::cnstr_get(x_1, 1);
x_3066 = lean::cnstr_get(x_1, 2);
x_3067 = lean::cnstr_get(x_1, 3);
lean::inc(x_3067);
lean::inc(x_3066);
lean::inc(x_3065);
lean::inc(x_3064);
lean::dec(x_1);
x_3068 = lean::cnstr_get(x_4, 1);
lean::inc(x_3068);
x_3069 = lean::cnstr_get(x_4, 2);
lean::inc(x_3069);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_3070 = x_4;
} else {
 lean::dec_ref(x_4);
 x_3070 = lean::box(0);
}
x_3071 = lean::cnstr_get(x_3004, 0);
lean::inc(x_3071);
x_3072 = lean::cnstr_get(x_3004, 1);
lean::inc(x_3072);
x_3073 = lean::cnstr_get(x_3004, 2);
lean::inc(x_3073);
x_3074 = lean::cnstr_get(x_3004, 3);
lean::inc(x_3074);
if (lean::is_exclusive(x_3004)) {
 lean::cnstr_release(x_3004, 0);
 lean::cnstr_release(x_3004, 1);
 lean::cnstr_release(x_3004, 2);
 lean::cnstr_release(x_3004, 3);
 x_3075 = x_3004;
} else {
 lean::dec_ref(x_3004);
 x_3075 = lean::box(0);
}
if (lean::is_scalar(x_3075)) {
 x_3076 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_3076 = x_3075;
}
lean::cnstr_set(x_3076, 0, x_3064);
lean::cnstr_set(x_3076, 1, x_3065);
lean::cnstr_set(x_3076, 2, x_3066);
lean::cnstr_set(x_3076, 3, x_3067);
lean::cnstr_set_uint8(x_3076, sizeof(void*)*4, x_2855);
if (lean::is_scalar(x_3070)) {
 x_3077 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_3077 = x_3070;
}
lean::cnstr_set(x_3077, 0, x_3076);
lean::cnstr_set(x_3077, 1, x_2);
lean::cnstr_set(x_3077, 2, x_3);
lean::cnstr_set(x_3077, 3, x_2788);
lean::cnstr_set_uint8(x_3077, sizeof(void*)*4, x_2855);
x_3078 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3078, 0, x_3071);
lean::cnstr_set(x_3078, 1, x_3072);
lean::cnstr_set(x_3078, 2, x_3073);
lean::cnstr_set(x_3078, 3, x_3074);
lean::cnstr_set_uint8(x_3078, sizeof(void*)*4, x_2855);
x_3079 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3079, 0, x_3077);
lean::cnstr_set(x_3079, 1, x_3068);
lean::cnstr_set(x_3079, 2, x_3069);
lean::cnstr_set(x_3079, 3, x_3078);
lean::cnstr_set_uint8(x_3079, sizeof(void*)*4, x_3027);
return x_3079;
}
}
else
{
uint8 x_3080; 
x_3080 = !lean::is_exclusive(x_1);
if (x_3080 == 0)
{
uint8 x_3081; 
x_3081 = !lean::is_exclusive(x_4);
if (x_3081 == 0)
{
obj* x_3082; obj* x_3083; obj* x_3084; obj* x_3085; obj* x_3086; obj* x_3087; obj* x_3088; obj* x_3089; uint8 x_3090; 
x_3082 = lean::cnstr_get(x_1, 0);
x_3083 = lean::cnstr_get(x_1, 1);
x_3084 = lean::cnstr_get(x_1, 2);
x_3085 = lean::cnstr_get(x_1, 3);
x_3086 = lean::cnstr_get(x_4, 1);
x_3087 = lean::cnstr_get(x_4, 2);
x_3088 = lean::cnstr_get(x_4, 3);
lean::dec(x_3088);
x_3089 = lean::cnstr_get(x_4, 0);
lean::dec(x_3089);
x_3090 = !lean::is_exclusive(x_2788);
if (x_3090 == 0)
{
obj* x_3091; obj* x_3092; obj* x_3093; obj* x_3094; obj* x_3095; 
x_3091 = lean::cnstr_get(x_2788, 0);
x_3092 = lean::cnstr_get(x_2788, 1);
x_3093 = lean::cnstr_get(x_2788, 2);
x_3094 = lean::cnstr_get(x_2788, 3);
lean::cnstr_set(x_2788, 3, x_3085);
lean::cnstr_set(x_2788, 2, x_3084);
lean::cnstr_set(x_2788, 1, x_3083);
lean::cnstr_set(x_2788, 0, x_3082);
lean::cnstr_set_uint8(x_2788, sizeof(void*)*4, x_3027);
lean::cnstr_set(x_4, 3, x_3094);
lean::cnstr_set(x_4, 2, x_3093);
lean::cnstr_set(x_4, 1, x_3092);
lean::cnstr_set(x_4, 0, x_3091);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_3027);
lean::cnstr_set(x_1, 3, x_3004);
lean::cnstr_set(x_1, 2, x_3087);
lean::cnstr_set(x_1, 1, x_3086);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2787);
x_3095 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3095, 0, x_2788);
lean::cnstr_set(x_3095, 1, x_2);
lean::cnstr_set(x_3095, 2, x_3);
lean::cnstr_set(x_3095, 3, x_1);
lean::cnstr_set_uint8(x_3095, sizeof(void*)*4, x_3027);
return x_3095;
}
else
{
obj* x_3096; obj* x_3097; obj* x_3098; obj* x_3099; obj* x_3100; obj* x_3101; 
x_3096 = lean::cnstr_get(x_2788, 0);
x_3097 = lean::cnstr_get(x_2788, 1);
x_3098 = lean::cnstr_get(x_2788, 2);
x_3099 = lean::cnstr_get(x_2788, 3);
lean::inc(x_3099);
lean::inc(x_3098);
lean::inc(x_3097);
lean::inc(x_3096);
lean::dec(x_2788);
x_3100 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3100, 0, x_3082);
lean::cnstr_set(x_3100, 1, x_3083);
lean::cnstr_set(x_3100, 2, x_3084);
lean::cnstr_set(x_3100, 3, x_3085);
lean::cnstr_set_uint8(x_3100, sizeof(void*)*4, x_3027);
lean::cnstr_set(x_4, 3, x_3099);
lean::cnstr_set(x_4, 2, x_3098);
lean::cnstr_set(x_4, 1, x_3097);
lean::cnstr_set(x_4, 0, x_3096);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_3027);
lean::cnstr_set(x_1, 3, x_3004);
lean::cnstr_set(x_1, 2, x_3087);
lean::cnstr_set(x_1, 1, x_3086);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2787);
x_3101 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3101, 0, x_3100);
lean::cnstr_set(x_3101, 1, x_2);
lean::cnstr_set(x_3101, 2, x_3);
lean::cnstr_set(x_3101, 3, x_1);
lean::cnstr_set_uint8(x_3101, sizeof(void*)*4, x_3027);
return x_3101;
}
}
else
{
obj* x_3102; obj* x_3103; obj* x_3104; obj* x_3105; obj* x_3106; obj* x_3107; obj* x_3108; obj* x_3109; obj* x_3110; obj* x_3111; obj* x_3112; obj* x_3113; obj* x_3114; obj* x_3115; 
x_3102 = lean::cnstr_get(x_1, 0);
x_3103 = lean::cnstr_get(x_1, 1);
x_3104 = lean::cnstr_get(x_1, 2);
x_3105 = lean::cnstr_get(x_1, 3);
x_3106 = lean::cnstr_get(x_4, 1);
x_3107 = lean::cnstr_get(x_4, 2);
lean::inc(x_3107);
lean::inc(x_3106);
lean::dec(x_4);
x_3108 = lean::cnstr_get(x_2788, 0);
lean::inc(x_3108);
x_3109 = lean::cnstr_get(x_2788, 1);
lean::inc(x_3109);
x_3110 = lean::cnstr_get(x_2788, 2);
lean::inc(x_3110);
x_3111 = lean::cnstr_get(x_2788, 3);
lean::inc(x_3111);
if (lean::is_exclusive(x_2788)) {
 lean::cnstr_release(x_2788, 0);
 lean::cnstr_release(x_2788, 1);
 lean::cnstr_release(x_2788, 2);
 lean::cnstr_release(x_2788, 3);
 x_3112 = x_2788;
} else {
 lean::dec_ref(x_2788);
 x_3112 = lean::box(0);
}
if (lean::is_scalar(x_3112)) {
 x_3113 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_3113 = x_3112;
}
lean::cnstr_set(x_3113, 0, x_3102);
lean::cnstr_set(x_3113, 1, x_3103);
lean::cnstr_set(x_3113, 2, x_3104);
lean::cnstr_set(x_3113, 3, x_3105);
lean::cnstr_set_uint8(x_3113, sizeof(void*)*4, x_3027);
x_3114 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3114, 0, x_3108);
lean::cnstr_set(x_3114, 1, x_3109);
lean::cnstr_set(x_3114, 2, x_3110);
lean::cnstr_set(x_3114, 3, x_3111);
lean::cnstr_set_uint8(x_3114, sizeof(void*)*4, x_3027);
lean::cnstr_set(x_1, 3, x_3004);
lean::cnstr_set(x_1, 2, x_3107);
lean::cnstr_set(x_1, 1, x_3106);
lean::cnstr_set(x_1, 0, x_3114);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2787);
x_3115 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3115, 0, x_3113);
lean::cnstr_set(x_3115, 1, x_2);
lean::cnstr_set(x_3115, 2, x_3);
lean::cnstr_set(x_3115, 3, x_1);
lean::cnstr_set_uint8(x_3115, sizeof(void*)*4, x_3027);
return x_3115;
}
}
else
{
obj* x_3116; obj* x_3117; obj* x_3118; obj* x_3119; obj* x_3120; obj* x_3121; obj* x_3122; obj* x_3123; obj* x_3124; obj* x_3125; obj* x_3126; obj* x_3127; obj* x_3128; obj* x_3129; obj* x_3130; obj* x_3131; 
x_3116 = lean::cnstr_get(x_1, 0);
x_3117 = lean::cnstr_get(x_1, 1);
x_3118 = lean::cnstr_get(x_1, 2);
x_3119 = lean::cnstr_get(x_1, 3);
lean::inc(x_3119);
lean::inc(x_3118);
lean::inc(x_3117);
lean::inc(x_3116);
lean::dec(x_1);
x_3120 = lean::cnstr_get(x_4, 1);
lean::inc(x_3120);
x_3121 = lean::cnstr_get(x_4, 2);
lean::inc(x_3121);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_3122 = x_4;
} else {
 lean::dec_ref(x_4);
 x_3122 = lean::box(0);
}
x_3123 = lean::cnstr_get(x_2788, 0);
lean::inc(x_3123);
x_3124 = lean::cnstr_get(x_2788, 1);
lean::inc(x_3124);
x_3125 = lean::cnstr_get(x_2788, 2);
lean::inc(x_3125);
x_3126 = lean::cnstr_get(x_2788, 3);
lean::inc(x_3126);
if (lean::is_exclusive(x_2788)) {
 lean::cnstr_release(x_2788, 0);
 lean::cnstr_release(x_2788, 1);
 lean::cnstr_release(x_2788, 2);
 lean::cnstr_release(x_2788, 3);
 x_3127 = x_2788;
} else {
 lean::dec_ref(x_2788);
 x_3127 = lean::box(0);
}
if (lean::is_scalar(x_3127)) {
 x_3128 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_3128 = x_3127;
}
lean::cnstr_set(x_3128, 0, x_3116);
lean::cnstr_set(x_3128, 1, x_3117);
lean::cnstr_set(x_3128, 2, x_3118);
lean::cnstr_set(x_3128, 3, x_3119);
lean::cnstr_set_uint8(x_3128, sizeof(void*)*4, x_3027);
if (lean::is_scalar(x_3122)) {
 x_3129 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_3129 = x_3122;
}
lean::cnstr_set(x_3129, 0, x_3123);
lean::cnstr_set(x_3129, 1, x_3124);
lean::cnstr_set(x_3129, 2, x_3125);
lean::cnstr_set(x_3129, 3, x_3126);
lean::cnstr_set_uint8(x_3129, sizeof(void*)*4, x_3027);
x_3130 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3130, 0, x_3129);
lean::cnstr_set(x_3130, 1, x_3120);
lean::cnstr_set(x_3130, 2, x_3121);
lean::cnstr_set(x_3130, 3, x_3004);
lean::cnstr_set_uint8(x_3130, sizeof(void*)*4, x_2787);
x_3131 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3131, 0, x_3128);
lean::cnstr_set(x_3131, 1, x_2);
lean::cnstr_set(x_3131, 2, x_3);
lean::cnstr_set(x_3131, 3, x_3130);
lean::cnstr_set_uint8(x_3131, sizeof(void*)*4, x_3027);
return x_3131;
}
}
}
}
}
}
else
{
uint8 x_3132; 
x_3132 = !lean::is_exclusive(x_1);
if (x_3132 == 0)
{
obj* x_3133; 
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_2787);
x_3133 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3133, 0, x_1);
lean::cnstr_set(x_3133, 1, x_2);
lean::cnstr_set(x_3133, 2, x_3);
lean::cnstr_set(x_3133, 3, x_4);
lean::cnstr_set_uint8(x_3133, sizeof(void*)*4, x_2787);
return x_3133;
}
else
{
obj* x_3134; obj* x_3135; obj* x_3136; obj* x_3137; obj* x_3138; obj* x_3139; 
x_3134 = lean::cnstr_get(x_1, 0);
x_3135 = lean::cnstr_get(x_1, 1);
x_3136 = lean::cnstr_get(x_1, 2);
x_3137 = lean::cnstr_get(x_1, 3);
lean::inc(x_3137);
lean::inc(x_3136);
lean::inc(x_3135);
lean::inc(x_3134);
lean::dec(x_1);
x_3138 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3138, 0, x_3134);
lean::cnstr_set(x_3138, 1, x_3135);
lean::cnstr_set(x_3138, 2, x_3136);
lean::cnstr_set(x_3138, 3, x_3137);
lean::cnstr_set_uint8(x_3138, sizeof(void*)*4, x_2787);
x_3139 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_3139, 0, x_3138);
lean::cnstr_set(x_3139, 1, x_2);
lean::cnstr_set(x_3139, 2, x_3);
lean::cnstr_set(x_3139, 3, x_4);
lean::cnstr_set_uint8(x_3139, sizeof(void*)*4, x_2787);
return x_3139;
}
}
}
}
}
}
}
obj* l_RBNode_balance_u2083(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balance_u2083___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_balance_u2083___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_balance_u2083(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_setRed___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_1;
}
else
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 0;
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_3);
return x_1;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_5);
lean::inc(x_4);
lean::dec(x_1);
x_8 = 0;
x_9 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_5);
lean::cnstr_set(x_9, 2, x_6);
lean::cnstr_set(x_9, 3, x_7);
lean::cnstr_set_uint8(x_9, sizeof(void*)*4, x_8);
return x_9;
}
}
}
}
obj* l_RBNode_setRed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_setRed___rarg), 1, 0);
return x_3;
}
}
obj* l_RBNode_setRed___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_setRed(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_balLeft___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; obj* x_6; 
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_4);
lean::cnstr_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_uint8(x_4, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_2);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_4);
lean::cnstr_set_uint8(x_9, sizeof(void*)*4, x_7);
return x_9;
}
else
{
uint8 x_10; 
x_10 = lean::cnstr_get_uint8(x_8, sizeof(void*)*4);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_4);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_4, 0);
lean::dec(x_12);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_10);
x_13 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_2);
lean::cnstr_set(x_13, 2, x_3);
lean::cnstr_set(x_13, 3, x_4);
lean::cnstr_set_uint8(x_13, sizeof(void*)*4, x_10);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_4, 1);
x_15 = lean::cnstr_get(x_4, 2);
x_16 = lean::cnstr_get(x_4, 3);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_4);
x_17 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_17, 0, x_8);
lean::cnstr_set(x_17, 1, x_14);
lean::cnstr_set(x_17, 2, x_15);
lean::cnstr_set(x_17, 3, x_16);
lean::cnstr_set_uint8(x_17, sizeof(void*)*4, x_10);
x_18 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_18, 0, x_1);
lean::cnstr_set(x_18, 1, x_2);
lean::cnstr_set(x_18, 2, x_3);
lean::cnstr_set(x_18, 3, x_17);
lean::cnstr_set_uint8(x_18, sizeof(void*)*4, x_10);
return x_18;
}
}
else
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_4);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_20 = lean::cnstr_get(x_4, 1);
x_21 = lean::cnstr_get(x_4, 2);
x_22 = lean::cnstr_get(x_4, 3);
x_23 = lean::cnstr_get(x_4, 0);
lean::dec(x_23);
x_24 = !lean::is_exclusive(x_8);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_25 = lean::cnstr_get(x_8, 0);
x_26 = lean::cnstr_get(x_8, 1);
x_27 = lean::cnstr_get(x_8, 2);
x_28 = lean::cnstr_get(x_8, 3);
lean::cnstr_set(x_8, 3, x_25);
lean::cnstr_set(x_8, 2, x_3);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 0, x_1);
x_29 = l_RBNode_setRed___rarg(x_22);
x_30 = l_RBNode_balance_u2083___rarg(x_28, x_20, x_21, x_29);
lean::cnstr_set(x_4, 3, x_30);
lean::cnstr_set(x_4, 2, x_27);
lean::cnstr_set(x_4, 1, x_26);
return x_4;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_31 = lean::cnstr_get(x_8, 0);
x_32 = lean::cnstr_get(x_8, 1);
x_33 = lean::cnstr_get(x_8, 2);
x_34 = lean::cnstr_get(x_8, 3);
lean::inc(x_34);
lean::inc(x_33);
lean::inc(x_32);
lean::inc(x_31);
lean::dec(x_8);
x_35 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_35, 0, x_1);
lean::cnstr_set(x_35, 1, x_2);
lean::cnstr_set(x_35, 2, x_3);
lean::cnstr_set(x_35, 3, x_31);
lean::cnstr_set_uint8(x_35, sizeof(void*)*4, x_10);
x_36 = l_RBNode_setRed___rarg(x_22);
x_37 = l_RBNode_balance_u2083___rarg(x_34, x_20, x_21, x_36);
lean::cnstr_set(x_4, 3, x_37);
lean::cnstr_set(x_4, 2, x_33);
lean::cnstr_set(x_4, 1, x_32);
lean::cnstr_set(x_4, 0, x_35);
return x_4;
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_38 = lean::cnstr_get(x_4, 1);
x_39 = lean::cnstr_get(x_4, 2);
x_40 = lean::cnstr_get(x_4, 3);
lean::inc(x_40);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_4);
x_41 = lean::cnstr_get(x_8, 0);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_8, 1);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_8, 2);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_8, 3);
lean::inc(x_44);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 lean::cnstr_release(x_8, 3);
 x_45 = x_8;
} else {
 lean::dec_ref(x_8);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_1);
lean::cnstr_set(x_46, 1, x_2);
lean::cnstr_set(x_46, 2, x_3);
lean::cnstr_set(x_46, 3, x_41);
lean::cnstr_set_uint8(x_46, sizeof(void*)*4, x_10);
x_47 = l_RBNode_setRed___rarg(x_40);
x_48 = l_RBNode_balance_u2083___rarg(x_44, x_38, x_39, x_47);
x_49 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_49, 0, x_46);
lean::cnstr_set(x_49, 1, x_42);
lean::cnstr_set(x_49, 2, x_43);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_uint8(x_49, sizeof(void*)*4, x_7);
return x_49;
}
}
}
}
else
{
uint8 x_50; 
x_50 = !lean::is_exclusive(x_4);
if (x_50 == 0)
{
uint8 x_51; obj* x_52; 
x_51 = 0;
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_51);
x_52 = l_RBNode_balance_u2083___rarg(x_1, x_2, x_3, x_4);
return x_52;
}
else
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; uint8 x_57; obj* x_58; obj* x_59; 
x_53 = lean::cnstr_get(x_4, 0);
x_54 = lean::cnstr_get(x_4, 1);
x_55 = lean::cnstr_get(x_4, 2);
x_56 = lean::cnstr_get(x_4, 3);
lean::inc(x_56);
lean::inc(x_55);
lean::inc(x_54);
lean::inc(x_53);
lean::dec(x_4);
x_57 = 0;
x_58 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_58, 0, x_53);
lean::cnstr_set(x_58, 1, x_54);
lean::cnstr_set(x_58, 2, x_55);
lean::cnstr_set(x_58, 3, x_56);
lean::cnstr_set_uint8(x_58, sizeof(void*)*4, x_57);
x_59 = l_RBNode_balance_u2083___rarg(x_1, x_2, x_3, x_58);
return x_59;
}
}
}
}
else
{
uint8 x_60; 
x_60 = lean::cnstr_get_uint8(x_1, sizeof(void*)*4);
if (x_60 == 0)
{
uint8 x_61; 
x_61 = !lean::is_exclusive(x_1);
if (x_61 == 0)
{
uint8 x_62; obj* x_63; 
x_62 = 1;
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_62);
x_63 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_63, 0, x_1);
lean::cnstr_set(x_63, 1, x_2);
lean::cnstr_set(x_63, 2, x_3);
lean::cnstr_set(x_63, 3, x_4);
lean::cnstr_set_uint8(x_63, sizeof(void*)*4, x_60);
return x_63;
}
else
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; uint8 x_68; obj* x_69; obj* x_70; 
x_64 = lean::cnstr_get(x_1, 0);
x_65 = lean::cnstr_get(x_1, 1);
x_66 = lean::cnstr_get(x_1, 2);
x_67 = lean::cnstr_get(x_1, 3);
lean::inc(x_67);
lean::inc(x_66);
lean::inc(x_65);
lean::inc(x_64);
lean::dec(x_1);
x_68 = 1;
x_69 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_69, 0, x_64);
lean::cnstr_set(x_69, 1, x_65);
lean::cnstr_set(x_69, 2, x_66);
lean::cnstr_set(x_69, 3, x_67);
lean::cnstr_set_uint8(x_69, sizeof(void*)*4, x_68);
x_70 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_2);
lean::cnstr_set(x_70, 2, x_3);
lean::cnstr_set(x_70, 3, x_4);
lean::cnstr_set_uint8(x_70, sizeof(void*)*4, x_60);
return x_70;
}
}
else
{
if (lean::obj_tag(x_4) == 0)
{
uint8 x_71; obj* x_72; 
x_71 = 0;
x_72 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_72, 0, x_1);
lean::cnstr_set(x_72, 1, x_2);
lean::cnstr_set(x_72, 2, x_3);
lean::cnstr_set(x_72, 3, x_4);
lean::cnstr_set_uint8(x_72, sizeof(void*)*4, x_71);
return x_72;
}
else
{
uint8 x_73; 
x_73 = lean::cnstr_get_uint8(x_4, sizeof(void*)*4);
if (x_73 == 0)
{
obj* x_74; 
x_74 = lean::cnstr_get(x_4, 0);
lean::inc(x_74);
if (lean::obj_tag(x_74) == 0)
{
obj* x_75; 
x_75 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_75, 0, x_1);
lean::cnstr_set(x_75, 1, x_2);
lean::cnstr_set(x_75, 2, x_3);
lean::cnstr_set(x_75, 3, x_4);
lean::cnstr_set_uint8(x_75, sizeof(void*)*4, x_73);
return x_75;
}
else
{
uint8 x_76; 
x_76 = lean::cnstr_get_uint8(x_74, sizeof(void*)*4);
if (x_76 == 0)
{
uint8 x_77; 
x_77 = !lean::is_exclusive(x_4);
if (x_77 == 0)
{
obj* x_78; obj* x_79; 
x_78 = lean::cnstr_get(x_4, 0);
lean::dec(x_78);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_76);
x_79 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_79, 0, x_1);
lean::cnstr_set(x_79, 1, x_2);
lean::cnstr_set(x_79, 2, x_3);
lean::cnstr_set(x_79, 3, x_4);
lean::cnstr_set_uint8(x_79, sizeof(void*)*4, x_76);
return x_79;
}
else
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_80 = lean::cnstr_get(x_4, 1);
x_81 = lean::cnstr_get(x_4, 2);
x_82 = lean::cnstr_get(x_4, 3);
lean::inc(x_82);
lean::inc(x_81);
lean::inc(x_80);
lean::dec(x_4);
x_83 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_83, 0, x_74);
lean::cnstr_set(x_83, 1, x_80);
lean::cnstr_set(x_83, 2, x_81);
lean::cnstr_set(x_83, 3, x_82);
lean::cnstr_set_uint8(x_83, sizeof(void*)*4, x_76);
x_84 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_84, 0, x_1);
lean::cnstr_set(x_84, 1, x_2);
lean::cnstr_set(x_84, 2, x_3);
lean::cnstr_set(x_84, 3, x_83);
lean::cnstr_set_uint8(x_84, sizeof(void*)*4, x_76);
return x_84;
}
}
else
{
uint8 x_85; 
x_85 = !lean::is_exclusive(x_1);
if (x_85 == 0)
{
uint8 x_86; 
x_86 = !lean::is_exclusive(x_4);
if (x_86 == 0)
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; uint8 x_95; 
x_87 = lean::cnstr_get(x_1, 0);
x_88 = lean::cnstr_get(x_1, 1);
x_89 = lean::cnstr_get(x_1, 2);
x_90 = lean::cnstr_get(x_1, 3);
x_91 = lean::cnstr_get(x_4, 1);
x_92 = lean::cnstr_get(x_4, 2);
x_93 = lean::cnstr_get(x_4, 3);
x_94 = lean::cnstr_get(x_4, 0);
lean::dec(x_94);
x_95 = !lean::is_exclusive(x_74);
if (x_95 == 0)
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_96 = lean::cnstr_get(x_74, 0);
x_97 = lean::cnstr_get(x_74, 1);
x_98 = lean::cnstr_get(x_74, 2);
x_99 = lean::cnstr_get(x_74, 3);
lean::cnstr_set(x_74, 3, x_90);
lean::cnstr_set(x_74, 2, x_89);
lean::cnstr_set(x_74, 1, x_88);
lean::cnstr_set(x_74, 0, x_87);
lean::cnstr_set(x_4, 3, x_96);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_76);
x_100 = l_RBNode_setRed___rarg(x_93);
x_101 = l_RBNode_balance_u2083___rarg(x_99, x_91, x_92, x_100);
lean::cnstr_set(x_1, 3, x_101);
lean::cnstr_set(x_1, 2, x_98);
lean::cnstr_set(x_1, 1, x_97);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_73);
return x_1;
}
else
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_102 = lean::cnstr_get(x_74, 0);
x_103 = lean::cnstr_get(x_74, 1);
x_104 = lean::cnstr_get(x_74, 2);
x_105 = lean::cnstr_get(x_74, 3);
lean::inc(x_105);
lean::inc(x_104);
lean::inc(x_103);
lean::inc(x_102);
lean::dec(x_74);
x_106 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_106, 0, x_87);
lean::cnstr_set(x_106, 1, x_88);
lean::cnstr_set(x_106, 2, x_89);
lean::cnstr_set(x_106, 3, x_90);
lean::cnstr_set_uint8(x_106, sizeof(void*)*4, x_76);
lean::cnstr_set(x_4, 3, x_102);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 0, x_106);
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_76);
x_107 = l_RBNode_setRed___rarg(x_93);
x_108 = l_RBNode_balance_u2083___rarg(x_105, x_91, x_92, x_107);
lean::cnstr_set(x_1, 3, x_108);
lean::cnstr_set(x_1, 2, x_104);
lean::cnstr_set(x_1, 1, x_103);
lean::cnstr_set(x_1, 0, x_4);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_73);
return x_1;
}
}
else
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
x_109 = lean::cnstr_get(x_1, 0);
x_110 = lean::cnstr_get(x_1, 1);
x_111 = lean::cnstr_get(x_1, 2);
x_112 = lean::cnstr_get(x_1, 3);
x_113 = lean::cnstr_get(x_4, 1);
x_114 = lean::cnstr_get(x_4, 2);
x_115 = lean::cnstr_get(x_4, 3);
lean::inc(x_115);
lean::inc(x_114);
lean::inc(x_113);
lean::dec(x_4);
x_116 = lean::cnstr_get(x_74, 0);
lean::inc(x_116);
x_117 = lean::cnstr_get(x_74, 1);
lean::inc(x_117);
x_118 = lean::cnstr_get(x_74, 2);
lean::inc(x_118);
x_119 = lean::cnstr_get(x_74, 3);
lean::inc(x_119);
if (lean::is_exclusive(x_74)) {
 lean::cnstr_release(x_74, 0);
 lean::cnstr_release(x_74, 1);
 lean::cnstr_release(x_74, 2);
 lean::cnstr_release(x_74, 3);
 x_120 = x_74;
} else {
 lean::dec_ref(x_74);
 x_120 = lean::box(0);
}
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_109);
lean::cnstr_set(x_121, 1, x_110);
lean::cnstr_set(x_121, 2, x_111);
lean::cnstr_set(x_121, 3, x_112);
lean::cnstr_set_uint8(x_121, sizeof(void*)*4, x_76);
x_122 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_2);
lean::cnstr_set(x_122, 2, x_3);
lean::cnstr_set(x_122, 3, x_116);
lean::cnstr_set_uint8(x_122, sizeof(void*)*4, x_76);
x_123 = l_RBNode_setRed___rarg(x_115);
x_124 = l_RBNode_balance_u2083___rarg(x_119, x_113, x_114, x_123);
lean::cnstr_set(x_1, 3, x_124);
lean::cnstr_set(x_1, 2, x_118);
lean::cnstr_set(x_1, 1, x_117);
lean::cnstr_set(x_1, 0, x_122);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_73);
return x_1;
}
}
else
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_125 = lean::cnstr_get(x_1, 0);
x_126 = lean::cnstr_get(x_1, 1);
x_127 = lean::cnstr_get(x_1, 2);
x_128 = lean::cnstr_get(x_1, 3);
lean::inc(x_128);
lean::inc(x_127);
lean::inc(x_126);
lean::inc(x_125);
lean::dec(x_1);
x_129 = lean::cnstr_get(x_4, 1);
lean::inc(x_129);
x_130 = lean::cnstr_get(x_4, 2);
lean::inc(x_130);
x_131 = lean::cnstr_get(x_4, 3);
lean::inc(x_131);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_132 = x_4;
} else {
 lean::dec_ref(x_4);
 x_132 = lean::box(0);
}
x_133 = lean::cnstr_get(x_74, 0);
lean::inc(x_133);
x_134 = lean::cnstr_get(x_74, 1);
lean::inc(x_134);
x_135 = lean::cnstr_get(x_74, 2);
lean::inc(x_135);
x_136 = lean::cnstr_get(x_74, 3);
lean::inc(x_136);
if (lean::is_exclusive(x_74)) {
 lean::cnstr_release(x_74, 0);
 lean::cnstr_release(x_74, 1);
 lean::cnstr_release(x_74, 2);
 lean::cnstr_release(x_74, 3);
 x_137 = x_74;
} else {
 lean::dec_ref(x_74);
 x_137 = lean::box(0);
}
if (lean::is_scalar(x_137)) {
 x_138 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_138 = x_137;
}
lean::cnstr_set(x_138, 0, x_125);
lean::cnstr_set(x_138, 1, x_126);
lean::cnstr_set(x_138, 2, x_127);
lean::cnstr_set(x_138, 3, x_128);
lean::cnstr_set_uint8(x_138, sizeof(void*)*4, x_76);
if (lean::is_scalar(x_132)) {
 x_139 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_139 = x_132;
}
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_2);
lean::cnstr_set(x_139, 2, x_3);
lean::cnstr_set(x_139, 3, x_133);
lean::cnstr_set_uint8(x_139, sizeof(void*)*4, x_76);
x_140 = l_RBNode_setRed___rarg(x_131);
x_141 = l_RBNode_balance_u2083___rarg(x_136, x_129, x_130, x_140);
x_142 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_142, 0, x_139);
lean::cnstr_set(x_142, 1, x_134);
lean::cnstr_set(x_142, 2, x_135);
lean::cnstr_set(x_142, 3, x_141);
lean::cnstr_set_uint8(x_142, sizeof(void*)*4, x_73);
return x_142;
}
}
}
}
else
{
uint8 x_143; 
x_143 = !lean::is_exclusive(x_1);
if (x_143 == 0)
{
uint8 x_144; 
x_144 = !lean::is_exclusive(x_4);
if (x_144 == 0)
{
obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; uint8 x_153; obj* x_154; 
x_145 = lean::cnstr_get(x_1, 0);
x_146 = lean::cnstr_get(x_1, 1);
x_147 = lean::cnstr_get(x_1, 2);
x_148 = lean::cnstr_get(x_1, 3);
x_149 = lean::cnstr_get(x_4, 0);
x_150 = lean::cnstr_get(x_4, 1);
x_151 = lean::cnstr_get(x_4, 2);
x_152 = lean::cnstr_get(x_4, 3);
lean::cnstr_set(x_4, 3, x_148);
lean::cnstr_set(x_4, 2, x_147);
lean::cnstr_set(x_4, 1, x_146);
lean::cnstr_set(x_4, 0, x_145);
x_153 = 0;
lean::cnstr_set(x_1, 3, x_152);
lean::cnstr_set(x_1, 2, x_151);
lean::cnstr_set(x_1, 1, x_150);
lean::cnstr_set(x_1, 0, x_149);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_153);
x_154 = l_RBNode_balance_u2083___rarg(x_4, x_2, x_3, x_1);
return x_154;
}
else
{
obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; uint8 x_164; obj* x_165; 
x_155 = lean::cnstr_get(x_1, 0);
x_156 = lean::cnstr_get(x_1, 1);
x_157 = lean::cnstr_get(x_1, 2);
x_158 = lean::cnstr_get(x_1, 3);
x_159 = lean::cnstr_get(x_4, 0);
x_160 = lean::cnstr_get(x_4, 1);
x_161 = lean::cnstr_get(x_4, 2);
x_162 = lean::cnstr_get(x_4, 3);
lean::inc(x_162);
lean::inc(x_161);
lean::inc(x_160);
lean::inc(x_159);
lean::dec(x_4);
x_163 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_163, 0, x_155);
lean::cnstr_set(x_163, 1, x_156);
lean::cnstr_set(x_163, 2, x_157);
lean::cnstr_set(x_163, 3, x_158);
lean::cnstr_set_uint8(x_163, sizeof(void*)*4, x_73);
x_164 = 0;
lean::cnstr_set(x_1, 3, x_162);
lean::cnstr_set(x_1, 2, x_161);
lean::cnstr_set(x_1, 1, x_160);
lean::cnstr_set(x_1, 0, x_159);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_164);
x_165 = l_RBNode_balance_u2083___rarg(x_163, x_2, x_3, x_1);
return x_165;
}
}
else
{
obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; uint8 x_176; obj* x_177; obj* x_178; 
x_166 = lean::cnstr_get(x_1, 0);
x_167 = lean::cnstr_get(x_1, 1);
x_168 = lean::cnstr_get(x_1, 2);
x_169 = lean::cnstr_get(x_1, 3);
lean::inc(x_169);
lean::inc(x_168);
lean::inc(x_167);
lean::inc(x_166);
lean::dec(x_1);
x_170 = lean::cnstr_get(x_4, 0);
lean::inc(x_170);
x_171 = lean::cnstr_get(x_4, 1);
lean::inc(x_171);
x_172 = lean::cnstr_get(x_4, 2);
lean::inc(x_172);
x_173 = lean::cnstr_get(x_4, 3);
lean::inc(x_173);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 lean::cnstr_release(x_4, 3);
 x_174 = x_4;
} else {
 lean::dec_ref(x_4);
 x_174 = lean::box(0);
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_166);
lean::cnstr_set(x_175, 1, x_167);
lean::cnstr_set(x_175, 2, x_168);
lean::cnstr_set(x_175, 3, x_169);
lean::cnstr_set_uint8(x_175, sizeof(void*)*4, x_73);
x_176 = 0;
x_177 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_177, 0, x_170);
lean::cnstr_set(x_177, 1, x_171);
lean::cnstr_set(x_177, 2, x_172);
lean::cnstr_set(x_177, 3, x_173);
lean::cnstr_set_uint8(x_177, sizeof(void*)*4, x_176);
x_178 = l_RBNode_balance_u2083___rarg(x_175, x_2, x_3, x_177);
return x_178;
}
}
}
}
}
}
}
obj* l_RBNode_balLeft(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balLeft___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_balLeft___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_balLeft(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_balRight___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; 
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_4);
lean::cnstr_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_2);
lean::cnstr_set(x_9, 2, x_3);
lean::cnstr_set(x_9, 3, x_4);
lean::cnstr_set_uint8(x_9, sizeof(void*)*4, x_7);
return x_9;
}
else
{
uint8 x_10; 
x_10 = lean::cnstr_get_uint8(x_8, sizeof(void*)*4);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_8);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_8, 3);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_8, 2);
lean::dec(x_13);
x_14 = lean::cnstr_get(x_8, 1);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_8, 0);
lean::dec(x_15);
lean::cnstr_set(x_8, 3, x_4);
lean::cnstr_set(x_8, 2, x_3);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 0, x_1);
return x_8;
}
else
{
obj* x_16; 
lean::dec(x_8);
x_16 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_16, 0, x_1);
lean::cnstr_set(x_16, 1, x_2);
lean::cnstr_set(x_16, 2, x_3);
lean::cnstr_set(x_16, 3, x_4);
lean::cnstr_set_uint8(x_16, sizeof(void*)*4, x_10);
return x_16;
}
}
else
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_1);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; 
x_18 = lean::cnstr_get(x_1, 0);
x_19 = lean::cnstr_get(x_1, 1);
x_20 = lean::cnstr_get(x_1, 2);
x_21 = lean::cnstr_get(x_1, 3);
lean::dec(x_21);
x_22 = !lean::is_exclusive(x_8);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_8, 0);
x_24 = lean::cnstr_get(x_8, 1);
x_25 = lean::cnstr_get(x_8, 2);
x_26 = lean::cnstr_get(x_8, 3);
x_27 = l_RBNode_setRed___rarg(x_18);
x_28 = l_RBNode_balance_u2083___rarg(x_27, x_19, x_20, x_23);
lean::cnstr_set(x_8, 3, x_4);
lean::cnstr_set(x_8, 2, x_3);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 0, x_26);
lean::cnstr_set(x_1, 2, x_25);
lean::cnstr_set(x_1, 1, x_24);
lean::cnstr_set(x_1, 0, x_28);
return x_1;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_29 = lean::cnstr_get(x_8, 0);
x_30 = lean::cnstr_get(x_8, 1);
x_31 = lean::cnstr_get(x_8, 2);
x_32 = lean::cnstr_get(x_8, 3);
lean::inc(x_32);
lean::inc(x_31);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_8);
x_33 = l_RBNode_setRed___rarg(x_18);
x_34 = l_RBNode_balance_u2083___rarg(x_33, x_19, x_20, x_29);
x_35 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_2);
lean::cnstr_set(x_35, 2, x_3);
lean::cnstr_set(x_35, 3, x_4);
lean::cnstr_set_uint8(x_35, sizeof(void*)*4, x_10);
lean::cnstr_set(x_1, 3, x_35);
lean::cnstr_set(x_1, 2, x_31);
lean::cnstr_set(x_1, 1, x_30);
lean::cnstr_set(x_1, 0, x_34);
return x_1;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_36 = lean::cnstr_get(x_1, 0);
x_37 = lean::cnstr_get(x_1, 1);
x_38 = lean::cnstr_get(x_1, 2);
lean::inc(x_38);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_1);
x_39 = lean::cnstr_get(x_8, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_8, 1);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_8, 2);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_8, 3);
lean::inc(x_42);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 lean::cnstr_release(x_8, 3);
 x_43 = x_8;
} else {
 lean::dec_ref(x_8);
 x_43 = lean::box(0);
}
x_44 = l_RBNode_setRed___rarg(x_36);
x_45 = l_RBNode_balance_u2083___rarg(x_44, x_37, x_38, x_39);
if (lean::is_scalar(x_43)) {
 x_46 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_46 = x_43;
}
lean::cnstr_set(x_46, 0, x_42);
lean::cnstr_set(x_46, 1, x_2);
lean::cnstr_set(x_46, 2, x_3);
lean::cnstr_set(x_46, 3, x_4);
lean::cnstr_set_uint8(x_46, sizeof(void*)*4, x_10);
x_47 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_40);
lean::cnstr_set(x_47, 2, x_41);
lean::cnstr_set(x_47, 3, x_46);
lean::cnstr_set_uint8(x_47, sizeof(void*)*4, x_7);
return x_47;
}
}
}
}
else
{
uint8 x_48; 
x_48 = !lean::is_exclusive(x_1);
if (x_48 == 0)
{
uint8 x_49; obj* x_50; 
x_49 = 0;
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_49);
x_50 = l_RBNode_balance_u2083___rarg(x_1, x_2, x_3, x_4);
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; uint8 x_55; obj* x_56; obj* x_57; 
x_51 = lean::cnstr_get(x_1, 0);
x_52 = lean::cnstr_get(x_1, 1);
x_53 = lean::cnstr_get(x_1, 2);
x_54 = lean::cnstr_get(x_1, 3);
lean::inc(x_54);
lean::inc(x_53);
lean::inc(x_52);
lean::inc(x_51);
lean::dec(x_1);
x_55 = 0;
x_56 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_56, 0, x_51);
lean::cnstr_set(x_56, 1, x_52);
lean::cnstr_set(x_56, 2, x_53);
lean::cnstr_set(x_56, 3, x_54);
lean::cnstr_set_uint8(x_56, sizeof(void*)*4, x_55);
x_57 = l_RBNode_balance_u2083___rarg(x_56, x_2, x_3, x_4);
return x_57;
}
}
}
}
else
{
uint8 x_58; 
x_58 = lean::cnstr_get_uint8(x_4, sizeof(void*)*4);
if (x_58 == 0)
{
uint8 x_59; 
x_59 = !lean::is_exclusive(x_4);
if (x_59 == 0)
{
uint8 x_60; obj* x_61; 
x_60 = 1;
lean::cnstr_set_uint8(x_4, sizeof(void*)*4, x_60);
x_61 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_61, 0, x_1);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_4);
lean::cnstr_set_uint8(x_61, sizeof(void*)*4, x_58);
return x_61;
}
else
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; uint8 x_66; obj* x_67; obj* x_68; 
x_62 = lean::cnstr_get(x_4, 0);
x_63 = lean::cnstr_get(x_4, 1);
x_64 = lean::cnstr_get(x_4, 2);
x_65 = lean::cnstr_get(x_4, 3);
lean::inc(x_65);
lean::inc(x_64);
lean::inc(x_63);
lean::inc(x_62);
lean::dec(x_4);
x_66 = 1;
x_67 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_67, 0, x_62);
lean::cnstr_set(x_67, 1, x_63);
lean::cnstr_set(x_67, 2, x_64);
lean::cnstr_set(x_67, 3, x_65);
lean::cnstr_set_uint8(x_67, sizeof(void*)*4, x_66);
x_68 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_68, 0, x_1);
lean::cnstr_set(x_68, 1, x_2);
lean::cnstr_set(x_68, 2, x_3);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_uint8(x_68, sizeof(void*)*4, x_58);
return x_68;
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_69; obj* x_70; 
x_69 = 0;
x_70 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_70, 0, x_1);
lean::cnstr_set(x_70, 1, x_2);
lean::cnstr_set(x_70, 2, x_3);
lean::cnstr_set(x_70, 3, x_4);
lean::cnstr_set_uint8(x_70, sizeof(void*)*4, x_69);
return x_70;
}
else
{
uint8 x_71; 
x_71 = lean::cnstr_get_uint8(x_1, sizeof(void*)*4);
if (x_71 == 0)
{
obj* x_72; 
x_72 = lean::cnstr_get(x_1, 3);
lean::inc(x_72);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; 
x_73 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_73, 0, x_1);
lean::cnstr_set(x_73, 1, x_2);
lean::cnstr_set(x_73, 2, x_3);
lean::cnstr_set(x_73, 3, x_4);
lean::cnstr_set_uint8(x_73, sizeof(void*)*4, x_71);
return x_73;
}
else
{
uint8 x_74; 
x_74 = lean::cnstr_get_uint8(x_72, sizeof(void*)*4);
if (x_74 == 0)
{
uint8 x_75; 
x_75 = !lean::is_exclusive(x_72);
if (x_75 == 0)
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_76 = lean::cnstr_get(x_72, 3);
lean::dec(x_76);
x_77 = lean::cnstr_get(x_72, 2);
lean::dec(x_77);
x_78 = lean::cnstr_get(x_72, 1);
lean::dec(x_78);
x_79 = lean::cnstr_get(x_72, 0);
lean::dec(x_79);
lean::cnstr_set(x_72, 3, x_4);
lean::cnstr_set(x_72, 2, x_3);
lean::cnstr_set(x_72, 1, x_2);
lean::cnstr_set(x_72, 0, x_1);
return x_72;
}
else
{
obj* x_80; 
lean::dec(x_72);
x_80 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_80, 0, x_1);
lean::cnstr_set(x_80, 1, x_2);
lean::cnstr_set(x_80, 2, x_3);
lean::cnstr_set(x_80, 3, x_4);
lean::cnstr_set_uint8(x_80, sizeof(void*)*4, x_74);
return x_80;
}
}
else
{
uint8 x_81; 
x_81 = !lean::is_exclusive(x_1);
if (x_81 == 0)
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; uint8 x_86; 
x_82 = lean::cnstr_get(x_1, 0);
x_83 = lean::cnstr_get(x_1, 1);
x_84 = lean::cnstr_get(x_1, 2);
x_85 = lean::cnstr_get(x_1, 3);
lean::dec(x_85);
x_86 = !lean::is_exclusive(x_72);
if (x_86 == 0)
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_87 = lean::cnstr_get(x_72, 0);
x_88 = lean::cnstr_get(x_72, 1);
x_89 = lean::cnstr_get(x_72, 2);
x_90 = lean::cnstr_get(x_72, 3);
x_91 = l_RBNode_setRed___rarg(x_82);
x_92 = l_RBNode_balance_u2083___rarg(x_91, x_83, x_84, x_87);
lean::cnstr_set(x_72, 3, x_4);
lean::cnstr_set(x_72, 2, x_3);
lean::cnstr_set(x_72, 1, x_2);
lean::cnstr_set(x_72, 0, x_90);
lean::cnstr_set(x_1, 2, x_89);
lean::cnstr_set(x_1, 1, x_88);
lean::cnstr_set(x_1, 0, x_92);
return x_1;
}
else
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_93 = lean::cnstr_get(x_72, 0);
x_94 = lean::cnstr_get(x_72, 1);
x_95 = lean::cnstr_get(x_72, 2);
x_96 = lean::cnstr_get(x_72, 3);
lean::inc(x_96);
lean::inc(x_95);
lean::inc(x_94);
lean::inc(x_93);
lean::dec(x_72);
x_97 = l_RBNode_setRed___rarg(x_82);
x_98 = l_RBNode_balance_u2083___rarg(x_97, x_83, x_84, x_93);
x_99 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_99, 0, x_96);
lean::cnstr_set(x_99, 1, x_2);
lean::cnstr_set(x_99, 2, x_3);
lean::cnstr_set(x_99, 3, x_4);
lean::cnstr_set_uint8(x_99, sizeof(void*)*4, x_74);
lean::cnstr_set(x_1, 3, x_99);
lean::cnstr_set(x_1, 2, x_95);
lean::cnstr_set(x_1, 1, x_94);
lean::cnstr_set(x_1, 0, x_98);
return x_1;
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
x_100 = lean::cnstr_get(x_1, 0);
x_101 = lean::cnstr_get(x_1, 1);
x_102 = lean::cnstr_get(x_1, 2);
lean::inc(x_102);
lean::inc(x_101);
lean::inc(x_100);
lean::dec(x_1);
x_103 = lean::cnstr_get(x_72, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_72, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_72, 2);
lean::inc(x_105);
x_106 = lean::cnstr_get(x_72, 3);
lean::inc(x_106);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 lean::cnstr_release(x_72, 1);
 lean::cnstr_release(x_72, 2);
 lean::cnstr_release(x_72, 3);
 x_107 = x_72;
} else {
 lean::dec_ref(x_72);
 x_107 = lean::box(0);
}
x_108 = l_RBNode_setRed___rarg(x_100);
x_109 = l_RBNode_balance_u2083___rarg(x_108, x_101, x_102, x_103);
if (lean::is_scalar(x_107)) {
 x_110 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_110 = x_107;
}
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set(x_110, 1, x_2);
lean::cnstr_set(x_110, 2, x_3);
lean::cnstr_set(x_110, 3, x_4);
lean::cnstr_set_uint8(x_110, sizeof(void*)*4, x_74);
x_111 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_111, 0, x_109);
lean::cnstr_set(x_111, 1, x_104);
lean::cnstr_set(x_111, 2, x_105);
lean::cnstr_set(x_111, 3, x_110);
lean::cnstr_set_uint8(x_111, sizeof(void*)*4, x_71);
return x_111;
}
}
}
}
else
{
uint8 x_112; 
x_112 = !lean::is_exclusive(x_1);
if (x_112 == 0)
{
uint8 x_113; obj* x_114; 
x_113 = 0;
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_113);
x_114 = l_RBNode_balance_u2083___rarg(x_1, x_2, x_3, x_4);
return x_114;
}
else
{
obj* x_115; obj* x_116; obj* x_117; obj* x_118; uint8 x_119; obj* x_120; obj* x_121; 
x_115 = lean::cnstr_get(x_1, 0);
x_116 = lean::cnstr_get(x_1, 1);
x_117 = lean::cnstr_get(x_1, 2);
x_118 = lean::cnstr_get(x_1, 3);
lean::inc(x_118);
lean::inc(x_117);
lean::inc(x_116);
lean::inc(x_115);
lean::dec(x_1);
x_119 = 0;
x_120 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_120, 0, x_115);
lean::cnstr_set(x_120, 1, x_116);
lean::cnstr_set(x_120, 2, x_117);
lean::cnstr_set(x_120, 3, x_118);
lean::cnstr_set_uint8(x_120, sizeof(void*)*4, x_119);
x_121 = l_RBNode_balance_u2083___rarg(x_120, x_2, x_3, x_4);
return x_121;
}
}
}
}
}
}
}
obj* l_RBNode_balRight(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balRight___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_balRight___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_balRight(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_appendTrees___main___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_2;
}
else
{
uint8 x_3; 
x_3 = lean::cnstr_get_uint8(x_1, sizeof(void*)*4);
if (x_3 == 0)
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8 x_4; 
x_4 = lean::cnstr_get_uint8(x_2, sizeof(void*)*4);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_1);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_2);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
x_9 = lean::cnstr_get(x_1, 2);
x_10 = lean::cnstr_get(x_1, 3);
x_11 = lean::cnstr_get(x_2, 0);
x_12 = l_RBNode_appendTrees___main___rarg(x_10, x_11);
if (lean::obj_tag(x_12) == 0)
{
lean::cnstr_set(x_2, 0, x_12);
lean::cnstr_set(x_1, 3, x_2);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_4);
return x_1;
}
else
{
uint8 x_13; 
x_13 = lean::cnstr_get_uint8(x_12, sizeof(void*)*4);
if (x_13 == 0)
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_12);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_12, 0);
x_16 = lean::cnstr_get(x_12, 1);
x_17 = lean::cnstr_get(x_12, 2);
x_18 = lean::cnstr_get(x_12, 3);
lean::cnstr_set(x_12, 3, x_15);
lean::cnstr_set(x_12, 2, x_9);
lean::cnstr_set(x_12, 1, x_8);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_2, 0, x_18);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_13);
lean::cnstr_set(x_1, 3, x_2);
lean::cnstr_set(x_1, 2, x_17);
lean::cnstr_set(x_1, 1, x_16);
lean::cnstr_set(x_1, 0, x_12);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_13);
return x_1;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_12, 0);
x_20 = lean::cnstr_get(x_12, 1);
x_21 = lean::cnstr_get(x_12, 2);
x_22 = lean::cnstr_get(x_12, 3);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_12);
x_23 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_8);
lean::cnstr_set(x_23, 2, x_9);
lean::cnstr_set(x_23, 3, x_19);
lean::cnstr_set_uint8(x_23, sizeof(void*)*4, x_13);
lean::cnstr_set(x_2, 0, x_22);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_13);
lean::cnstr_set(x_1, 3, x_2);
lean::cnstr_set(x_1, 2, x_21);
lean::cnstr_set(x_1, 1, x_20);
lean::cnstr_set(x_1, 0, x_23);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_13);
return x_1;
}
}
else
{
lean::cnstr_set(x_2, 0, x_12);
lean::cnstr_set(x_1, 3, x_2);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_4);
return x_1;
}
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_24 = lean::cnstr_get(x_1, 0);
x_25 = lean::cnstr_get(x_1, 1);
x_26 = lean::cnstr_get(x_1, 2);
x_27 = lean::cnstr_get(x_1, 3);
x_28 = lean::cnstr_get(x_2, 0);
x_29 = lean::cnstr_get(x_2, 1);
x_30 = lean::cnstr_get(x_2, 2);
x_31 = lean::cnstr_get(x_2, 3);
lean::inc(x_31);
lean::inc(x_30);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_2);
x_32 = l_RBNode_appendTrees___main___rarg(x_27, x_28);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; 
x_33 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_29);
lean::cnstr_set(x_33, 2, x_30);
lean::cnstr_set(x_33, 3, x_31);
lean::cnstr_set_uint8(x_33, sizeof(void*)*4, x_4);
lean::cnstr_set(x_1, 3, x_33);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_4);
return x_1;
}
else
{
uint8 x_34; 
x_34 = lean::cnstr_get_uint8(x_32, sizeof(void*)*4);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
x_36 = lean::cnstr_get(x_32, 1);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_32, 2);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_32, 3);
lean::inc(x_38);
if (lean::is_exclusive(x_32)) {
 lean::cnstr_release(x_32, 0);
 lean::cnstr_release(x_32, 1);
 lean::cnstr_release(x_32, 2);
 lean::cnstr_release(x_32, 3);
 x_39 = x_32;
} else {
 lean::dec_ref(x_32);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_24);
lean::cnstr_set(x_40, 1, x_25);
lean::cnstr_set(x_40, 2, x_26);
lean::cnstr_set(x_40, 3, x_35);
lean::cnstr_set_uint8(x_40, sizeof(void*)*4, x_34);
x_41 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set(x_41, 1, x_29);
lean::cnstr_set(x_41, 2, x_30);
lean::cnstr_set(x_41, 3, x_31);
lean::cnstr_set_uint8(x_41, sizeof(void*)*4, x_34);
lean::cnstr_set(x_1, 3, x_41);
lean::cnstr_set(x_1, 2, x_37);
lean::cnstr_set(x_1, 1, x_36);
lean::cnstr_set(x_1, 0, x_40);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_34);
return x_1;
}
else
{
obj* x_42; 
x_42 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_42, 0, x_32);
lean::cnstr_set(x_42, 1, x_29);
lean::cnstr_set(x_42, 2, x_30);
lean::cnstr_set(x_42, 3, x_31);
lean::cnstr_set_uint8(x_42, sizeof(void*)*4, x_4);
lean::cnstr_set(x_1, 3, x_42);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_4);
return x_1;
}
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_43 = lean::cnstr_get(x_1, 0);
x_44 = lean::cnstr_get(x_1, 1);
x_45 = lean::cnstr_get(x_1, 2);
x_46 = lean::cnstr_get(x_1, 3);
lean::inc(x_46);
lean::inc(x_45);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_1);
x_47 = lean::cnstr_get(x_2, 0);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_2, 1);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_2, 2);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_2, 3);
lean::inc(x_50);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 lean::cnstr_release(x_2, 3);
 x_51 = x_2;
} else {
 lean::dec_ref(x_2);
 x_51 = lean::box(0);
}
x_52 = l_RBNode_appendTrees___main___rarg(x_46, x_47);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_54; 
if (lean::is_scalar(x_51)) {
 x_53 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_53 = x_51;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_48);
lean::cnstr_set(x_53, 2, x_49);
lean::cnstr_set(x_53, 3, x_50);
lean::cnstr_set_uint8(x_53, sizeof(void*)*4, x_4);
x_54 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_54, 0, x_43);
lean::cnstr_set(x_54, 1, x_44);
lean::cnstr_set(x_54, 2, x_45);
lean::cnstr_set(x_54, 3, x_53);
lean::cnstr_set_uint8(x_54, sizeof(void*)*4, x_4);
return x_54;
}
else
{
uint8 x_55; 
x_55 = lean::cnstr_get_uint8(x_52, sizeof(void*)*4);
if (x_55 == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_56 = lean::cnstr_get(x_52, 0);
lean::inc(x_56);
x_57 = lean::cnstr_get(x_52, 1);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_52, 2);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_52, 3);
lean::inc(x_59);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 lean::cnstr_release(x_52, 2);
 lean::cnstr_release(x_52, 3);
 x_60 = x_52;
} else {
 lean::dec_ref(x_52);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_43);
lean::cnstr_set(x_61, 1, x_44);
lean::cnstr_set(x_61, 2, x_45);
lean::cnstr_set(x_61, 3, x_56);
lean::cnstr_set_uint8(x_61, sizeof(void*)*4, x_55);
if (lean::is_scalar(x_51)) {
 x_62 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_62 = x_51;
}
lean::cnstr_set(x_62, 0, x_59);
lean::cnstr_set(x_62, 1, x_48);
lean::cnstr_set(x_62, 2, x_49);
lean::cnstr_set(x_62, 3, x_50);
lean::cnstr_set_uint8(x_62, sizeof(void*)*4, x_55);
x_63 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_63, 0, x_61);
lean::cnstr_set(x_63, 1, x_57);
lean::cnstr_set(x_63, 2, x_58);
lean::cnstr_set(x_63, 3, x_62);
lean::cnstr_set_uint8(x_63, sizeof(void*)*4, x_55);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
if (lean::is_scalar(x_51)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_51;
}
lean::cnstr_set(x_64, 0, x_52);
lean::cnstr_set(x_64, 1, x_48);
lean::cnstr_set(x_64, 2, x_49);
lean::cnstr_set(x_64, 3, x_50);
lean::cnstr_set_uint8(x_64, sizeof(void*)*4, x_4);
x_65 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_65, 0, x_43);
lean::cnstr_set(x_65, 1, x_44);
lean::cnstr_set(x_65, 2, x_45);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_uint8(x_65, sizeof(void*)*4, x_4);
return x_65;
}
}
}
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; uint8 x_71; 
x_66 = lean::cnstr_get(x_1, 0);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_1, 1);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_1, 2);
lean::inc(x_68);
x_69 = lean::cnstr_get(x_1, 3);
lean::inc(x_69);
lean::dec(x_1);
lean::inc(x_2);
x_70 = l_RBNode_appendTrees___main___rarg(x_69, x_2);
x_71 = !lean::is_exclusive(x_2);
if (x_71 == 0)
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_72 = lean::cnstr_get(x_2, 3);
lean::dec(x_72);
x_73 = lean::cnstr_get(x_2, 2);
lean::dec(x_73);
x_74 = lean::cnstr_get(x_2, 1);
lean::dec(x_74);
x_75 = lean::cnstr_get(x_2, 0);
lean::dec(x_75);
lean::cnstr_set(x_2, 3, x_70);
lean::cnstr_set(x_2, 2, x_68);
lean::cnstr_set(x_2, 1, x_67);
lean::cnstr_set(x_2, 0, x_66);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_3);
return x_2;
}
else
{
obj* x_76; 
lean::dec(x_2);
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_66);
lean::cnstr_set(x_76, 1, x_67);
lean::cnstr_set(x_76, 2, x_68);
lean::cnstr_set(x_76, 3, x_70);
lean::cnstr_set_uint8(x_76, sizeof(void*)*4, x_3);
return x_76;
}
}
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8 x_77; 
x_77 = lean::cnstr_get_uint8(x_2, sizeof(void*)*4);
if (x_77 == 0)
{
uint8 x_78; 
x_78 = !lean::is_exclusive(x_2);
if (x_78 == 0)
{
obj* x_79; obj* x_80; 
x_79 = lean::cnstr_get(x_2, 0);
x_80 = l_RBNode_appendTrees___main___rarg(x_1, x_79);
lean::cnstr_set(x_2, 0, x_80);
return x_2;
}
else
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_81 = lean::cnstr_get(x_2, 0);
x_82 = lean::cnstr_get(x_2, 1);
x_83 = lean::cnstr_get(x_2, 2);
x_84 = lean::cnstr_get(x_2, 3);
lean::inc(x_84);
lean::inc(x_83);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_2);
x_85 = l_RBNode_appendTrees___main___rarg(x_1, x_81);
x_86 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_82);
lean::cnstr_set(x_86, 2, x_83);
lean::cnstr_set(x_86, 3, x_84);
lean::cnstr_set_uint8(x_86, sizeof(void*)*4, x_77);
return x_86;
}
}
else
{
uint8 x_87; 
x_87 = !lean::is_exclusive(x_1);
if (x_87 == 0)
{
uint8 x_88; 
x_88 = !lean::is_exclusive(x_2);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_89 = lean::cnstr_get(x_1, 0);
x_90 = lean::cnstr_get(x_1, 1);
x_91 = lean::cnstr_get(x_1, 2);
x_92 = lean::cnstr_get(x_1, 3);
x_93 = lean::cnstr_get(x_2, 0);
x_94 = l_RBNode_appendTrees___main___rarg(x_92, x_93);
if (lean::obj_tag(x_94) == 0)
{
obj* x_95; 
lean::free_heap_obj(x_1);
lean::cnstr_set(x_2, 0, x_94);
x_95 = l_RBNode_balLeft___rarg(x_89, x_90, x_91, x_2);
return x_95;
}
else
{
uint8 x_96; 
x_96 = lean::cnstr_get_uint8(x_94, sizeof(void*)*4);
if (x_96 == 0)
{
uint8 x_97; 
x_97 = !lean::is_exclusive(x_94);
if (x_97 == 0)
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_98 = lean::cnstr_get(x_94, 0);
x_99 = lean::cnstr_get(x_94, 1);
x_100 = lean::cnstr_get(x_94, 2);
x_101 = lean::cnstr_get(x_94, 3);
lean::cnstr_set(x_94, 3, x_98);
lean::cnstr_set(x_94, 2, x_91);
lean::cnstr_set(x_94, 1, x_90);
lean::cnstr_set(x_94, 0, x_89);
lean::cnstr_set_uint8(x_94, sizeof(void*)*4, x_77);
lean::cnstr_set(x_2, 0, x_101);
lean::cnstr_set(x_1, 3, x_2);
lean::cnstr_set(x_1, 2, x_100);
lean::cnstr_set(x_1, 1, x_99);
lean::cnstr_set(x_1, 0, x_94);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_96);
return x_1;
}
else
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_102 = lean::cnstr_get(x_94, 0);
x_103 = lean::cnstr_get(x_94, 1);
x_104 = lean::cnstr_get(x_94, 2);
x_105 = lean::cnstr_get(x_94, 3);
lean::inc(x_105);
lean::inc(x_104);
lean::inc(x_103);
lean::inc(x_102);
lean::dec(x_94);
x_106 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_106, 0, x_89);
lean::cnstr_set(x_106, 1, x_90);
lean::cnstr_set(x_106, 2, x_91);
lean::cnstr_set(x_106, 3, x_102);
lean::cnstr_set_uint8(x_106, sizeof(void*)*4, x_77);
lean::cnstr_set(x_2, 0, x_105);
lean::cnstr_set(x_1, 3, x_2);
lean::cnstr_set(x_1, 2, x_104);
lean::cnstr_set(x_1, 1, x_103);
lean::cnstr_set(x_1, 0, x_106);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_96);
return x_1;
}
}
else
{
obj* x_107; 
lean::free_heap_obj(x_1);
lean::cnstr_set(x_2, 0, x_94);
lean::cnstr_set_uint8(x_2, sizeof(void*)*4, x_96);
x_107 = l_RBNode_balLeft___rarg(x_89, x_90, x_91, x_2);
return x_107;
}
}
}
else
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
x_108 = lean::cnstr_get(x_1, 0);
x_109 = lean::cnstr_get(x_1, 1);
x_110 = lean::cnstr_get(x_1, 2);
x_111 = lean::cnstr_get(x_1, 3);
x_112 = lean::cnstr_get(x_2, 0);
x_113 = lean::cnstr_get(x_2, 1);
x_114 = lean::cnstr_get(x_2, 2);
x_115 = lean::cnstr_get(x_2, 3);
lean::inc(x_115);
lean::inc(x_114);
lean::inc(x_113);
lean::inc(x_112);
lean::dec(x_2);
x_116 = l_RBNode_appendTrees___main___rarg(x_111, x_112);
if (lean::obj_tag(x_116) == 0)
{
obj* x_117; obj* x_118; 
lean::free_heap_obj(x_1);
x_117 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_113);
lean::cnstr_set(x_117, 2, x_114);
lean::cnstr_set(x_117, 3, x_115);
lean::cnstr_set_uint8(x_117, sizeof(void*)*4, x_77);
x_118 = l_RBNode_balLeft___rarg(x_108, x_109, x_110, x_117);
return x_118;
}
else
{
uint8 x_119; 
x_119 = lean::cnstr_get_uint8(x_116, sizeof(void*)*4);
if (x_119 == 0)
{
obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
x_120 = lean::cnstr_get(x_116, 0);
lean::inc(x_120);
x_121 = lean::cnstr_get(x_116, 1);
lean::inc(x_121);
x_122 = lean::cnstr_get(x_116, 2);
lean::inc(x_122);
x_123 = lean::cnstr_get(x_116, 3);
lean::inc(x_123);
if (lean::is_exclusive(x_116)) {
 lean::cnstr_release(x_116, 0);
 lean::cnstr_release(x_116, 1);
 lean::cnstr_release(x_116, 2);
 lean::cnstr_release(x_116, 3);
 x_124 = x_116;
} else {
 lean::dec_ref(x_116);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_108);
lean::cnstr_set(x_125, 1, x_109);
lean::cnstr_set(x_125, 2, x_110);
lean::cnstr_set(x_125, 3, x_120);
lean::cnstr_set_uint8(x_125, sizeof(void*)*4, x_77);
x_126 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_126, 0, x_123);
lean::cnstr_set(x_126, 1, x_113);
lean::cnstr_set(x_126, 2, x_114);
lean::cnstr_set(x_126, 3, x_115);
lean::cnstr_set_uint8(x_126, sizeof(void*)*4, x_77);
lean::cnstr_set(x_1, 3, x_126);
lean::cnstr_set(x_1, 2, x_122);
lean::cnstr_set(x_1, 1, x_121);
lean::cnstr_set(x_1, 0, x_125);
lean::cnstr_set_uint8(x_1, sizeof(void*)*4, x_119);
return x_1;
}
else
{
obj* x_127; obj* x_128; 
lean::free_heap_obj(x_1);
x_127 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_127, 0, x_116);
lean::cnstr_set(x_127, 1, x_113);
lean::cnstr_set(x_127, 2, x_114);
lean::cnstr_set(x_127, 3, x_115);
lean::cnstr_set_uint8(x_127, sizeof(void*)*4, x_119);
x_128 = l_RBNode_balLeft___rarg(x_108, x_109, x_110, x_127);
return x_128;
}
}
}
}
else
{
obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
x_129 = lean::cnstr_get(x_1, 0);
x_130 = lean::cnstr_get(x_1, 1);
x_131 = lean::cnstr_get(x_1, 2);
x_132 = lean::cnstr_get(x_1, 3);
lean::inc(x_132);
lean::inc(x_131);
lean::inc(x_130);
lean::inc(x_129);
lean::dec(x_1);
x_133 = lean::cnstr_get(x_2, 0);
lean::inc(x_133);
x_134 = lean::cnstr_get(x_2, 1);
lean::inc(x_134);
x_135 = lean::cnstr_get(x_2, 2);
lean::inc(x_135);
x_136 = lean::cnstr_get(x_2, 3);
lean::inc(x_136);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 lean::cnstr_release(x_2, 3);
 x_137 = x_2;
} else {
 lean::dec_ref(x_2);
 x_137 = lean::box(0);
}
x_138 = l_RBNode_appendTrees___main___rarg(x_132, x_133);
if (lean::obj_tag(x_138) == 0)
{
obj* x_139; obj* x_140; 
if (lean::is_scalar(x_137)) {
 x_139 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_139 = x_137;
}
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_134);
lean::cnstr_set(x_139, 2, x_135);
lean::cnstr_set(x_139, 3, x_136);
lean::cnstr_set_uint8(x_139, sizeof(void*)*4, x_77);
x_140 = l_RBNode_balLeft___rarg(x_129, x_130, x_131, x_139);
return x_140;
}
else
{
uint8 x_141; 
x_141 = lean::cnstr_get_uint8(x_138, sizeof(void*)*4);
if (x_141 == 0)
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
x_142 = lean::cnstr_get(x_138, 0);
lean::inc(x_142);
x_143 = lean::cnstr_get(x_138, 1);
lean::inc(x_143);
x_144 = lean::cnstr_get(x_138, 2);
lean::inc(x_144);
x_145 = lean::cnstr_get(x_138, 3);
lean::inc(x_145);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 lean::cnstr_release(x_138, 1);
 lean::cnstr_release(x_138, 2);
 lean::cnstr_release(x_138, 3);
 x_146 = x_138;
} else {
 lean::dec_ref(x_138);
 x_146 = lean::box(0);
}
if (lean::is_scalar(x_146)) {
 x_147 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_147 = x_146;
}
lean::cnstr_set(x_147, 0, x_129);
lean::cnstr_set(x_147, 1, x_130);
lean::cnstr_set(x_147, 2, x_131);
lean::cnstr_set(x_147, 3, x_142);
lean::cnstr_set_uint8(x_147, sizeof(void*)*4, x_77);
if (lean::is_scalar(x_137)) {
 x_148 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_148 = x_137;
}
lean::cnstr_set(x_148, 0, x_145);
lean::cnstr_set(x_148, 1, x_134);
lean::cnstr_set(x_148, 2, x_135);
lean::cnstr_set(x_148, 3, x_136);
lean::cnstr_set_uint8(x_148, sizeof(void*)*4, x_77);
x_149 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_149, 0, x_147);
lean::cnstr_set(x_149, 1, x_143);
lean::cnstr_set(x_149, 2, x_144);
lean::cnstr_set(x_149, 3, x_148);
lean::cnstr_set_uint8(x_149, sizeof(void*)*4, x_141);
return x_149;
}
else
{
obj* x_150; obj* x_151; 
if (lean::is_scalar(x_137)) {
 x_150 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_150 = x_137;
}
lean::cnstr_set(x_150, 0, x_138);
lean::cnstr_set(x_150, 1, x_134);
lean::cnstr_set(x_150, 2, x_135);
lean::cnstr_set(x_150, 3, x_136);
lean::cnstr_set_uint8(x_150, sizeof(void*)*4, x_141);
x_151 = l_RBNode_balLeft___rarg(x_129, x_130, x_131, x_150);
return x_151;
}
}
}
}
}
}
}
}
}
obj* l_RBNode_appendTrees___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_appendTrees___main___rarg), 2, 0);
return x_3;
}
}
obj* l_RBNode_appendTrees___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_appendTrees___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_appendTrees___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_appendTrees___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_RBNode_appendTrees(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_appendTrees___rarg), 2, 0);
return x_3;
}
}
obj* l_RBNode_appendTrees___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_appendTrees(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_del___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_7 = lean::cnstr_get(x_3, 2);
x_8 = lean::cnstr_get(x_3, 3);
lean::inc(x_1);
lean::inc(x_6);
lean::inc(x_2);
x_9 = lean::apply_2(x_1, x_2, x_6);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
lean::inc(x_1);
lean::inc(x_2);
lean::inc(x_6);
x_11 = lean::apply_2(x_1, x_6, x_2);
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
obj* x_13; 
lean::free_heap_obj(x_3);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_1);
x_13 = l_RBNode_appendTrees___main___rarg(x_5, x_8);
return x_13;
}
else
{
uint8 x_14; 
x_14 = l_RBNode_isBlack___rarg(x_8);
if (x_14 == 0)
{
obj* x_15; uint8 x_16; 
x_15 = l_RBNode_del___main___rarg(x_1, x_2, x_8);
x_16 = 0;
lean::cnstr_set(x_3, 3, x_15);
lean::cnstr_set_uint8(x_3, sizeof(void*)*4, x_16);
return x_3;
}
else
{
obj* x_17; obj* x_18; 
lean::free_heap_obj(x_3);
x_17 = l_RBNode_del___main___rarg(x_1, x_2, x_8);
x_18 = l_RBNode_balRight___rarg(x_5, x_6, x_7, x_17);
return x_18;
}
}
}
else
{
uint8 x_19; 
x_19 = l_RBNode_isBlack___rarg(x_5);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_RBNode_del___main___rarg(x_1, x_2, x_5);
x_21 = 0;
lean::cnstr_set(x_3, 0, x_20);
lean::cnstr_set_uint8(x_3, sizeof(void*)*4, x_21);
return x_3;
}
else
{
obj* x_22; obj* x_23; 
lean::free_heap_obj(x_3);
x_22 = l_RBNode_del___main___rarg(x_1, x_2, x_5);
x_23 = l_RBNode_balLeft___rarg(x_22, x_6, x_7, x_8);
return x_23;
}
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; uint8 x_29; 
x_24 = lean::cnstr_get(x_3, 0);
x_25 = lean::cnstr_get(x_3, 1);
x_26 = lean::cnstr_get(x_3, 2);
x_27 = lean::cnstr_get(x_3, 3);
lean::inc(x_27);
lean::inc(x_26);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_3);
lean::inc(x_1);
lean::inc(x_25);
lean::inc(x_2);
x_28 = lean::apply_2(x_1, x_2, x_25);
x_29 = lean::unbox(x_28);
lean::dec(x_28);
if (x_29 == 0)
{
obj* x_30; uint8 x_31; 
lean::inc(x_1);
lean::inc(x_2);
lean::inc(x_25);
x_30 = lean::apply_2(x_1, x_25, x_2);
x_31 = lean::unbox(x_30);
lean::dec(x_30);
if (x_31 == 0)
{
obj* x_32; 
lean::dec(x_26);
lean::dec(x_25);
lean::dec(x_2);
lean::dec(x_1);
x_32 = l_RBNode_appendTrees___main___rarg(x_24, x_27);
return x_32;
}
else
{
uint8 x_33; 
x_33 = l_RBNode_isBlack___rarg(x_27);
if (x_33 == 0)
{
obj* x_34; uint8 x_35; obj* x_36; 
x_34 = l_RBNode_del___main___rarg(x_1, x_2, x_27);
x_35 = 0;
x_36 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_36, 0, x_24);
lean::cnstr_set(x_36, 1, x_25);
lean::cnstr_set(x_36, 2, x_26);
lean::cnstr_set(x_36, 3, x_34);
lean::cnstr_set_uint8(x_36, sizeof(void*)*4, x_35);
return x_36;
}
else
{
obj* x_37; obj* x_38; 
x_37 = l_RBNode_del___main___rarg(x_1, x_2, x_27);
x_38 = l_RBNode_balRight___rarg(x_24, x_25, x_26, x_37);
return x_38;
}
}
}
else
{
uint8 x_39; 
x_39 = l_RBNode_isBlack___rarg(x_24);
if (x_39 == 0)
{
obj* x_40; uint8 x_41; obj* x_42; 
x_40 = l_RBNode_del___main___rarg(x_1, x_2, x_24);
x_41 = 0;
x_42 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_25);
lean::cnstr_set(x_42, 2, x_26);
lean::cnstr_set(x_42, 3, x_27);
lean::cnstr_set_uint8(x_42, sizeof(void*)*4, x_41);
return x_42;
}
else
{
obj* x_43; obj* x_44; 
x_43 = l_RBNode_del___main___rarg(x_1, x_2, x_24);
x_44 = l_RBNode_balLeft___rarg(x_43, x_25, x_26, x_27);
return x_44;
}
}
}
}
}
}
obj* l_RBNode_del___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_del___main___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_del___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_del___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_del___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_del___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBNode_del(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_del___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_del___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_del(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_erase___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_RBNode_del___main___rarg(x_1, x_2, x_3);
x_5 = l_RBNode_setBlack___rarg(x_4);
return x_5;
}
}
obj* l_RBNode_erase(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_erase___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_erase___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_erase(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_findCore___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_3);
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_2, 3);
lean::inc(x_8);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_6);
lean::inc(x_3);
x_9 = lean::apply_2(x_1, x_3, x_6);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
lean::dec(x_5);
lean::inc(x_1);
lean::inc(x_3);
lean::inc(x_6);
x_11 = lean::apply_2(x_1, x_6, x_3);
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_8);
lean::dec(x_3);
lean::dec(x_1);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_6);
lean::cnstr_set(x_13, 1, x_7);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
else
{
lean::dec(x_7);
lean::dec(x_6);
x_2 = x_8;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
x_2 = x_5;
goto _start;
}
}
}
}
obj* l_RBNode_findCore___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_findCore___main___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_findCore___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_findCore___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_findCore___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBNode_findCore(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_findCore___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_findCore___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_find___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; 
lean::dec(x_4);
lean::dec(x_1);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_3, 2);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_3, 3);
lean::inc(x_9);
lean::dec(x_3);
lean::inc(x_1);
lean::inc(x_7);
lean::inc(x_4);
x_10 = lean::apply_2(x_1, x_4, x_7);
x_11 = lean::unbox(x_10);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_12; uint8 x_13; 
lean::dec(x_6);
lean::inc(x_1);
lean::inc(x_4);
x_12 = lean::apply_2(x_1, x_7, x_4);
x_13 = lean::unbox(x_12);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_14; 
lean::dec(x_9);
lean::dec(x_4);
lean::dec(x_1);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_8);
return x_14;
}
else
{
lean::dec(x_8);
x_2 = lean::box(0);
x_3 = x_9;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_7);
x_2 = lean::box(0);
x_3 = x_6;
goto _start;
}
}
}
}
obj* l_RBNode_find___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_find___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBNode_find___main___rarg(x_1, lean::box(0), x_3, x_4);
return x_5;
}
}
obj* l_RBNode_find(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_lowerBound___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_2, 3);
lean::inc(x_8);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_6);
lean::inc(x_3);
x_9 = lean::apply_2(x_1, x_3, x_6);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::inc(x_1);
lean::inc(x_3);
lean::inc(x_6);
x_11 = lean::apply_2(x_1, x_6, x_3);
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_8);
lean::dec(x_3);
lean::dec(x_1);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_6);
lean::cnstr_set(x_13, 1, x_7);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
else
{
obj* x_15; obj* x_16; 
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_6);
lean::cnstr_set(x_15, 1, x_7);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_2 = x_8;
x_4 = x_16;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
x_2 = x_5;
goto _start;
}
}
}
}
obj* l_RBNode_lowerBound___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_lowerBound___main___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_lowerBound___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_lowerBound___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_lowerBound___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBNode_lowerBound___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_RBNode_lowerBound(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_lowerBound___rarg), 4, 0);
return x_3;
}
}
obj* l_RBNode_lowerBound___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_lowerBound(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_mkRBMap(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
}
obj* l_mkRBMap___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_mkRBMap(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_empty(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
}
obj* l_RBMap_empty___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_empty(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_HasEmptyc(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
}
obj* l_RBMap_HasEmptyc___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_HasEmptyc(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_depth___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_depth___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_RBMap_depth(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_depth___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_RBMap_depth___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_depth___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_depth___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_depth(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_fold___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_fold___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_fold(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_fold___rarg), 3, 0);
return x_5;
}
}
obj* l_RBMap_fold___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBMap_fold(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_RBMap_revFold___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_revFold___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_revFold(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_revFold___rarg), 3, 0);
return x_5;
}
}
obj* l_RBMap_revFold___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBMap_revFold(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_RBMap_mfold___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBNode_mfold___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_RBMap_mfold(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_mfold___rarg), 4, 0);
return x_6;
}
}
obj* l_RBMap_mfold___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_RBMap_mfold(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_8, 4);
lean::inc(x_9);
lean::inc(x_2);
x_10 = lean::apply_2(x_2, x_3, x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_11, lean::box(0), x_12);
x_14 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_10, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__1), 4, 3);
lean::closure_set(x_15, 0, x_1);
lean::closure_set(x_15, 1, x_2);
lean::closure_set(x_15, 2, x_5);
x_16 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_14, x_15);
return x_16;
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_4, 2);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_4, 3);
lean::inc(x_11);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::inc(x_2);
lean::inc(x_1);
x_13 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(x_1, x_2, x_3, x_8);
lean::inc(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2___boxed), 7, 6);
lean::closure_set(x_14, 0, x_1);
lean::closure_set(x_14, 1, x_2);
lean::closure_set(x_14, 2, x_9);
lean::closure_set(x_14, 3, x_10);
lean::closure_set(x_14, 4, x_11);
lean::closure_set(x_14, 5, x_12);
x_15 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg), 4, 0);
return x_5;
}
}
obj* l_RBMap_mfor___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
obj* l_RBMap_mfor(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_mfor___rarg), 3, 0);
return x_6;
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_7);
return x_8;
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_RBMap_mfor___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_RBMap_mfor(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
return x_6;
}
}
uint8 l_RBMap_isEmpty___rarg(obj* x_1) {
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
obj* l_RBMap_isEmpty(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_isEmpty___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_RBMap_isEmpty___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBMap_isEmpty___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBMap_isEmpty___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_isEmpty(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBNode_revFold___main___at_RBMap_toList___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_2, 2);
x_6 = lean::cnstr_get(x_2, 3);
x_7 = l_RBNode_revFold___main___at_RBMap_toList___spec__1___rarg(x_1, x_6);
lean::inc(x_5);
lean::inc(x_4);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_4);
lean::cnstr_set(x_8, 1, x_5);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_1 = x_9;
x_2 = x_3;
goto _start;
}
}
}
obj* l_RBNode_revFold___main___at_RBMap_toList___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_revFold___main___at_RBMap_toList___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBMap_toList___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_RBNode_revFold___main___at_RBMap_toList___spec__1___rarg(x_2, x_1);
return x_3;
}
}
obj* l_RBMap_toList(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_toList___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_RBNode_revFold___main___at_RBMap_toList___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_revFold___main___at_RBMap_toList___spec__1___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_toList___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_toList___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_toList___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_toList(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_min___rarg(obj* x_1) {
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
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
lean::dec(x_5);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
lean::cnstr_set(x_2, 0, x_8);
return x_2;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
}
}
obj* l_RBMap_min(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_min___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_RBMap_min___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_min___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_min___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_min(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_max___rarg(obj* x_1) {
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
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
lean::dec(x_5);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
lean::cnstr_set(x_2, 0, x_8);
return x_2;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
}
}
obj* l_RBMap_max(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_max___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_RBMap_max___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_max___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_max___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_max(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(obj* x_1, obj* x_2, uint8 x_3, obj* x_4) {
_start:
{
if (x_3 == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
lean::dec(x_2);
lean::dec(x_1);
x_5 = l_String_splitAux___main___closed__1;
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
lean::inc(x_2);
lean::inc(x_1);
x_8 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_1, x_2, x_3, x_7);
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
lean::dec(x_6);
x_11 = lean::apply_1(x_1, x_9);
x_12 = l_Prod_HasRepr___rarg___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean::dec(x_11);
x_14 = l_List_reprAux___main___rarg___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean::apply_1(x_2, x_10);
x_17 = lean_string_append(x_15, x_16);
lean::dec(x_16);
x_18 = l_Option_HasRepr___rarg___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_14, x_19);
lean::dec(x_19);
x_21 = lean_string_append(x_20, x_8);
lean::dec(x_8);
return x_21;
}
}
else
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_22; 
lean::dec(x_2);
lean::dec(x_1);
x_22 = l_String_splitAux___main___closed__1;
return x_22;
}
else
{
obj* x_23; obj* x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_23 = lean::cnstr_get(x_4, 0);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_4, 1);
lean::inc(x_24);
lean::dec(x_4);
x_25 = 0;
lean::inc(x_2);
lean::inc(x_1);
x_26 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_1, x_2, x_25, x_24);
x_27 = lean::cnstr_get(x_23, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_23, 1);
lean::inc(x_28);
lean::dec(x_23);
x_29 = lean::apply_1(x_1, x_27);
x_30 = l_Prod_HasRepr___rarg___closed__1;
x_31 = lean_string_append(x_30, x_29);
lean::dec(x_29);
x_32 = l_List_reprAux___main___rarg___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean::apply_1(x_2, x_28);
x_35 = lean_string_append(x_33, x_34);
lean::dec(x_34);
x_36 = l_Option_HasRepr___rarg___closed__3;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_26);
lean::dec(x_26);
return x_38;
}
}
}
}
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_List_repr___at_RBMap_HasRepr___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
lean::dec(x_2);
lean::dec(x_1);
x_4 = l_List_repr___rarg___closed__1;
return x_4;
}
else
{
uint8 x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = 1;
x_6 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_1, x_2, x_5, x_3);
x_7 = l_List_repr___rarg___closed__2;
x_8 = lean_string_append(x_7, x_6);
lean::dec(x_6);
x_9 = l_List_repr___rarg___closed__3;
x_10 = lean_string_append(x_8, x_9);
return x_10;
}
}
}
obj* l_List_repr___at_RBMap_HasRepr___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_repr___at_RBMap_HasRepr___spec__1___rarg), 3, 0);
return x_3;
}
}
obj* _init_l_RBMap_HasRepr___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("rbmapOf ");
return x_1;
}
}
obj* l_RBMap_HasRepr___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = l_RBMap_toList___rarg(x_3);
x_5 = l_List_repr___at_RBMap_HasRepr___spec__1___rarg(x_1, x_2, x_4);
x_6 = l_RBMap_HasRepr___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean::dec(x_5);
return x_7;
}
}
obj* l_RBMap_HasRepr(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_HasRepr___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_3);
lean::dec(x_3);
x_6 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
obj* l_RBMap_HasRepr___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_HasRepr___rarg(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_HasRepr___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_HasRepr(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_insert___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBNode_insert___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_RBMap_insert(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_insert___rarg), 4, 0);
return x_3;
}
}
obj* l_RBMap_erase___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_erase___rarg(x_1, x_3, x_2);
return x_4;
}
}
obj* l_RBMap_erase(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_erase___rarg), 3, 0);
return x_3;
}
}
obj* l_RBMap_ofList___main___rarg(obj* x_1, obj* x_2) {
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
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
lean::inc(x_1);
x_8 = l_RBMap_ofList___main___rarg(x_1, x_5);
x_9 = l_RBNode_insert___rarg(x_1, x_8, x_6, x_7);
return x_9;
}
}
}
obj* l_RBMap_ofList___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_ofList___main___rarg), 2, 0);
return x_3;
}
}
obj* l_RBMap_ofList___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_ofList___main___rarg(x_1, x_2);
return x_3;
}
}
obj* l_RBMap_ofList(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_ofList___rarg), 2, 0);
return x_3;
}
}
obj* l_RBMap_findCore___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_findCore___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_findCore(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_findCore___rarg), 3, 0);
return x_3;
}
}
obj* l_RBMap_find___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_find___main___rarg(x_1, lean::box(0), x_2, x_3);
return x_4;
}
}
obj* l_RBMap_find(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_find___rarg), 3, 0);
return x_3;
}
}
obj* l_RBMap_lowerBound___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_RBNode_lowerBound___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_RBMap_lowerBound(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_lowerBound___rarg), 3, 0);
return x_3;
}
}
uint8 l_RBMap_contains___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_find___main___rarg(x_1, lean::box(0), x_2, x_3);
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
obj* l_RBMap_contains(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_contains___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_RBMap_contains___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_RBMap_contains___rarg(x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_List_foldl___main___at_RBMap_fromList___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
lean::inc(x_1);
x_8 = l_RBNode_insert___rarg(x_1, x_2, x_6, x_7);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
obj* l_List_foldl___main___at_RBMap_fromList___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_RBMap_fromList___spec__1___rarg), 3, 0);
return x_3;
}
}
obj* l_RBMap_fromList___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_List_foldl___main___at_RBMap_fromList___spec__1___rarg(x_2, x_3, x_1);
return x_4;
}
}
obj* l_RBMap_fromList(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_fromList___rarg), 2, 0);
return x_3;
}
}
uint8 l_RBMap_all___rarg(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_all___main___rarg(x_2, x_1);
return x_3;
}
}
obj* l_RBMap_all(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_all___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_RBMap_all___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBMap_all___rarg(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBMap_all___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_all(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
uint8 l_RBMap_any___rarg(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_any___main___rarg(x_2, x_1);
return x_3;
}
}
obj* l_RBMap_any(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_any___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_RBMap_any___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBMap_any___rarg(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBMap_any___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_any(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_2, 0);
x_4 = lean::cnstr_get(x_2, 3);
x_5 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_1, x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean_nat_add(x_5, x_6);
lean::dec(x_5);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
obj* l_RBNode_fold___main___at_RBMap_size___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_fold___main___at_RBMap_size___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBMap_size___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_2, x_1);
return x_3;
}
}
obj* l_RBMap_size(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_size___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_size___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_size___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_size___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_size(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* _init_l_RBMap_maxDepth___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_max___boxed), 2, 0);
return x_1;
}
}
obj* l_RBMap_maxDepth___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_RBMap_maxDepth___rarg___closed__1;
x_3 = l_RBNode_depth___main___rarg(x_2, x_1);
return x_3;
}
}
obj* l_RBMap_maxDepth(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_maxDepth___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_RBMap_maxDepth___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_maxDepth___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_maxDepth___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_maxDepth(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_List_foldl___main___at_rbmapOf___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
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
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
lean::inc(x_1);
x_8 = l_RBNode_insert___rarg(x_1, x_2, x_6, x_7);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
obj* l_List_foldl___main___at_rbmapOf___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_rbmapOf___spec__1___rarg), 3, 0);
return x_3;
}
}
obj* l_rbmapOf___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_List_foldl___main___at_rbmapOf___spec__1___rarg(x_2, x_3, x_1);
return x_4;
}
}
obj* l_rbmapOf(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmapOf___rarg), 2, 0);
return x_3;
}
}
obj* initialize_init_data_repr(obj*);
obj* initialize_init_data_option_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_rbmap_basic(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_repr(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (lean::io_result_is_error(w)) return w;
l_RBMap_HasRepr___rarg___closed__1 = _init_l_RBMap_HasRepr___rarg___closed__1();
lean::mark_persistent(l_RBMap_HasRepr___rarg___closed__1);
l_RBMap_maxDepth___rarg___closed__1 = _init_l_RBMap_maxDepth___rarg___closed__1();
lean::mark_persistent(l_RBMap_maxDepth___rarg___closed__1);
return w;
}
}
