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
obj* l_RBNode_depth___rarg(obj*, obj*);
obj* l_RBNode_min___boxed(obj*, obj*);
obj* l_RBNode_max___main___boxed(obj*, obj*);
obj* l_RBNode_balance1(obj*, obj*);
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_RBNode_find(obj*);
obj* l_RBNode_depth___main___rarg___boxed(obj*, obj*);
obj* l_List_repr___main___at_RBMap_HasRepr___spec__1___boxed(obj*, obj*);
obj* l_RBNode_ins___main___boxed(obj*, obj*);
obj* l_RBMap_fold___main___rarg(obj*, obj*, obj*);
obj* l_RBMap_contains(obj*, obj*);
obj* l_RBNode_findCore(obj*, obj*);
obj* l_RBMap_revFold___rarg(obj*, obj*, obj*);
obj* l_RBNode_lowerBound(obj*, obj*);
obj* l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___rarg(obj*, obj*);
obj* l_RBNode_revFold___rarg(obj*, obj*, obj*);
obj* l_RBNode_findCore___main___rarg(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_findCore___main___boxed(obj*, obj*);
obj* l_RBMap_find___rarg(obj*, obj*, obj*);
obj* l_RBNode_insert___boxed(obj*, obj*);
obj* l_RBMap_any___main(obj*, obj*, obj*);
obj* l_RBMap_contains___boxed(obj*, obj*);
obj* l_RBMap_any___main___rarg___boxed(obj*, obj*);
obj* l_RBNode_setBlack(obj*, obj*);
obj* l_List_foldl___main___at_rbmapOf___spec__1(obj*, obj*);
obj* l_RBNode_isRed___boxed(obj*, obj*);
obj* l_RBNode_ins___main(obj*, obj*);
obj* l_RBNode_balance2___main___boxed(obj*, obj*);
obj* l_RBMap_ofList(obj*, obj*);
obj* l_RBMap_insert___boxed(obj*, obj*);
obj* l_RBNode_find___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_toList___main___boxed(obj*, obj*, obj*);
obj* l_RBMap_min(obj*, obj*, obj*);
obj* l_RBMap_toList___rarg(obj*);
obj* l_RBMap_depth___rarg___boxed(obj*, obj*);
obj* l_RBNode_isRed___rarg___boxed(obj*);
uint8 l_RBNode_all___rarg(obj*, obj*);
obj* l_RBNode_balance2(obj*, obj*);
obj* l_RBMap_findCore___rarg(obj*, obj*, obj*);
obj* l_RBNode_lowerBound___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_all___main(obj*, obj*, obj*);
obj* l_RBMap_min___main___rarg(obj*);
obj* l_RBMap_min___rarg(obj*);
uint8 l_RBNode_any___main___rarg(obj*, obj*);
obj* l_RBMap_findCore(obj*, obj*);
obj* l_RBNode_isRed___main___rarg___boxed(obj*);
obj* l_RBNode_lowerBound___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmapOf___rarg(obj*, obj*);
obj* l_RBNode_any___main(obj*, obj*);
obj* l_RBNode_mfold___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_revFold___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_findCore___main___boxed(obj*, obj*);
obj* l_List_foldl___main___at_rbmapOf___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbmapOf(obj*, obj*);
obj* l_RBNode_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_toList___boxed(obj*, obj*, obj*);
obj* l_RBNode_min___main___rarg(obj*);
obj* l_RBMap_mfold(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___boxed(obj*, obj*);
obj* l_RBMap_mfor(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_lowerBound___main(obj*, obj*);
obj* l_RBNode_max___main___rarg(obj*);
obj* l_RBMap_lowerBound___main(obj*, obj*);
obj* l_RBMap_mfold___main(obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_all___boxed(obj*, obj*, obj*);
obj* l_RBNode_any(obj*, obj*);
obj* l_RBMap_depth(obj*, obj*, obj*);
obj* l_RBNode_max(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1(obj*, obj*, obj*, obj*);
obj* l_RBMap_empty___boxed(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_isRed(obj*, obj*);
obj* l_RBMap_toList___main(obj*, obj*, obj*);
uint8 l_RBMap_any___main___rarg(obj*, obj*);
obj* l_RBNode_fold___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_min___rarg(obj*);
obj* l_RBMap_findCore___main___rarg(obj*, obj*, obj*);
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(obj*, obj*, uint8, obj*);
obj* l_RBMap_fold___main(obj*, obj*, obj*, obj*);
obj* l_RBMap_fold___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_depth___boxed(obj*, obj*, obj*);
obj* l_RBNode_depth___main___rarg(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___boxed(obj*, obj*);
obj* l_RBMap_lowerBound(obj*, obj*);
obj* l_RBNode_lowerBound___main___boxed(obj*, obj*);
obj* l_RBMap_isEmpty(obj*, obj*, obj*);
obj* l_RBNode_setBlack___boxed(obj*, obj*);
obj* l_RBNode_balance2___main___rarg(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_RBMap_fromList___spec__1___boxed(obj*, obj*);
obj* l_RBMap_mfor___rarg(obj*, obj*, obj*);
obj* l_mkRBMap___boxed(obj*, obj*, obj*);
obj* l_RBMap_isEmpty___main___boxed(obj*, obj*, obj*);
obj* l_RBMap_toList___main___rarg(obj*);
obj* l_RBMap_ofList___main___rarg(obj*, obj*);
obj* l_RBNode_balance2___main(obj*, obj*);
obj* l_RBNode_all___main___rarg___boxed(obj*, obj*);
obj* l_RBMap_revFold___main___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_List_repr___main___rarg___closed__3;
obj* l_RBNode_singleton(obj*, obj*);
obj* l_RBMap_ofList___rarg(obj*, obj*);
obj* l_RBNode_find___main___boxed(obj*);
obj* l_RBMap_fold___main___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_findCore___boxed(obj*, obj*);
obj* l_RBNode_balance2___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_lowerBound___boxed(obj*, obj*);
obj* l_RBNode_find___boxed(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_RBMap_revFold___main___rarg(obj*, obj*, obj*);
obj* l_RBMap_contains___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_fold___rarg(obj*, obj*, obj*);
extern obj* l_List_reprAux___main___rarg___closed__1;
obj* l_RBMap_findCore___boxed(obj*, obj*);
obj* l_RBNode_insert(obj*, obj*);
uint8 l_RBNode_isRed___rarg(obj*);
obj* l_RBMap_HasRepr(obj*, obj*, obj*);
obj* l_RBMap_min___boxed(obj*, obj*, obj*);
extern obj* l_Option_HasRepr___rarg___closed__3;
obj* l_RBMap_fold___rarg(obj*, obj*, obj*);
obj* l_RBMap_ofList___boxed(obj*, obj*);
obj* l_RBMap_min___main(obj*, obj*, obj*);
obj* l_RBMap_mfor___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_ofList___main___boxed(obj*, obj*);
obj* l_RBMap_HasRepr___rarg___closed__1;
obj* l_RBMap_max(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_all___boxed(obj*, obj*);
obj* l_RBNode_find___main(obj*);
obj* l_RBMap_insert___main___boxed(obj*, obj*);
obj* l_RBNode_singleton___rarg(obj*, obj*);
obj* l_RBNode_revFold___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_max___boxed(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_RBMap_HasEmptyc___boxed(obj*, obj*, obj*);
obj* l_RBNode_isRed___main___boxed(obj*, obj*);
obj* l_RBMap_HasRepr___rarg(obj*, obj*, obj*);
obj* l_RBNode_setBlack___main___boxed(obj*, obj*);
extern obj* l_Prod_HasRepr___rarg___closed__1;
obj* l_RBMap_find(obj*, obj*);
obj* l_RBMap_max___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_fold___main___rarg(obj*, obj*, obj*);
obj* l_RBNode_isRed___main(obj*, obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_RBMap_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins(obj*, obj*);
obj* l_RBMap_depth___rarg(obj*, obj*);
uint8 l_RBNode_all___main___rarg(obj*, obj*);
uint8 l_RBNode_any___rarg(obj*, obj*);
obj* l_RBMap_toList(obj*, obj*, obj*);
obj* l_RBMap_mfold___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___boxed(obj*, obj*);
obj* l_RBNode_all(obj*, obj*);
obj* l_RBNode_mfold___main(obj*, obj*, obj*, obj*);
obj* l_RBMap_findCore___main(obj*, obj*);
obj* l_RBMap_any___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_any___main___rarg___boxed(obj*, obj*);
obj* l_RBMap_max___main(obj*, obj*, obj*);
obj* l_RBNode_all___main(obj*, obj*);
obj* l_RBMap_empty(obj*, obj*, obj*);
uint8 l_RBMap_isEmpty___main___rarg(obj*);
obj* l_RBNode_max___rarg(obj*);
obj* l_RBMap_all___main___boxed(obj*, obj*, obj*);
obj* l_List_repr___main___at_RBMap_HasRepr___spec__1(obj*, obj*);
obj* l_RBNode_depth___rarg___boxed(obj*, obj*);
obj* l_RBNode_balance2___boxed(obj*, obj*);
obj* l_RBNode_all___rarg___boxed(obj*, obj*);
obj* l_rbmapOf___boxed(obj*, obj*);
obj* l_RBNode_depth___main(obj*, obj*);
obj* l_RBNode_mfold___main___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_isEmpty___main(obj*, obj*, obj*);
obj* l_RBNode_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main(obj*, obj*);
obj* l_RBMap_lowerBound___main___boxed(obj*, obj*);
obj* l_RBNode_min(obj*, obj*);
obj* l_RBNode_min___main(obj*, obj*);
obj* l_RBMap_mfold___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_any___main___boxed(obj*, obj*);
obj* l_RBMap_fold(obj*, obj*, obj*, obj*);
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_singleton___boxed(obj*, obj*);
obj* l_RBNode_balance1___main(obj*, obj*);
obj* l_RBNode_any___boxed(obj*, obj*);
obj* l_RBNode_setBlack___main(obj*, obj*);
obj* l_RBMap_find___boxed(obj*, obj*);
extern obj* l_List_repr___main___rarg___closed__1;
obj* l_RBMap_any___boxed(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_RBMap_fromList___boxed(obj*, obj*);
uint8 l_RBMap_all___rarg(obj*, obj*);
obj* l_RBMap_any___rarg___boxed(obj*, obj*);
obj* l_RBMap_find___main___boxed(obj*, obj*);
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2(obj*, obj*);
obj* l_RBMap_insert(obj*, obj*);
obj* l_RBMap_revFold(obj*, obj*, obj*, obj*);
obj* l_RBNode_revFold___main(obj*, obj*, obj*);
obj* l_RBNode_revFold___main___at_RBMap_toList___main___spec__1(obj*, obj*);
obj* l_List_foldl___main___at_RBMap_fromList___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_lowerBound___main___rarg(obj*, obj*, obj*);
obj* l_RBMap_isEmpty___boxed(obj*, obj*, obj*);
uint8 l_RBMap_all___main___rarg(obj*, obj*);
obj* l_RBNode_balance1___boxed(obj*, obj*);
obj* l_RBNode_depth___main___boxed(obj*, obj*);
obj* l_RBMap_revFold___main(obj*, obj*, obj*, obj*);
obj* l_RBMap_all___main___rarg___boxed(obj*, obj*);
obj* l_RBNode_find___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_fromList(obj*, obj*);
obj* l_RBNode_any___rarg___boxed(obj*, obj*);
obj* l_RBNode_max___main(obj*, obj*);
obj* l_RBNode_setBlack___rarg(obj*);
obj* l_RBMap_lowerBound___rarg(obj*, obj*, obj*);
obj* l_RBMap_HasEmptyc(obj*, obj*, obj*);
obj* l_RBNode_min___main___boxed(obj*, obj*);
obj* l_RBNode_depth___boxed(obj*, obj*);
obj* l_RBMap_find___main___rarg(obj*, obj*, obj*);
obj* l_RBNode_balance1___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_isEmpty___rarg___boxed(obj*);
obj* l_RBNode_revFold___main___rarg(obj*, obj*, obj*);
obj* l_mkRBMap(obj*, obj*, obj*);
obj* l_RBNode_balance1___main___boxed(obj*, obj*);
obj* l_RBMap_all(obj*, obj*, obj*);
obj* l_RBMap_ofList___main(obj*, obj*);
obj* l_RBNode_findCore___main(obj*, obj*);
obj* l_RBNode_lowerBound___boxed(obj*, obj*);
obj* l_RBMap_fromList___rarg(obj*, obj*);
obj* l_RBNode_ins___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_all___rarg___boxed(obj*, obj*);
obj* l_RBNode_fold___boxed(obj*, obj*, obj*);
obj* l_RBNode_fold___main(obj*, obj*, obj*);
obj* l_List_foldl___main___at_rbmapOf___spec__1___boxed(obj*, obj*);
obj* l_RBNode_fold(obj*, obj*, obj*);
obj* l_RBNode_depth(obj*, obj*);
obj* l_RBMap_min___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_all___main___boxed(obj*, obj*);
obj* l_RBNode_mfold(obj*, obj*, obj*, obj*);
obj* l_RBMap_isEmpty___main___rarg___boxed(obj*);
obj* l_RBNode_balance1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_find___main(obj*, obj*);
extern obj* l_List_repr___main___rarg___closed__2;
obj* l_RBNode_find___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main___rarg(obj*, obj*, obj*, obj*);
uint8 l_RBMap_any___rarg(obj*, obj*);
obj* l_RBMap_any(obj*, obj*, obj*);
obj* l_RBMap_HasRepr___boxed(obj*, obj*, obj*);
obj* l_RBNode_findCore___rarg(obj*, obj*, obj*);
obj* l_RBMap_max___rarg(obj*);
obj* l_RBMap_max___main___rarg(obj*);
uint8 l_RBMap_isEmpty___rarg(obj*);
obj* l_List_foldl___main___at_RBMap_fromList___spec__1(obj*, obj*);
obj* l_List_repr___main___at_RBMap_HasRepr___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_RBNode_revFold(obj*, obj*, obj*);
uint8 l_RBMap_contains___rarg(obj*, obj*, obj*);
obj* l_RBNode_revFold___boxed(obj*, obj*, obj*);
obj* l_RBMap_mfold___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_RBMap_max___boxed(obj*, obj*, obj*);
obj* l_RBNode_depth___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_0);
x_3 = lean::mk_nat_obj(0ul);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 3);
lean::inc(x_0);
x_7 = l_RBNode_depth___main___rarg(x_0, x_4);
lean::inc(x_0);
x_9 = l_RBNode_depth___main___rarg(x_0, x_5);
x_10 = lean::apply_2(x_0, x_7, x_9);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_10, x_11);
lean::dec(x_10);
return x_12;
}
}
}
obj* l_RBNode_depth___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_depth___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_depth___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_depth___main___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_depth___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_depth___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_depth___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_depth___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBNode_depth(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_depth___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_depth___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_depth___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_depth___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_depth(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_min___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
else
{
lean::dec(x_0);
x_0 = x_2;
goto _start;
}
}
}
}
obj* l_RBNode_min___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_min___main___rarg), 1, 0);
return x_2;
}
}
obj* l_RBNode_min___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_min___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_min___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_min___main___rarg(x_0);
return x_1;
}
}
obj* l_RBNode_min(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_min___rarg), 1, 0);
return x_2;
}
}
obj* l_RBNode_min___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_min(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_max___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 3);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
else
{
lean::dec(x_0);
x_0 = x_2;
goto _start;
}
}
}
}
obj* l_RBNode_max___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_max___main___rarg), 1, 0);
return x_2;
}
}
obj* l_RBNode_max___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_max___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_max___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_max___main___rarg(x_0);
return x_1;
}
}
obj* l_RBNode_max(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_max___rarg), 1, 0);
return x_2;
}
}
obj* l_RBNode_max___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_max(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_14; obj* x_16; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 3);
lean::inc(x_10);
lean::dec(x_2);
lean::inc(x_0);
x_14 = l_RBNode_fold___main___rarg(x_0, x_1, x_4);
lean::inc(x_0);
x_16 = lean::apply_3(x_0, x_14, x_6, x_8);
x_1 = x_16;
x_2 = x_10;
goto _start;
}
}
}
obj* l_RBNode_fold___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_fold___main___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_fold___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_fold___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBNode_fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_fold___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_fold___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_fold(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_mfold___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main___rarg(x_0, x_1, x_3, x_2);
return x_4;
}
}
obj* l_RBNode_mfold___main___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_0);
x_8 = lean::apply_3(x_0, x_6, x_1, x_2);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___rarg___lambda__1), 4, 3);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_0);
lean::closure_set(x_9, 2, x_4);
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_RBNode_mfold___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_25; obj* x_27; obj* x_28; 
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_3, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_3, 2);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_3, 3);
lean::inc(x_18);
lean::dec(x_3);
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::inc(x_1);
lean::inc(x_0);
x_25 = l_RBNode_mfold___main___rarg(x_0, x_1, x_2, x_12);
lean::inc(x_21);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___rarg___lambda__2), 7, 6);
lean::closure_set(x_27, 0, x_1);
lean::closure_set(x_27, 1, x_14);
lean::closure_set(x_27, 2, x_16);
lean::closure_set(x_27, 3, x_0);
lean::closure_set(x_27, 4, x_18);
lean::closure_set(x_27, 5, x_21);
x_28 = lean::apply_4(x_21, lean::box(0), lean::box(0), x_25, x_27);
return x_28;
}
}
}
obj* l_RBNode_mfold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___rarg), 4, 0);
return x_4;
}
}
obj* l_RBNode_mfold___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBNode_mfold___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBNode_mfold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___rarg), 4, 0);
return x_4;
}
}
obj* l_RBNode_mfold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBNode_revFold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_14; obj* x_16; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 3);
lean::inc(x_10);
lean::dec(x_2);
lean::inc(x_0);
x_14 = l_RBNode_revFold___main___rarg(x_0, x_1, x_10);
lean::inc(x_0);
x_16 = lean::apply_3(x_0, x_14, x_6, x_8);
x_1 = x_16;
x_2 = x_4;
goto _start;
}
}
}
obj* l_RBNode_revFold___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_revFold___main___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_revFold___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_revFold___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_revFold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_revFold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBNode_revFold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_revFold___rarg), 3, 0);
return x_3;
}
}
obj* l_RBNode_revFold___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_revFold(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBNode_all___main___rarg(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_14; uint8 x_15; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_6, x_8);
x_15 = lean::unbox(x_14);
if (x_15 == 0)
{
uint8 x_19; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_4);
x_19 = 0;
return x_19;
}
else
{
uint8 x_21; 
lean::inc(x_0);
x_21 = l_RBNode_all___main___rarg(x_0, x_4);
if (x_21 == 0)
{
uint8 x_24; 
lean::dec(x_10);
lean::dec(x_0);
x_24 = 0;
return x_24;
}
else
{
x_1 = x_10;
goto _start;
}
}
}
}
}
obj* l_RBNode_all___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_all___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_all___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBNode_all___main___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBNode_all___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_all___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBNode_all___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_RBNode_all___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBNode_all(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_all___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_all___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBNode_all___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBNode_all___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_all(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBNode_any___main___rarg(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_14; uint8 x_15; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_6, x_8);
x_15 = lean::unbox(x_14);
if (x_15 == 0)
{
uint8 x_17; 
lean::inc(x_0);
x_17 = l_RBNode_any___main___rarg(x_0, x_4);
if (x_17 == 0)
{
x_1 = x_10;
goto _start;
}
else
{
uint8 x_21; 
lean::dec(x_10);
lean::dec(x_0);
x_21 = 1;
return x_21;
}
}
else
{
uint8 x_25; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_4);
x_25 = 1;
return x_25;
}
}
}
}
obj* l_RBNode_any___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_any___main___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_any___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBNode_any___main___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBNode_any___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_any___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBNode_any___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_RBNode_any___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBNode_any(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_any___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_any___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBNode_any___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBNode_any___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_any(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_singleton___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; obj* x_4; obj* x_5; 
x_2 = lean::box(0);
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_0);
lean::cnstr_set(x_4, 2, x_1);
lean::cnstr_set(x_4, 3, x_2);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
}
obj* l_RBNode_singleton(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_singleton___rarg), 2, 0);
return x_2;
}
}
obj* l_RBNode_singleton___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_singleton(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_balance1___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_3, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; 
x_11 = lean::cnstr_get(x_3, 1);
x_13 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_15 = x_3;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_3);
 x_15 = lean::box(0);
}
x_16 = 0;
if (lean::is_scalar(x_15)) {
 x_17 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_17 = x_15;
}
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_11);
lean::cnstr_set(x_17, 2, x_13);
lean::cnstr_set(x_17, 3, x_9);
lean::cnstr_set_scalar(x_17, sizeof(void*)*4, x_16);
x_18 = x_17;
x_19 = 1;
x_20 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_0);
lean::cnstr_set(x_20, 2, x_1);
lean::cnstr_set(x_20, 3, x_2);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_19);
x_21 = x_20;
return x_21;
}
else
{
uint8 x_22; 
x_22 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*4);
if (x_22 == 0)
{
obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_23 = lean::cnstr_get(x_3, 1);
x_25 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_27 = x_3;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_3);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_9, 0);
x_30 = lean::cnstr_get(x_9, 1);
x_32 = lean::cnstr_get(x_9, 2);
x_34 = lean::cnstr_get(x_9, 3);
if (lean::is_exclusive(x_9)) {
 x_36 = x_9;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_9);
 x_36 = lean::box(0);
}
x_37 = 1;
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_7);
lean::cnstr_set(x_38, 1, x_23);
lean::cnstr_set(x_38, 2, x_25);
lean::cnstr_set(x_38, 3, x_28);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_37);
x_39 = x_38;
if (lean::is_scalar(x_27)) {
 x_40 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_40 = x_27;
}
lean::cnstr_set(x_40, 0, x_34);
lean::cnstr_set(x_40, 1, x_0);
lean::cnstr_set(x_40, 2, x_1);
lean::cnstr_set(x_40, 3, x_2);
lean::cnstr_set_scalar(x_40, sizeof(void*)*4, x_37);
x_41 = x_40;
x_42 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_42, 0, x_39);
lean::cnstr_set(x_42, 1, x_30);
lean::cnstr_set(x_42, 2, x_32);
lean::cnstr_set(x_42, 3, x_41);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_22);
x_43 = x_42;
return x_43;
}
else
{
obj* x_44; obj* x_46; obj* x_48; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_44 = lean::cnstr_get(x_3, 1);
x_46 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_48 = x_3;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_3);
 x_48 = lean::box(0);
}
x_49 = 0;
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_7);
lean::cnstr_set(x_50, 1, x_44);
lean::cnstr_set(x_50, 2, x_46);
lean::cnstr_set(x_50, 3, x_9);
lean::cnstr_set_scalar(x_50, sizeof(void*)*4, x_49);
x_51 = x_50;
x_52 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_0);
lean::cnstr_set(x_52, 2, x_1);
lean::cnstr_set(x_52, 3, x_2);
lean::cnstr_set_scalar(x_52, sizeof(void*)*4, x_22);
x_53 = x_52;
return x_53;
}
}
}
else
{
uint8 x_54; 
x_54 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*4);
if (x_54 == 0)
{
obj* x_55; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_70; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_55 = lean::cnstr_get(x_3, 1);
x_57 = lean::cnstr_get(x_3, 2);
x_59 = lean::cnstr_get(x_3, 3);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_61 = x_3;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_3);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_7, 0);
x_64 = lean::cnstr_get(x_7, 1);
x_66 = lean::cnstr_get(x_7, 2);
x_68 = lean::cnstr_get(x_7, 3);
if (lean::is_exclusive(x_7)) {
 x_70 = x_7;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::inc(x_66);
 lean::inc(x_68);
 lean::dec(x_7);
 x_70 = lean::box(0);
}
x_71 = 1;
if (lean::is_scalar(x_70)) {
 x_72 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_72 = x_70;
}
lean::cnstr_set(x_72, 0, x_62);
lean::cnstr_set(x_72, 1, x_64);
lean::cnstr_set(x_72, 2, x_66);
lean::cnstr_set(x_72, 3, x_68);
lean::cnstr_set_scalar(x_72, sizeof(void*)*4, x_71);
x_73 = x_72;
if (lean::is_scalar(x_61)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_61;
}
lean::cnstr_set(x_74, 0, x_59);
lean::cnstr_set(x_74, 1, x_0);
lean::cnstr_set(x_74, 2, x_1);
lean::cnstr_set(x_74, 3, x_2);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_71);
x_75 = x_74;
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set(x_76, 1, x_55);
lean::cnstr_set(x_76, 2, x_57);
lean::cnstr_set(x_76, 3, x_75);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_54);
x_77 = x_76;
return x_77;
}
else
{
obj* x_78; 
x_78 = lean::cnstr_get(x_3, 3);
lean::inc(x_78);
if (lean::obj_tag(x_78) == 0)
{
obj* x_80; obj* x_82; obj* x_84; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_80 = lean::cnstr_get(x_3, 1);
x_82 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_84 = x_3;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_3);
 x_84 = lean::box(0);
}
x_85 = 0;
if (lean::is_scalar(x_84)) {
 x_86 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_86 = x_84;
}
lean::cnstr_set(x_86, 0, x_7);
lean::cnstr_set(x_86, 1, x_80);
lean::cnstr_set(x_86, 2, x_82);
lean::cnstr_set(x_86, 3, x_78);
lean::cnstr_set_scalar(x_86, sizeof(void*)*4, x_85);
x_87 = x_86;
x_88 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_0);
lean::cnstr_set(x_88, 2, x_1);
lean::cnstr_set(x_88, 3, x_2);
lean::cnstr_set_scalar(x_88, sizeof(void*)*4, x_54);
x_89 = x_88;
return x_89;
}
else
{
uint8 x_90; 
x_90 = lean::cnstr_get_scalar<uint8>(x_78, sizeof(void*)*4);
if (x_90 == 0)
{
obj* x_91; obj* x_93; obj* x_95; obj* x_96; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_91 = lean::cnstr_get(x_3, 1);
x_93 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_95 = x_3;
} else {
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_3);
 x_95 = lean::box(0);
}
x_96 = lean::cnstr_get(x_78, 0);
x_98 = lean::cnstr_get(x_78, 1);
x_100 = lean::cnstr_get(x_78, 2);
x_102 = lean::cnstr_get(x_78, 3);
if (lean::is_exclusive(x_78)) {
 x_104 = x_78;
} else {
 lean::inc(x_96);
 lean::inc(x_98);
 lean::inc(x_100);
 lean::inc(x_102);
 lean::dec(x_78);
 x_104 = lean::box(0);
}
lean::inc(x_7);
if (lean::is_scalar(x_104)) {
 x_106 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_106 = x_104;
}
lean::cnstr_set(x_106, 0, x_7);
lean::cnstr_set(x_106, 1, x_91);
lean::cnstr_set(x_106, 2, x_93);
lean::cnstr_set(x_106, 3, x_96);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 lean::cnstr_release(x_7, 3);
 x_107 = x_7;
} else {
 lean::dec(x_7);
 x_107 = lean::box(0);
}
lean::cnstr_set_scalar(x_106, sizeof(void*)*4, x_54);
x_108 = x_106;
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_102);
lean::cnstr_set(x_109, 1, x_0);
lean::cnstr_set(x_109, 2, x_1);
lean::cnstr_set(x_109, 3, x_2);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_54);
x_110 = x_109;
if (lean::is_scalar(x_95)) {
 x_111 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_111 = x_95;
}
lean::cnstr_set(x_111, 0, x_108);
lean::cnstr_set(x_111, 1, x_98);
lean::cnstr_set(x_111, 2, x_100);
lean::cnstr_set(x_111, 3, x_110);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_90);
x_112 = x_111;
return x_112;
}
else
{
obj* x_113; obj* x_115; obj* x_117; obj* x_118; obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_127; obj* x_128; uint8 x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_113 = lean::cnstr_get(x_3, 1);
x_115 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_117 = x_3;
} else {
 lean::inc(x_113);
 lean::inc(x_115);
 lean::dec(x_3);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_7, 0);
x_120 = lean::cnstr_get(x_7, 1);
x_122 = lean::cnstr_get(x_7, 2);
x_124 = lean::cnstr_get(x_7, 3);
if (lean::is_exclusive(x_7)) {
 x_126 = x_7;
} else {
 lean::inc(x_118);
 lean::inc(x_120);
 lean::inc(x_122);
 lean::inc(x_124);
 lean::dec(x_7);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_118);
lean::cnstr_set(x_127, 1, x_120);
lean::cnstr_set(x_127, 2, x_122);
lean::cnstr_set(x_127, 3, x_124);
lean::cnstr_set_scalar(x_127, sizeof(void*)*4, x_90);
x_128 = x_127;
x_129 = 0;
if (lean::is_scalar(x_117)) {
 x_130 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_130 = x_117;
}
lean::cnstr_set(x_130, 0, x_128);
lean::cnstr_set(x_130, 1, x_113);
lean::cnstr_set(x_130, 2, x_115);
lean::cnstr_set(x_130, 3, x_78);
lean::cnstr_set_scalar(x_130, sizeof(void*)*4, x_129);
x_131 = x_130;
x_132 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_0);
lean::cnstr_set(x_132, 2, x_1);
lean::cnstr_set(x_132, 3, x_2);
lean::cnstr_set_scalar(x_132, sizeof(void*)*4, x_90);
x_133 = x_132;
return x_133;
}
}
}
}
}
}
}
obj* l_RBNode_balance1___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balance1___main___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_balance1___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_balance1___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_balance1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_3, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; 
x_11 = lean::cnstr_get(x_3, 1);
x_13 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_15 = x_3;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_3);
 x_15 = lean::box(0);
}
x_16 = 0;
if (lean::is_scalar(x_15)) {
 x_17 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_17 = x_15;
}
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_11);
lean::cnstr_set(x_17, 2, x_13);
lean::cnstr_set(x_17, 3, x_9);
lean::cnstr_set_scalar(x_17, sizeof(void*)*4, x_16);
x_18 = x_17;
x_19 = 1;
x_20 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_0);
lean::cnstr_set(x_20, 2, x_1);
lean::cnstr_set(x_20, 3, x_2);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_19);
x_21 = x_20;
return x_21;
}
else
{
uint8 x_22; 
x_22 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*4);
if (x_22 == 0)
{
obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_23 = lean::cnstr_get(x_3, 1);
x_25 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_27 = x_3;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_3);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_9, 0);
x_30 = lean::cnstr_get(x_9, 1);
x_32 = lean::cnstr_get(x_9, 2);
x_34 = lean::cnstr_get(x_9, 3);
if (lean::is_exclusive(x_9)) {
 x_36 = x_9;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_9);
 x_36 = lean::box(0);
}
x_37 = 1;
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_7);
lean::cnstr_set(x_38, 1, x_23);
lean::cnstr_set(x_38, 2, x_25);
lean::cnstr_set(x_38, 3, x_28);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_37);
x_39 = x_38;
if (lean::is_scalar(x_27)) {
 x_40 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_40 = x_27;
}
lean::cnstr_set(x_40, 0, x_34);
lean::cnstr_set(x_40, 1, x_0);
lean::cnstr_set(x_40, 2, x_1);
lean::cnstr_set(x_40, 3, x_2);
lean::cnstr_set_scalar(x_40, sizeof(void*)*4, x_37);
x_41 = x_40;
x_42 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_42, 0, x_39);
lean::cnstr_set(x_42, 1, x_30);
lean::cnstr_set(x_42, 2, x_32);
lean::cnstr_set(x_42, 3, x_41);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_22);
x_43 = x_42;
return x_43;
}
else
{
obj* x_44; obj* x_46; obj* x_48; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_44 = lean::cnstr_get(x_3, 1);
x_46 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_48 = x_3;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_3);
 x_48 = lean::box(0);
}
x_49 = 0;
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_7);
lean::cnstr_set(x_50, 1, x_44);
lean::cnstr_set(x_50, 2, x_46);
lean::cnstr_set(x_50, 3, x_9);
lean::cnstr_set_scalar(x_50, sizeof(void*)*4, x_49);
x_51 = x_50;
x_52 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_0);
lean::cnstr_set(x_52, 2, x_1);
lean::cnstr_set(x_52, 3, x_2);
lean::cnstr_set_scalar(x_52, sizeof(void*)*4, x_22);
x_53 = x_52;
return x_53;
}
}
}
else
{
uint8 x_54; 
x_54 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*4);
if (x_54 == 0)
{
obj* x_55; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_70; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_55 = lean::cnstr_get(x_3, 1);
x_57 = lean::cnstr_get(x_3, 2);
x_59 = lean::cnstr_get(x_3, 3);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_61 = x_3;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_3);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_7, 0);
x_64 = lean::cnstr_get(x_7, 1);
x_66 = lean::cnstr_get(x_7, 2);
x_68 = lean::cnstr_get(x_7, 3);
if (lean::is_exclusive(x_7)) {
 x_70 = x_7;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::inc(x_66);
 lean::inc(x_68);
 lean::dec(x_7);
 x_70 = lean::box(0);
}
x_71 = 1;
if (lean::is_scalar(x_70)) {
 x_72 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_72 = x_70;
}
lean::cnstr_set(x_72, 0, x_62);
lean::cnstr_set(x_72, 1, x_64);
lean::cnstr_set(x_72, 2, x_66);
lean::cnstr_set(x_72, 3, x_68);
lean::cnstr_set_scalar(x_72, sizeof(void*)*4, x_71);
x_73 = x_72;
if (lean::is_scalar(x_61)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_61;
}
lean::cnstr_set(x_74, 0, x_59);
lean::cnstr_set(x_74, 1, x_0);
lean::cnstr_set(x_74, 2, x_1);
lean::cnstr_set(x_74, 3, x_2);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_71);
x_75 = x_74;
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set(x_76, 1, x_55);
lean::cnstr_set(x_76, 2, x_57);
lean::cnstr_set(x_76, 3, x_75);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_54);
x_77 = x_76;
return x_77;
}
else
{
obj* x_78; 
x_78 = lean::cnstr_get(x_3, 3);
lean::inc(x_78);
if (lean::obj_tag(x_78) == 0)
{
obj* x_80; obj* x_82; obj* x_84; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_80 = lean::cnstr_get(x_3, 1);
x_82 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_84 = x_3;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_3);
 x_84 = lean::box(0);
}
x_85 = 0;
if (lean::is_scalar(x_84)) {
 x_86 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_86 = x_84;
}
lean::cnstr_set(x_86, 0, x_7);
lean::cnstr_set(x_86, 1, x_80);
lean::cnstr_set(x_86, 2, x_82);
lean::cnstr_set(x_86, 3, x_78);
lean::cnstr_set_scalar(x_86, sizeof(void*)*4, x_85);
x_87 = x_86;
x_88 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_0);
lean::cnstr_set(x_88, 2, x_1);
lean::cnstr_set(x_88, 3, x_2);
lean::cnstr_set_scalar(x_88, sizeof(void*)*4, x_54);
x_89 = x_88;
return x_89;
}
else
{
uint8 x_90; 
x_90 = lean::cnstr_get_scalar<uint8>(x_78, sizeof(void*)*4);
if (x_90 == 0)
{
obj* x_91; obj* x_93; obj* x_95; obj* x_96; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_91 = lean::cnstr_get(x_3, 1);
x_93 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_95 = x_3;
} else {
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_3);
 x_95 = lean::box(0);
}
x_96 = lean::cnstr_get(x_78, 0);
x_98 = lean::cnstr_get(x_78, 1);
x_100 = lean::cnstr_get(x_78, 2);
x_102 = lean::cnstr_get(x_78, 3);
if (lean::is_exclusive(x_78)) {
 x_104 = x_78;
} else {
 lean::inc(x_96);
 lean::inc(x_98);
 lean::inc(x_100);
 lean::inc(x_102);
 lean::dec(x_78);
 x_104 = lean::box(0);
}
lean::inc(x_7);
if (lean::is_scalar(x_104)) {
 x_106 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_106 = x_104;
}
lean::cnstr_set(x_106, 0, x_7);
lean::cnstr_set(x_106, 1, x_91);
lean::cnstr_set(x_106, 2, x_93);
lean::cnstr_set(x_106, 3, x_96);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 lean::cnstr_release(x_7, 3);
 x_107 = x_7;
} else {
 lean::dec(x_7);
 x_107 = lean::box(0);
}
lean::cnstr_set_scalar(x_106, sizeof(void*)*4, x_54);
x_108 = x_106;
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_102);
lean::cnstr_set(x_109, 1, x_0);
lean::cnstr_set(x_109, 2, x_1);
lean::cnstr_set(x_109, 3, x_2);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_54);
x_110 = x_109;
if (lean::is_scalar(x_95)) {
 x_111 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_111 = x_95;
}
lean::cnstr_set(x_111, 0, x_108);
lean::cnstr_set(x_111, 1, x_98);
lean::cnstr_set(x_111, 2, x_100);
lean::cnstr_set(x_111, 3, x_110);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_90);
x_112 = x_111;
return x_112;
}
else
{
obj* x_113; obj* x_115; obj* x_117; obj* x_118; obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_127; obj* x_128; uint8 x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_113 = lean::cnstr_get(x_3, 1);
x_115 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_117 = x_3;
} else {
 lean::inc(x_113);
 lean::inc(x_115);
 lean::dec(x_3);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_7, 0);
x_120 = lean::cnstr_get(x_7, 1);
x_122 = lean::cnstr_get(x_7, 2);
x_124 = lean::cnstr_get(x_7, 3);
if (lean::is_exclusive(x_7)) {
 x_126 = x_7;
} else {
 lean::inc(x_118);
 lean::inc(x_120);
 lean::inc(x_122);
 lean::inc(x_124);
 lean::dec(x_7);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_118);
lean::cnstr_set(x_127, 1, x_120);
lean::cnstr_set(x_127, 2, x_122);
lean::cnstr_set(x_127, 3, x_124);
lean::cnstr_set_scalar(x_127, sizeof(void*)*4, x_90);
x_128 = x_127;
x_129 = 0;
if (lean::is_scalar(x_117)) {
 x_130 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_130 = x_117;
}
lean::cnstr_set(x_130, 0, x_128);
lean::cnstr_set(x_130, 1, x_113);
lean::cnstr_set(x_130, 2, x_115);
lean::cnstr_set(x_130, 3, x_78);
lean::cnstr_set_scalar(x_130, sizeof(void*)*4, x_129);
x_131 = x_130;
x_132 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_0);
lean::cnstr_set(x_132, 2, x_1);
lean::cnstr_set(x_132, 3, x_2);
lean::cnstr_set_scalar(x_132, sizeof(void*)*4, x_90);
x_133 = x_132;
return x_133;
}
}
}
}
}
}
}
obj* l_RBNode_balance1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balance1___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_balance1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_balance1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_balance2___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_3, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; 
x_11 = lean::cnstr_get(x_3, 1);
x_13 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_15 = x_3;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_3);
 x_15 = lean::box(0);
}
x_16 = 0;
if (lean::is_scalar(x_15)) {
 x_17 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_17 = x_15;
}
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_11);
lean::cnstr_set(x_17, 2, x_13);
lean::cnstr_set(x_17, 3, x_9);
lean::cnstr_set_scalar(x_17, sizeof(void*)*4, x_16);
x_18 = x_17;
x_19 = 1;
x_20 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_20, 0, x_0);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_18);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_19);
x_21 = x_20;
return x_21;
}
else
{
uint8 x_22; 
x_22 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*4);
if (x_22 == 0)
{
obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_23 = lean::cnstr_get(x_3, 1);
x_25 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_27 = x_3;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_3);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_9, 0);
x_30 = lean::cnstr_get(x_9, 1);
x_32 = lean::cnstr_get(x_9, 2);
x_34 = lean::cnstr_get(x_9, 3);
if (lean::is_exclusive(x_9)) {
 x_36 = x_9;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_9);
 x_36 = lean::box(0);
}
x_37 = 1;
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_0);
lean::cnstr_set(x_38, 1, x_1);
lean::cnstr_set(x_38, 2, x_2);
lean::cnstr_set(x_38, 3, x_7);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_37);
x_39 = x_38;
if (lean::is_scalar(x_27)) {
 x_40 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_40 = x_27;
}
lean::cnstr_set(x_40, 0, x_28);
lean::cnstr_set(x_40, 1, x_30);
lean::cnstr_set(x_40, 2, x_32);
lean::cnstr_set(x_40, 3, x_34);
lean::cnstr_set_scalar(x_40, sizeof(void*)*4, x_37);
x_41 = x_40;
x_42 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_42, 0, x_39);
lean::cnstr_set(x_42, 1, x_23);
lean::cnstr_set(x_42, 2, x_25);
lean::cnstr_set(x_42, 3, x_41);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_22);
x_43 = x_42;
return x_43;
}
else
{
obj* x_44; obj* x_46; obj* x_48; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_44 = lean::cnstr_get(x_3, 1);
x_46 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_48 = x_3;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_3);
 x_48 = lean::box(0);
}
x_49 = 0;
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_7);
lean::cnstr_set(x_50, 1, x_44);
lean::cnstr_set(x_50, 2, x_46);
lean::cnstr_set(x_50, 3, x_9);
lean::cnstr_set_scalar(x_50, sizeof(void*)*4, x_49);
x_51 = x_50;
x_52 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_52, 0, x_0);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*4, x_22);
x_53 = x_52;
return x_53;
}
}
}
else
{
uint8 x_54; 
x_54 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*4);
if (x_54 == 0)
{
obj* x_55; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_70; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_55 = lean::cnstr_get(x_3, 1);
x_57 = lean::cnstr_get(x_3, 2);
x_59 = lean::cnstr_get(x_3, 3);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_61 = x_3;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_3);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_7, 0);
x_64 = lean::cnstr_get(x_7, 1);
x_66 = lean::cnstr_get(x_7, 2);
x_68 = lean::cnstr_get(x_7, 3);
if (lean::is_exclusive(x_7)) {
 x_70 = x_7;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::inc(x_66);
 lean::inc(x_68);
 lean::dec(x_7);
 x_70 = lean::box(0);
}
x_71 = 1;
if (lean::is_scalar(x_70)) {
 x_72 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_72 = x_70;
}
lean::cnstr_set(x_72, 0, x_0);
lean::cnstr_set(x_72, 1, x_1);
lean::cnstr_set(x_72, 2, x_2);
lean::cnstr_set(x_72, 3, x_62);
lean::cnstr_set_scalar(x_72, sizeof(void*)*4, x_71);
x_73 = x_72;
if (lean::is_scalar(x_61)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_61;
}
lean::cnstr_set(x_74, 0, x_68);
lean::cnstr_set(x_74, 1, x_55);
lean::cnstr_set(x_74, 2, x_57);
lean::cnstr_set(x_74, 3, x_59);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_71);
x_75 = x_74;
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set(x_76, 1, x_64);
lean::cnstr_set(x_76, 2, x_66);
lean::cnstr_set(x_76, 3, x_75);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_54);
x_77 = x_76;
return x_77;
}
else
{
obj* x_78; 
x_78 = lean::cnstr_get(x_3, 3);
lean::inc(x_78);
if (lean::obj_tag(x_78) == 0)
{
obj* x_80; obj* x_82; obj* x_84; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_80 = lean::cnstr_get(x_3, 1);
x_82 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_84 = x_3;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_3);
 x_84 = lean::box(0);
}
x_85 = 0;
if (lean::is_scalar(x_84)) {
 x_86 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_86 = x_84;
}
lean::cnstr_set(x_86, 0, x_7);
lean::cnstr_set(x_86, 1, x_80);
lean::cnstr_set(x_86, 2, x_82);
lean::cnstr_set(x_86, 3, x_78);
lean::cnstr_set_scalar(x_86, sizeof(void*)*4, x_85);
x_87 = x_86;
x_88 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_88, 0, x_0);
lean::cnstr_set(x_88, 1, x_1);
lean::cnstr_set(x_88, 2, x_2);
lean::cnstr_set(x_88, 3, x_87);
lean::cnstr_set_scalar(x_88, sizeof(void*)*4, x_54);
x_89 = x_88;
return x_89;
}
else
{
uint8 x_90; 
x_90 = lean::cnstr_get_scalar<uint8>(x_78, sizeof(void*)*4);
if (x_90 == 0)
{
obj* x_91; obj* x_93; obj* x_95; obj* x_96; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_91 = lean::cnstr_get(x_3, 1);
x_93 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_95 = x_3;
} else {
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_3);
 x_95 = lean::box(0);
}
x_96 = lean::cnstr_get(x_78, 0);
x_98 = lean::cnstr_get(x_78, 1);
x_100 = lean::cnstr_get(x_78, 2);
x_102 = lean::cnstr_get(x_78, 3);
if (lean::is_exclusive(x_78)) {
 x_104 = x_78;
} else {
 lean::inc(x_96);
 lean::inc(x_98);
 lean::inc(x_100);
 lean::inc(x_102);
 lean::dec(x_78);
 x_104 = lean::box(0);
}
lean::inc(x_7);
if (lean::is_scalar(x_104)) {
 x_106 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_106 = x_104;
}
lean::cnstr_set(x_106, 0, x_0);
lean::cnstr_set(x_106, 1, x_1);
lean::cnstr_set(x_106, 2, x_2);
lean::cnstr_set(x_106, 3, x_7);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 lean::cnstr_release(x_7, 3);
 x_107 = x_7;
} else {
 lean::dec(x_7);
 x_107 = lean::box(0);
}
lean::cnstr_set_scalar(x_106, sizeof(void*)*4, x_54);
x_108 = x_106;
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_96);
lean::cnstr_set(x_109, 1, x_98);
lean::cnstr_set(x_109, 2, x_100);
lean::cnstr_set(x_109, 3, x_102);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_54);
x_110 = x_109;
if (lean::is_scalar(x_95)) {
 x_111 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_111 = x_95;
}
lean::cnstr_set(x_111, 0, x_108);
lean::cnstr_set(x_111, 1, x_91);
lean::cnstr_set(x_111, 2, x_93);
lean::cnstr_set(x_111, 3, x_110);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_90);
x_112 = x_111;
return x_112;
}
else
{
obj* x_113; obj* x_115; obj* x_117; obj* x_118; obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_127; obj* x_128; uint8 x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_113 = lean::cnstr_get(x_3, 1);
x_115 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_117 = x_3;
} else {
 lean::inc(x_113);
 lean::inc(x_115);
 lean::dec(x_3);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_7, 0);
x_120 = lean::cnstr_get(x_7, 1);
x_122 = lean::cnstr_get(x_7, 2);
x_124 = lean::cnstr_get(x_7, 3);
if (lean::is_exclusive(x_7)) {
 x_126 = x_7;
} else {
 lean::inc(x_118);
 lean::inc(x_120);
 lean::inc(x_122);
 lean::inc(x_124);
 lean::dec(x_7);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_118);
lean::cnstr_set(x_127, 1, x_120);
lean::cnstr_set(x_127, 2, x_122);
lean::cnstr_set(x_127, 3, x_124);
lean::cnstr_set_scalar(x_127, sizeof(void*)*4, x_90);
x_128 = x_127;
x_129 = 0;
if (lean::is_scalar(x_117)) {
 x_130 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_130 = x_117;
}
lean::cnstr_set(x_130, 0, x_128);
lean::cnstr_set(x_130, 1, x_113);
lean::cnstr_set(x_130, 2, x_115);
lean::cnstr_set(x_130, 3, x_78);
lean::cnstr_set_scalar(x_130, sizeof(void*)*4, x_129);
x_131 = x_130;
x_132 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_132, 0, x_0);
lean::cnstr_set(x_132, 1, x_1);
lean::cnstr_set(x_132, 2, x_2);
lean::cnstr_set(x_132, 3, x_131);
lean::cnstr_set_scalar(x_132, sizeof(void*)*4, x_90);
x_133 = x_132;
return x_133;
}
}
}
}
}
}
}
obj* l_RBNode_balance2___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balance2___main___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_balance2___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_balance2___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_balance2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_3, 3);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; 
x_11 = lean::cnstr_get(x_3, 1);
x_13 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_15 = x_3;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_3);
 x_15 = lean::box(0);
}
x_16 = 0;
if (lean::is_scalar(x_15)) {
 x_17 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_17 = x_15;
}
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_11);
lean::cnstr_set(x_17, 2, x_13);
lean::cnstr_set(x_17, 3, x_9);
lean::cnstr_set_scalar(x_17, sizeof(void*)*4, x_16);
x_18 = x_17;
x_19 = 1;
x_20 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_20, 0, x_0);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_18);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_19);
x_21 = x_20;
return x_21;
}
else
{
uint8 x_22; 
x_22 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*4);
if (x_22 == 0)
{
obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_23 = lean::cnstr_get(x_3, 1);
x_25 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_27 = x_3;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_3);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_9, 0);
x_30 = lean::cnstr_get(x_9, 1);
x_32 = lean::cnstr_get(x_9, 2);
x_34 = lean::cnstr_get(x_9, 3);
if (lean::is_exclusive(x_9)) {
 x_36 = x_9;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_9);
 x_36 = lean::box(0);
}
x_37 = 1;
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_0);
lean::cnstr_set(x_38, 1, x_1);
lean::cnstr_set(x_38, 2, x_2);
lean::cnstr_set(x_38, 3, x_7);
lean::cnstr_set_scalar(x_38, sizeof(void*)*4, x_37);
x_39 = x_38;
if (lean::is_scalar(x_27)) {
 x_40 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_40 = x_27;
}
lean::cnstr_set(x_40, 0, x_28);
lean::cnstr_set(x_40, 1, x_30);
lean::cnstr_set(x_40, 2, x_32);
lean::cnstr_set(x_40, 3, x_34);
lean::cnstr_set_scalar(x_40, sizeof(void*)*4, x_37);
x_41 = x_40;
x_42 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_42, 0, x_39);
lean::cnstr_set(x_42, 1, x_23);
lean::cnstr_set(x_42, 2, x_25);
lean::cnstr_set(x_42, 3, x_41);
lean::cnstr_set_scalar(x_42, sizeof(void*)*4, x_22);
x_43 = x_42;
return x_43;
}
else
{
obj* x_44; obj* x_46; obj* x_48; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_44 = lean::cnstr_get(x_3, 1);
x_46 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_48 = x_3;
} else {
 lean::inc(x_44);
 lean::inc(x_46);
 lean::dec(x_3);
 x_48 = lean::box(0);
}
x_49 = 0;
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_7);
lean::cnstr_set(x_50, 1, x_44);
lean::cnstr_set(x_50, 2, x_46);
lean::cnstr_set(x_50, 3, x_9);
lean::cnstr_set_scalar(x_50, sizeof(void*)*4, x_49);
x_51 = x_50;
x_52 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_52, 0, x_0);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*4, x_22);
x_53 = x_52;
return x_53;
}
}
}
else
{
uint8 x_54; 
x_54 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*4);
if (x_54 == 0)
{
obj* x_55; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_70; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_55 = lean::cnstr_get(x_3, 1);
x_57 = lean::cnstr_get(x_3, 2);
x_59 = lean::cnstr_get(x_3, 3);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_61 = x_3;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_3);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_7, 0);
x_64 = lean::cnstr_get(x_7, 1);
x_66 = lean::cnstr_get(x_7, 2);
x_68 = lean::cnstr_get(x_7, 3);
if (lean::is_exclusive(x_7)) {
 x_70 = x_7;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::inc(x_66);
 lean::inc(x_68);
 lean::dec(x_7);
 x_70 = lean::box(0);
}
x_71 = 1;
if (lean::is_scalar(x_70)) {
 x_72 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_72 = x_70;
}
lean::cnstr_set(x_72, 0, x_0);
lean::cnstr_set(x_72, 1, x_1);
lean::cnstr_set(x_72, 2, x_2);
lean::cnstr_set(x_72, 3, x_62);
lean::cnstr_set_scalar(x_72, sizeof(void*)*4, x_71);
x_73 = x_72;
if (lean::is_scalar(x_61)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_61;
}
lean::cnstr_set(x_74, 0, x_68);
lean::cnstr_set(x_74, 1, x_55);
lean::cnstr_set(x_74, 2, x_57);
lean::cnstr_set(x_74, 3, x_59);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_71);
x_75 = x_74;
x_76 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set(x_76, 1, x_64);
lean::cnstr_set(x_76, 2, x_66);
lean::cnstr_set(x_76, 3, x_75);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_54);
x_77 = x_76;
return x_77;
}
else
{
obj* x_78; 
x_78 = lean::cnstr_get(x_3, 3);
lean::inc(x_78);
if (lean::obj_tag(x_78) == 0)
{
obj* x_80; obj* x_82; obj* x_84; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_80 = lean::cnstr_get(x_3, 1);
x_82 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_84 = x_3;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_3);
 x_84 = lean::box(0);
}
x_85 = 0;
if (lean::is_scalar(x_84)) {
 x_86 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_86 = x_84;
}
lean::cnstr_set(x_86, 0, x_7);
lean::cnstr_set(x_86, 1, x_80);
lean::cnstr_set(x_86, 2, x_82);
lean::cnstr_set(x_86, 3, x_78);
lean::cnstr_set_scalar(x_86, sizeof(void*)*4, x_85);
x_87 = x_86;
x_88 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_88, 0, x_0);
lean::cnstr_set(x_88, 1, x_1);
lean::cnstr_set(x_88, 2, x_2);
lean::cnstr_set(x_88, 3, x_87);
lean::cnstr_set_scalar(x_88, sizeof(void*)*4, x_54);
x_89 = x_88;
return x_89;
}
else
{
uint8 x_90; 
x_90 = lean::cnstr_get_scalar<uint8>(x_78, sizeof(void*)*4);
if (x_90 == 0)
{
obj* x_91; obj* x_93; obj* x_95; obj* x_96; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_91 = lean::cnstr_get(x_3, 1);
x_93 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_95 = x_3;
} else {
 lean::inc(x_91);
 lean::inc(x_93);
 lean::dec(x_3);
 x_95 = lean::box(0);
}
x_96 = lean::cnstr_get(x_78, 0);
x_98 = lean::cnstr_get(x_78, 1);
x_100 = lean::cnstr_get(x_78, 2);
x_102 = lean::cnstr_get(x_78, 3);
if (lean::is_exclusive(x_78)) {
 x_104 = x_78;
} else {
 lean::inc(x_96);
 lean::inc(x_98);
 lean::inc(x_100);
 lean::inc(x_102);
 lean::dec(x_78);
 x_104 = lean::box(0);
}
lean::inc(x_7);
if (lean::is_scalar(x_104)) {
 x_106 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_106 = x_104;
}
lean::cnstr_set(x_106, 0, x_0);
lean::cnstr_set(x_106, 1, x_1);
lean::cnstr_set(x_106, 2, x_2);
lean::cnstr_set(x_106, 3, x_7);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 lean::cnstr_release(x_7, 3);
 x_107 = x_7;
} else {
 lean::dec(x_7);
 x_107 = lean::box(0);
}
lean::cnstr_set_scalar(x_106, sizeof(void*)*4, x_54);
x_108 = x_106;
if (lean::is_scalar(x_107)) {
 x_109 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_109 = x_107;
}
lean::cnstr_set(x_109, 0, x_96);
lean::cnstr_set(x_109, 1, x_98);
lean::cnstr_set(x_109, 2, x_100);
lean::cnstr_set(x_109, 3, x_102);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_54);
x_110 = x_109;
if (lean::is_scalar(x_95)) {
 x_111 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_111 = x_95;
}
lean::cnstr_set(x_111, 0, x_108);
lean::cnstr_set(x_111, 1, x_91);
lean::cnstr_set(x_111, 2, x_93);
lean::cnstr_set(x_111, 3, x_110);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_90);
x_112 = x_111;
return x_112;
}
else
{
obj* x_113; obj* x_115; obj* x_117; obj* x_118; obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_127; obj* x_128; uint8 x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_113 = lean::cnstr_get(x_3, 1);
x_115 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_117 = x_3;
} else {
 lean::inc(x_113);
 lean::inc(x_115);
 lean::dec(x_3);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_7, 0);
x_120 = lean::cnstr_get(x_7, 1);
x_122 = lean::cnstr_get(x_7, 2);
x_124 = lean::cnstr_get(x_7, 3);
if (lean::is_exclusive(x_7)) {
 x_126 = x_7;
} else {
 lean::inc(x_118);
 lean::inc(x_120);
 lean::inc(x_122);
 lean::inc(x_124);
 lean::dec(x_7);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_118);
lean::cnstr_set(x_127, 1, x_120);
lean::cnstr_set(x_127, 2, x_122);
lean::cnstr_set(x_127, 3, x_124);
lean::cnstr_set_scalar(x_127, sizeof(void*)*4, x_90);
x_128 = x_127;
x_129 = 0;
if (lean::is_scalar(x_117)) {
 x_130 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_130 = x_117;
}
lean::cnstr_set(x_130, 0, x_128);
lean::cnstr_set(x_130, 1, x_113);
lean::cnstr_set(x_130, 2, x_115);
lean::cnstr_set(x_130, 3, x_78);
lean::cnstr_set_scalar(x_130, sizeof(void*)*4, x_129);
x_131 = x_130;
x_132 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_132, 0, x_0);
lean::cnstr_set(x_132, 1, x_1);
lean::cnstr_set(x_132, 2, x_2);
lean::cnstr_set(x_132, 3, x_131);
lean::cnstr_set_scalar(x_132, sizeof(void*)*4, x_90);
x_133 = x_132;
return x_133;
}
}
}
}
}
}
}
obj* l_RBNode_balance2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balance2___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_balance2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_balance2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBNode_isRed___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
else
{
uint8 x_2; 
x_2 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_2 == 0)
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
}
}
}
obj* l_RBNode_isRed___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_isRed___main___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_RBNode_isRed___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_RBNode_isRed___main___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBNode_isRed___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_isRed___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBNode_isRed___rarg(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_RBNode_isRed___main___rarg(x_0);
return x_1;
}
}
obj* l_RBNode_isRed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_isRed___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_RBNode_isRed___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_RBNode_isRed___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBNode_isRed___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_isRed(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_ins___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::dec(x_0);
x_5 = 0;
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_5);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_21; uint8 x_22; 
x_9 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_1, 2);
x_15 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_17 = x_1;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
lean::inc(x_11);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_2(x_0, x_2, x_11);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
obj* x_26; uint8 x_27; 
lean::inc(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_11, x_2);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_3);
lean::cnstr_set(x_31, 3, x_15);
lean::cnstr_set_scalar(x_31, sizeof(void*)*4, x_8);
x_32 = x_31;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_RBNode_ins___main___rarg(x_0, x_15, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_11);
lean::cnstr_set(x_34, 2, x_13);
lean::cnstr_set(x_34, 3, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_8);
x_35 = x_34;
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = l_RBNode_ins___main___rarg(x_0, x_9, x_2, x_3);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_11);
lean::cnstr_set(x_37, 2, x_13);
lean::cnstr_set(x_37, 3, x_15);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_8);
x_38 = x_37;
return x_38;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_51; uint8 x_52; 
x_39 = lean::cnstr_get(x_1, 0);
x_41 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_1, 2);
x_45 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_47 = x_1;
} else {
 lean::inc(x_39);
 lean::inc(x_41);
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_1);
 x_47 = lean::box(0);
}
lean::inc(x_41);
lean::inc(x_2);
lean::inc(x_0);
x_51 = lean::apply_2(x_0, x_2, x_41);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_56; uint8 x_57; 
lean::inc(x_2);
lean::inc(x_41);
lean::inc(x_0);
x_56 = lean::apply_2(x_0, x_41, x_2);
x_57 = lean::unbox(x_56);
if (x_57 == 0)
{
obj* x_61; obj* x_62; 
lean::dec(x_0);
lean::dec(x_41);
lean::dec(x_43);
if (lean::is_scalar(x_47)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_47;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_2);
lean::cnstr_set(x_61, 2, x_3);
lean::cnstr_set(x_61, 3, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_8);
x_62 = x_61;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_RBNode_isRed___main___rarg(x_45);
if (x_63 == 0)
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = l_RBNode_ins___main___rarg(x_0, x_45, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_47;
}
lean::cnstr_set(x_65, 0, x_39);
lean::cnstr_set(x_65, 1, x_41);
lean::cnstr_set(x_65, 2, x_43);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_8);
x_66 = x_65;
return x_66;
}
else
{
obj* x_67; 
x_67 = l_RBNode_ins___main___rarg(x_0, x_45, x_2, x_3);
if (lean::obj_tag(x_67) == 0)
{
lean::dec(x_47);
lean::dec(x_39);
lean::dec(x_41);
lean::dec(x_43);
return x_67;
}
else
{
obj* x_72; 
x_72 = lean::cnstr_get(x_67, 0);
lean::inc(x_72);
if (lean::obj_tag(x_72) == 0)
{
obj* x_74; 
x_74 = lean::cnstr_get(x_67, 3);
lean::inc(x_74);
if (lean::obj_tag(x_74) == 0)
{
obj* x_76; obj* x_78; obj* x_80; uint8 x_81; obj* x_82; obj* x_83; uint8 x_84; obj* x_85; obj* x_86; 
x_76 = lean::cnstr_get(x_67, 1);
x_78 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 3);
 x_80 = x_67;
} else {
 lean::inc(x_76);
 lean::inc(x_78);
 lean::dec(x_67);
 x_80 = lean::box(0);
}
x_81 = 0;
if (lean::is_scalar(x_80)) {
 x_82 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_82 = x_80;
}
lean::cnstr_set(x_82, 0, x_74);
lean::cnstr_set(x_82, 1, x_76);
lean::cnstr_set(x_82, 2, x_78);
lean::cnstr_set(x_82, 3, x_74);
lean::cnstr_set_scalar(x_82, sizeof(void*)*4, x_81);
x_83 = x_82;
x_84 = 1;
if (lean::is_scalar(x_47)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_47;
}
lean::cnstr_set(x_85, 0, x_39);
lean::cnstr_set(x_85, 1, x_41);
lean::cnstr_set(x_85, 2, x_43);
lean::cnstr_set(x_85, 3, x_83);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_84);
x_86 = x_85;
return x_86;
}
else
{
uint8 x_87; 
x_87 = lean::cnstr_get_scalar<uint8>(x_74, sizeof(void*)*4);
if (x_87 == 0)
{
obj* x_88; obj* x_90; obj* x_92; obj* x_93; obj* x_95; obj* x_97; obj* x_99; obj* x_101; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_88 = lean::cnstr_get(x_67, 1);
x_90 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 3);
 x_92 = x_67;
} else {
 lean::inc(x_88);
 lean::inc(x_90);
 lean::dec(x_67);
 x_92 = lean::box(0);
}
x_93 = lean::cnstr_get(x_74, 0);
x_95 = lean::cnstr_get(x_74, 1);
x_97 = lean::cnstr_get(x_74, 2);
x_99 = lean::cnstr_get(x_74, 3);
if (lean::is_exclusive(x_74)) {
 x_101 = x_74;
} else {
 lean::inc(x_93);
 lean::inc(x_95);
 lean::inc(x_97);
 lean::inc(x_99);
 lean::dec(x_74);
 x_101 = lean::box(0);
}
x_102 = 1;
if (lean::is_scalar(x_101)) {
 x_103 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_103 = x_101;
}
lean::cnstr_set(x_103, 0, x_39);
lean::cnstr_set(x_103, 1, x_41);
lean::cnstr_set(x_103, 2, x_43);
lean::cnstr_set(x_103, 3, x_72);
lean::cnstr_set_scalar(x_103, sizeof(void*)*4, x_102);
x_104 = x_103;
if (lean::is_scalar(x_92)) {
 x_105 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_105 = x_92;
}
lean::cnstr_set(x_105, 0, x_93);
lean::cnstr_set(x_105, 1, x_95);
lean::cnstr_set(x_105, 2, x_97);
lean::cnstr_set(x_105, 3, x_99);
lean::cnstr_set_scalar(x_105, sizeof(void*)*4, x_102);
x_106 = x_105;
if (lean::is_scalar(x_47)) {
 x_107 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_107 = x_47;
}
lean::cnstr_set(x_107, 0, x_104);
lean::cnstr_set(x_107, 1, x_88);
lean::cnstr_set(x_107, 2, x_90);
lean::cnstr_set(x_107, 3, x_106);
lean::cnstr_set_scalar(x_107, sizeof(void*)*4, x_87);
x_108 = x_107;
return x_108;
}
else
{
obj* x_109; obj* x_111; obj* x_113; uint8 x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_109 = lean::cnstr_get(x_67, 1);
x_111 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 3);
 x_113 = x_67;
} else {
 lean::inc(x_109);
 lean::inc(x_111);
 lean::dec(x_67);
 x_113 = lean::box(0);
}
x_114 = 0;
if (lean::is_scalar(x_113)) {
 x_115 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_115 = x_113;
}
lean::cnstr_set(x_115, 0, x_72);
lean::cnstr_set(x_115, 1, x_109);
lean::cnstr_set(x_115, 2, x_111);
lean::cnstr_set(x_115, 3, x_74);
lean::cnstr_set_scalar(x_115, sizeof(void*)*4, x_114);
x_116 = x_115;
if (lean::is_scalar(x_47)) {
 x_117 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_117 = x_47;
}
lean::cnstr_set(x_117, 0, x_39);
lean::cnstr_set(x_117, 1, x_41);
lean::cnstr_set(x_117, 2, x_43);
lean::cnstr_set(x_117, 3, x_116);
lean::cnstr_set_scalar(x_117, sizeof(void*)*4, x_87);
x_118 = x_117;
return x_118;
}
}
}
else
{
uint8 x_119; 
x_119 = lean::cnstr_get_scalar<uint8>(x_72, sizeof(void*)*4);
if (x_119 == 0)
{
obj* x_120; obj* x_122; obj* x_124; obj* x_126; obj* x_127; obj* x_129; obj* x_131; obj* x_133; obj* x_135; uint8 x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_120 = lean::cnstr_get(x_67, 1);
x_122 = lean::cnstr_get(x_67, 2);
x_124 = lean::cnstr_get(x_67, 3);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 x_126 = x_67;
} else {
 lean::inc(x_120);
 lean::inc(x_122);
 lean::inc(x_124);
 lean::dec(x_67);
 x_126 = lean::box(0);
}
x_127 = lean::cnstr_get(x_72, 0);
x_129 = lean::cnstr_get(x_72, 1);
x_131 = lean::cnstr_get(x_72, 2);
x_133 = lean::cnstr_get(x_72, 3);
if (lean::is_exclusive(x_72)) {
 x_135 = x_72;
} else {
 lean::inc(x_127);
 lean::inc(x_129);
 lean::inc(x_131);
 lean::inc(x_133);
 lean::dec(x_72);
 x_135 = lean::box(0);
}
x_136 = 1;
if (lean::is_scalar(x_135)) {
 x_137 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_137 = x_135;
}
lean::cnstr_set(x_137, 0, x_39);
lean::cnstr_set(x_137, 1, x_41);
lean::cnstr_set(x_137, 2, x_43);
lean::cnstr_set(x_137, 3, x_127);
lean::cnstr_set_scalar(x_137, sizeof(void*)*4, x_136);
x_138 = x_137;
if (lean::is_scalar(x_126)) {
 x_139 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_139 = x_126;
}
lean::cnstr_set(x_139, 0, x_133);
lean::cnstr_set(x_139, 1, x_120);
lean::cnstr_set(x_139, 2, x_122);
lean::cnstr_set(x_139, 3, x_124);
lean::cnstr_set_scalar(x_139, sizeof(void*)*4, x_136);
x_140 = x_139;
if (lean::is_scalar(x_47)) {
 x_141 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_141 = x_47;
}
lean::cnstr_set(x_141, 0, x_138);
lean::cnstr_set(x_141, 1, x_129);
lean::cnstr_set(x_141, 2, x_131);
lean::cnstr_set(x_141, 3, x_140);
lean::cnstr_set_scalar(x_141, sizeof(void*)*4, x_119);
x_142 = x_141;
return x_142;
}
else
{
obj* x_143; 
x_143 = lean::cnstr_get(x_67, 3);
lean::inc(x_143);
if (lean::obj_tag(x_143) == 0)
{
obj* x_145; obj* x_147; obj* x_149; uint8 x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; 
x_145 = lean::cnstr_get(x_67, 1);
x_147 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 3);
 x_149 = x_67;
} else {
 lean::inc(x_145);
 lean::inc(x_147);
 lean::dec(x_67);
 x_149 = lean::box(0);
}
x_150 = 0;
if (lean::is_scalar(x_149)) {
 x_151 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_151 = x_149;
}
lean::cnstr_set(x_151, 0, x_72);
lean::cnstr_set(x_151, 1, x_145);
lean::cnstr_set(x_151, 2, x_147);
lean::cnstr_set(x_151, 3, x_143);
lean::cnstr_set_scalar(x_151, sizeof(void*)*4, x_150);
x_152 = x_151;
if (lean::is_scalar(x_47)) {
 x_153 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_153 = x_47;
}
lean::cnstr_set(x_153, 0, x_39);
lean::cnstr_set(x_153, 1, x_41);
lean::cnstr_set(x_153, 2, x_43);
lean::cnstr_set(x_153, 3, x_152);
lean::cnstr_set_scalar(x_153, sizeof(void*)*4, x_119);
x_154 = x_153;
return x_154;
}
else
{
uint8 x_155; 
x_155 = lean::cnstr_get_scalar<uint8>(x_143, sizeof(void*)*4);
if (x_155 == 0)
{
obj* x_157; obj* x_159; obj* x_161; obj* x_162; obj* x_164; obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; 
lean::dec(x_47);
x_157 = lean::cnstr_get(x_67, 1);
x_159 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 3);
 x_161 = x_67;
} else {
 lean::inc(x_157);
 lean::inc(x_159);
 lean::dec(x_67);
 x_161 = lean::box(0);
}
x_162 = lean::cnstr_get(x_143, 0);
x_164 = lean::cnstr_get(x_143, 1);
x_166 = lean::cnstr_get(x_143, 2);
x_168 = lean::cnstr_get(x_143, 3);
if (lean::is_exclusive(x_143)) {
 x_170 = x_143;
} else {
 lean::inc(x_162);
 lean::inc(x_164);
 lean::inc(x_166);
 lean::inc(x_168);
 lean::dec(x_143);
 x_170 = lean::box(0);
}
lean::inc(x_72);
if (lean::is_scalar(x_170)) {
 x_172 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_172 = x_170;
}
lean::cnstr_set(x_172, 0, x_39);
lean::cnstr_set(x_172, 1, x_41);
lean::cnstr_set(x_172, 2, x_43);
lean::cnstr_set(x_172, 3, x_72);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 lean::cnstr_release(x_72, 1);
 lean::cnstr_release(x_72, 2);
 lean::cnstr_release(x_72, 3);
 x_173 = x_72;
} else {
 lean::dec(x_72);
 x_173 = lean::box(0);
}
lean::cnstr_set_scalar(x_172, sizeof(void*)*4, x_119);
x_174 = x_172;
if (lean::is_scalar(x_173)) {
 x_175 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_175 = x_173;
}
lean::cnstr_set(x_175, 0, x_162);
lean::cnstr_set(x_175, 1, x_164);
lean::cnstr_set(x_175, 2, x_166);
lean::cnstr_set(x_175, 3, x_168);
lean::cnstr_set_scalar(x_175, sizeof(void*)*4, x_119);
x_176 = x_175;
if (lean::is_scalar(x_161)) {
 x_177 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_177 = x_161;
}
lean::cnstr_set(x_177, 0, x_174);
lean::cnstr_set(x_177, 1, x_157);
lean::cnstr_set(x_177, 2, x_159);
lean::cnstr_set(x_177, 3, x_176);
lean::cnstr_set_scalar(x_177, sizeof(void*)*4, x_155);
x_178 = x_177;
return x_178;
}
else
{
obj* x_179; obj* x_181; obj* x_183; obj* x_184; obj* x_186; obj* x_188; obj* x_190; obj* x_192; obj* x_193; obj* x_194; uint8 x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; 
x_179 = lean::cnstr_get(x_67, 1);
x_181 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 lean::cnstr_release(x_67, 3);
 x_183 = x_67;
} else {
 lean::inc(x_179);
 lean::inc(x_181);
 lean::dec(x_67);
 x_183 = lean::box(0);
}
x_184 = lean::cnstr_get(x_72, 0);
x_186 = lean::cnstr_get(x_72, 1);
x_188 = lean::cnstr_get(x_72, 2);
x_190 = lean::cnstr_get(x_72, 3);
if (lean::is_exclusive(x_72)) {
 x_192 = x_72;
} else {
 lean::inc(x_184);
 lean::inc(x_186);
 lean::inc(x_188);
 lean::inc(x_190);
 lean::dec(x_72);
 x_192 = lean::box(0);
}
if (lean::is_scalar(x_192)) {
 x_193 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_193 = x_192;
}
lean::cnstr_set(x_193, 0, x_184);
lean::cnstr_set(x_193, 1, x_186);
lean::cnstr_set(x_193, 2, x_188);
lean::cnstr_set(x_193, 3, x_190);
lean::cnstr_set_scalar(x_193, sizeof(void*)*4, x_155);
x_194 = x_193;
x_195 = 0;
if (lean::is_scalar(x_183)) {
 x_196 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_196 = x_183;
}
lean::cnstr_set(x_196, 0, x_194);
lean::cnstr_set(x_196, 1, x_179);
lean::cnstr_set(x_196, 2, x_181);
lean::cnstr_set(x_196, 3, x_143);
lean::cnstr_set_scalar(x_196, sizeof(void*)*4, x_195);
x_197 = x_196;
if (lean::is_scalar(x_47)) {
 x_198 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_198 = x_47;
}
lean::cnstr_set(x_198, 0, x_39);
lean::cnstr_set(x_198, 1, x_41);
lean::cnstr_set(x_198, 2, x_43);
lean::cnstr_set(x_198, 3, x_197);
lean::cnstr_set_scalar(x_198, sizeof(void*)*4, x_155);
x_199 = x_198;
return x_199;
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
uint8 x_200; 
x_200 = l_RBNode_isRed___main___rarg(x_39);
if (x_200 == 0)
{
obj* x_201; obj* x_202; obj* x_203; 
x_201 = l_RBNode_ins___main___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_202 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_202 = x_47;
}
lean::cnstr_set(x_202, 0, x_201);
lean::cnstr_set(x_202, 1, x_41);
lean::cnstr_set(x_202, 2, x_43);
lean::cnstr_set(x_202, 3, x_45);
lean::cnstr_set_scalar(x_202, sizeof(void*)*4, x_8);
x_203 = x_202;
return x_203;
}
else
{
obj* x_204; 
x_204 = l_RBNode_ins___main___rarg(x_0, x_39, x_2, x_3);
if (lean::obj_tag(x_204) == 0)
{
lean::dec(x_47);
lean::dec(x_45);
lean::dec(x_41);
lean::dec(x_43);
return x_204;
}
else
{
obj* x_209; 
x_209 = lean::cnstr_get(x_204, 0);
lean::inc(x_209);
if (lean::obj_tag(x_209) == 0)
{
obj* x_211; 
x_211 = lean::cnstr_get(x_204, 3);
lean::inc(x_211);
if (lean::obj_tag(x_211) == 0)
{
obj* x_213; obj* x_215; obj* x_217; uint8 x_218; obj* x_219; obj* x_220; uint8 x_221; obj* x_222; obj* x_223; 
x_213 = lean::cnstr_get(x_204, 1);
x_215 = lean::cnstr_get(x_204, 2);
if (lean::is_exclusive(x_204)) {
 lean::cnstr_release(x_204, 0);
 lean::cnstr_release(x_204, 3);
 x_217 = x_204;
} else {
 lean::inc(x_213);
 lean::inc(x_215);
 lean::dec(x_204);
 x_217 = lean::box(0);
}
x_218 = 0;
if (lean::is_scalar(x_217)) {
 x_219 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_219 = x_217;
}
lean::cnstr_set(x_219, 0, x_211);
lean::cnstr_set(x_219, 1, x_213);
lean::cnstr_set(x_219, 2, x_215);
lean::cnstr_set(x_219, 3, x_211);
lean::cnstr_set_scalar(x_219, sizeof(void*)*4, x_218);
x_220 = x_219;
x_221 = 1;
if (lean::is_scalar(x_47)) {
 x_222 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_222 = x_47;
}
lean::cnstr_set(x_222, 0, x_220);
lean::cnstr_set(x_222, 1, x_41);
lean::cnstr_set(x_222, 2, x_43);
lean::cnstr_set(x_222, 3, x_45);
lean::cnstr_set_scalar(x_222, sizeof(void*)*4, x_221);
x_223 = x_222;
return x_223;
}
else
{
uint8 x_224; 
x_224 = lean::cnstr_get_scalar<uint8>(x_211, sizeof(void*)*4);
if (x_224 == 0)
{
obj* x_225; obj* x_227; obj* x_229; obj* x_230; obj* x_232; obj* x_234; obj* x_236; obj* x_238; uint8 x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; 
x_225 = lean::cnstr_get(x_204, 1);
x_227 = lean::cnstr_get(x_204, 2);
if (lean::is_exclusive(x_204)) {
 lean::cnstr_release(x_204, 0);
 lean::cnstr_release(x_204, 3);
 x_229 = x_204;
} else {
 lean::inc(x_225);
 lean::inc(x_227);
 lean::dec(x_204);
 x_229 = lean::box(0);
}
x_230 = lean::cnstr_get(x_211, 0);
x_232 = lean::cnstr_get(x_211, 1);
x_234 = lean::cnstr_get(x_211, 2);
x_236 = lean::cnstr_get(x_211, 3);
if (lean::is_exclusive(x_211)) {
 x_238 = x_211;
} else {
 lean::inc(x_230);
 lean::inc(x_232);
 lean::inc(x_234);
 lean::inc(x_236);
 lean::dec(x_211);
 x_238 = lean::box(0);
}
x_239 = 1;
if (lean::is_scalar(x_238)) {
 x_240 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_240 = x_238;
}
lean::cnstr_set(x_240, 0, x_209);
lean::cnstr_set(x_240, 1, x_225);
lean::cnstr_set(x_240, 2, x_227);
lean::cnstr_set(x_240, 3, x_230);
lean::cnstr_set_scalar(x_240, sizeof(void*)*4, x_239);
x_241 = x_240;
if (lean::is_scalar(x_229)) {
 x_242 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_242 = x_229;
}
lean::cnstr_set(x_242, 0, x_236);
lean::cnstr_set(x_242, 1, x_41);
lean::cnstr_set(x_242, 2, x_43);
lean::cnstr_set(x_242, 3, x_45);
lean::cnstr_set_scalar(x_242, sizeof(void*)*4, x_239);
x_243 = x_242;
if (lean::is_scalar(x_47)) {
 x_244 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_244 = x_47;
}
lean::cnstr_set(x_244, 0, x_241);
lean::cnstr_set(x_244, 1, x_232);
lean::cnstr_set(x_244, 2, x_234);
lean::cnstr_set(x_244, 3, x_243);
lean::cnstr_set_scalar(x_244, sizeof(void*)*4, x_224);
x_245 = x_244;
return x_245;
}
else
{
obj* x_246; obj* x_248; obj* x_250; uint8 x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; 
x_246 = lean::cnstr_get(x_204, 1);
x_248 = lean::cnstr_get(x_204, 2);
if (lean::is_exclusive(x_204)) {
 lean::cnstr_release(x_204, 0);
 lean::cnstr_release(x_204, 3);
 x_250 = x_204;
} else {
 lean::inc(x_246);
 lean::inc(x_248);
 lean::dec(x_204);
 x_250 = lean::box(0);
}
x_251 = 0;
if (lean::is_scalar(x_250)) {
 x_252 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_252 = x_250;
}
lean::cnstr_set(x_252, 0, x_209);
lean::cnstr_set(x_252, 1, x_246);
lean::cnstr_set(x_252, 2, x_248);
lean::cnstr_set(x_252, 3, x_211);
lean::cnstr_set_scalar(x_252, sizeof(void*)*4, x_251);
x_253 = x_252;
if (lean::is_scalar(x_47)) {
 x_254 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_254 = x_47;
}
lean::cnstr_set(x_254, 0, x_253);
lean::cnstr_set(x_254, 1, x_41);
lean::cnstr_set(x_254, 2, x_43);
lean::cnstr_set(x_254, 3, x_45);
lean::cnstr_set_scalar(x_254, sizeof(void*)*4, x_224);
x_255 = x_254;
return x_255;
}
}
}
else
{
uint8 x_256; 
x_256 = lean::cnstr_get_scalar<uint8>(x_209, sizeof(void*)*4);
if (x_256 == 0)
{
obj* x_257; obj* x_259; obj* x_261; obj* x_263; obj* x_264; obj* x_266; obj* x_268; obj* x_270; obj* x_272; uint8 x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_277; obj* x_278; obj* x_279; 
x_257 = lean::cnstr_get(x_204, 1);
x_259 = lean::cnstr_get(x_204, 2);
x_261 = lean::cnstr_get(x_204, 3);
if (lean::is_exclusive(x_204)) {
 lean::cnstr_release(x_204, 0);
 x_263 = x_204;
} else {
 lean::inc(x_257);
 lean::inc(x_259);
 lean::inc(x_261);
 lean::dec(x_204);
 x_263 = lean::box(0);
}
x_264 = lean::cnstr_get(x_209, 0);
x_266 = lean::cnstr_get(x_209, 1);
x_268 = lean::cnstr_get(x_209, 2);
x_270 = lean::cnstr_get(x_209, 3);
if (lean::is_exclusive(x_209)) {
 x_272 = x_209;
} else {
 lean::inc(x_264);
 lean::inc(x_266);
 lean::inc(x_268);
 lean::inc(x_270);
 lean::dec(x_209);
 x_272 = lean::box(0);
}
x_273 = 1;
if (lean::is_scalar(x_272)) {
 x_274 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_274 = x_272;
}
lean::cnstr_set(x_274, 0, x_264);
lean::cnstr_set(x_274, 1, x_266);
lean::cnstr_set(x_274, 2, x_268);
lean::cnstr_set(x_274, 3, x_270);
lean::cnstr_set_scalar(x_274, sizeof(void*)*4, x_273);
x_275 = x_274;
if (lean::is_scalar(x_263)) {
 x_276 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_276 = x_263;
}
lean::cnstr_set(x_276, 0, x_261);
lean::cnstr_set(x_276, 1, x_41);
lean::cnstr_set(x_276, 2, x_43);
lean::cnstr_set(x_276, 3, x_45);
lean::cnstr_set_scalar(x_276, sizeof(void*)*4, x_273);
x_277 = x_276;
if (lean::is_scalar(x_47)) {
 x_278 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_278 = x_47;
}
lean::cnstr_set(x_278, 0, x_275);
lean::cnstr_set(x_278, 1, x_257);
lean::cnstr_set(x_278, 2, x_259);
lean::cnstr_set(x_278, 3, x_277);
lean::cnstr_set_scalar(x_278, sizeof(void*)*4, x_256);
x_279 = x_278;
return x_279;
}
else
{
obj* x_280; 
x_280 = lean::cnstr_get(x_204, 3);
lean::inc(x_280);
if (lean::obj_tag(x_280) == 0)
{
obj* x_282; obj* x_284; obj* x_286; uint8 x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; 
x_282 = lean::cnstr_get(x_204, 1);
x_284 = lean::cnstr_get(x_204, 2);
if (lean::is_exclusive(x_204)) {
 lean::cnstr_release(x_204, 0);
 lean::cnstr_release(x_204, 3);
 x_286 = x_204;
} else {
 lean::inc(x_282);
 lean::inc(x_284);
 lean::dec(x_204);
 x_286 = lean::box(0);
}
x_287 = 0;
if (lean::is_scalar(x_286)) {
 x_288 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_288 = x_286;
}
lean::cnstr_set(x_288, 0, x_209);
lean::cnstr_set(x_288, 1, x_282);
lean::cnstr_set(x_288, 2, x_284);
lean::cnstr_set(x_288, 3, x_280);
lean::cnstr_set_scalar(x_288, sizeof(void*)*4, x_287);
x_289 = x_288;
if (lean::is_scalar(x_47)) {
 x_290 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_290 = x_47;
}
lean::cnstr_set(x_290, 0, x_289);
lean::cnstr_set(x_290, 1, x_41);
lean::cnstr_set(x_290, 2, x_43);
lean::cnstr_set(x_290, 3, x_45);
lean::cnstr_set_scalar(x_290, sizeof(void*)*4, x_256);
x_291 = x_290;
return x_291;
}
else
{
uint8 x_292; 
x_292 = lean::cnstr_get_scalar<uint8>(x_280, sizeof(void*)*4);
if (x_292 == 0)
{
obj* x_294; obj* x_296; obj* x_298; obj* x_299; obj* x_301; obj* x_303; obj* x_305; obj* x_307; obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; obj* x_314; obj* x_315; 
lean::dec(x_47);
x_294 = lean::cnstr_get(x_204, 1);
x_296 = lean::cnstr_get(x_204, 2);
if (lean::is_exclusive(x_204)) {
 lean::cnstr_release(x_204, 0);
 lean::cnstr_release(x_204, 3);
 x_298 = x_204;
} else {
 lean::inc(x_294);
 lean::inc(x_296);
 lean::dec(x_204);
 x_298 = lean::box(0);
}
x_299 = lean::cnstr_get(x_280, 0);
x_301 = lean::cnstr_get(x_280, 1);
x_303 = lean::cnstr_get(x_280, 2);
x_305 = lean::cnstr_get(x_280, 3);
if (lean::is_exclusive(x_280)) {
 x_307 = x_280;
} else {
 lean::inc(x_299);
 lean::inc(x_301);
 lean::inc(x_303);
 lean::inc(x_305);
 lean::dec(x_280);
 x_307 = lean::box(0);
}
lean::inc(x_209);
if (lean::is_scalar(x_307)) {
 x_309 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_309 = x_307;
}
lean::cnstr_set(x_309, 0, x_209);
lean::cnstr_set(x_309, 1, x_294);
lean::cnstr_set(x_309, 2, x_296);
lean::cnstr_set(x_309, 3, x_299);
if (lean::is_exclusive(x_209)) {
 lean::cnstr_release(x_209, 0);
 lean::cnstr_release(x_209, 1);
 lean::cnstr_release(x_209, 2);
 lean::cnstr_release(x_209, 3);
 x_310 = x_209;
} else {
 lean::dec(x_209);
 x_310 = lean::box(0);
}
lean::cnstr_set_scalar(x_309, sizeof(void*)*4, x_256);
x_311 = x_309;
if (lean::is_scalar(x_310)) {
 x_312 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_312 = x_310;
}
lean::cnstr_set(x_312, 0, x_305);
lean::cnstr_set(x_312, 1, x_41);
lean::cnstr_set(x_312, 2, x_43);
lean::cnstr_set(x_312, 3, x_45);
lean::cnstr_set_scalar(x_312, sizeof(void*)*4, x_256);
x_313 = x_312;
if (lean::is_scalar(x_298)) {
 x_314 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_314 = x_298;
}
lean::cnstr_set(x_314, 0, x_311);
lean::cnstr_set(x_314, 1, x_301);
lean::cnstr_set(x_314, 2, x_303);
lean::cnstr_set(x_314, 3, x_313);
lean::cnstr_set_scalar(x_314, sizeof(void*)*4, x_292);
x_315 = x_314;
return x_315;
}
else
{
obj* x_316; obj* x_318; obj* x_320; obj* x_321; obj* x_323; obj* x_325; obj* x_327; obj* x_329; obj* x_330; obj* x_331; uint8 x_332; obj* x_333; obj* x_334; obj* x_335; obj* x_336; 
x_316 = lean::cnstr_get(x_204, 1);
x_318 = lean::cnstr_get(x_204, 2);
if (lean::is_exclusive(x_204)) {
 lean::cnstr_release(x_204, 0);
 lean::cnstr_release(x_204, 3);
 x_320 = x_204;
} else {
 lean::inc(x_316);
 lean::inc(x_318);
 lean::dec(x_204);
 x_320 = lean::box(0);
}
x_321 = lean::cnstr_get(x_209, 0);
x_323 = lean::cnstr_get(x_209, 1);
x_325 = lean::cnstr_get(x_209, 2);
x_327 = lean::cnstr_get(x_209, 3);
if (lean::is_exclusive(x_209)) {
 x_329 = x_209;
} else {
 lean::inc(x_321);
 lean::inc(x_323);
 lean::inc(x_325);
 lean::inc(x_327);
 lean::dec(x_209);
 x_329 = lean::box(0);
}
if (lean::is_scalar(x_329)) {
 x_330 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_330 = x_329;
}
lean::cnstr_set(x_330, 0, x_321);
lean::cnstr_set(x_330, 1, x_323);
lean::cnstr_set(x_330, 2, x_325);
lean::cnstr_set(x_330, 3, x_327);
lean::cnstr_set_scalar(x_330, sizeof(void*)*4, x_292);
x_331 = x_330;
x_332 = 0;
if (lean::is_scalar(x_320)) {
 x_333 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_333 = x_320;
}
lean::cnstr_set(x_333, 0, x_331);
lean::cnstr_set(x_333, 1, x_316);
lean::cnstr_set(x_333, 2, x_318);
lean::cnstr_set(x_333, 3, x_280);
lean::cnstr_set_scalar(x_333, sizeof(void*)*4, x_332);
x_334 = x_333;
if (lean::is_scalar(x_47)) {
 x_335 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_335 = x_47;
}
lean::cnstr_set(x_335, 0, x_334);
lean::cnstr_set(x_335, 1, x_41);
lean::cnstr_set(x_335, 2, x_43);
lean::cnstr_set(x_335, 3, x_45);
lean::cnstr_set_scalar(x_335, sizeof(void*)*4, x_292);
x_336 = x_335;
return x_336;
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
obj* l_RBNode_ins___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_ins___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_ins___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_ins___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBNode_ins(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_ins___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_ins(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_setBlack___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_0;
}
else
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
x_7 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_9 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_0);
 x_9 = lean::box(0);
}
x_10 = 1;
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_3);
lean::cnstr_set(x_11, 2, x_5);
lean::cnstr_set(x_11, 3, x_7);
lean::cnstr_set_scalar(x_11, sizeof(void*)*4, x_10);
x_12 = x_11;
return x_12;
}
}
}
obj* l_RBNode_setBlack___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_setBlack___main___rarg), 1, 0);
return x_2;
}
}
obj* l_RBNode_setBlack___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_setBlack___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_setBlack___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_setBlack___main___rarg(x_0);
return x_1;
}
}
obj* l_RBNode_setBlack(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_setBlack___rarg), 1, 0);
return x_2;
}
}
obj* l_RBNode_setBlack___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_setBlack(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___rarg(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_insert___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_insert(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_findCore___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; 
lean::dec(x_0);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_24; uint8 x_25; 
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_8, x_2);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_29; obj* x_30; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_8);
lean::cnstr_set(x_29, 1, x_10);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
else
{
lean::dec(x_8);
lean::dec(x_10);
x_1 = x_12;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_12);
x_1 = x_6;
goto _start;
}
}
}
}
obj* l_RBNode_findCore___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_findCore___main___rarg), 3, 0);
return x_2;
}
}
obj* l_RBNode_findCore___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_findCore___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_findCore___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBNode_findCore(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_findCore___rarg), 3, 0);
return x_2;
}
}
obj* l_RBNode_findCore___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_findCore(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_find___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 3);
lean::inc(x_13);
lean::dec(x_2);
lean::inc(x_9);
lean::inc(x_3);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_3, x_9);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_24; uint8 x_25; 
lean::dec(x_7);
lean::inc(x_3);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_9, x_3);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_29; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_11);
return x_29;
}
else
{
lean::dec(x_11);
x_1 = lean::box(0);
x_2 = x_13;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_13);
x_1 = lean::box(0);
x_2 = x_7;
goto _start;
}
}
}
}
obj* l_RBNode_find___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_RBNode_find___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_find___main___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_RBNode_find___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_find___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_find___main___rarg(x_0, lean::box(0), x_2, x_3);
return x_4;
}
}
obj* l_RBNode_find(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_RBNode_find___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_find___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_RBNode_find___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_find(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_lowerBound___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_25; uint8 x_26; 
lean::dec(x_3);
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_8, x_2);
x_26 = lean::unbox(x_25);
if (x_26 == 0)
{
obj* x_30; obj* x_31; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_12);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_8);
lean::cnstr_set(x_30, 1, x_10);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_8);
lean::cnstr_set(x_32, 1, x_10);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_1 = x_12;
x_3 = x_33;
goto _start;
}
}
else
{
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_12);
x_1 = x_6;
goto _start;
}
}
}
}
obj* l_RBNode_lowerBound___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_lowerBound___main___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_lowerBound___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_lowerBound___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_lowerBound___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_lowerBound___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBNode_lowerBound(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_lowerBound___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_lowerBound___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_lowerBound(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_mkRBMap(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_mkRBMap___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_mkRBMap(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_empty(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_RBMap_empty___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_empty(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_HasEmptyc(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_RBMap_HasEmptyc___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_HasEmptyc(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_depth___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_depth___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBMap_depth(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_depth___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBMap_depth___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_depth___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_depth___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_depth(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_fold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_fold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_fold___main___rarg), 3, 0);
return x_4;
}
}
obj* l_RBMap_fold___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_fold___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_fold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_fold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_fold___rarg), 3, 0);
return x_4;
}
}
obj* l_RBMap_fold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_fold(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_revFold___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_revFold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_revFold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_revFold___main___rarg), 3, 0);
return x_4;
}
}
obj* l_RBMap_revFold___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_revFold___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_revFold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_revFold___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_revFold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_revFold___rarg), 3, 0);
return x_4;
}
}
obj* l_RBMap_revFold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBMap_revFold(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_mfold___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_mfold___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_mfold___main___rarg), 4, 0);
return x_5;
}
}
obj* l_RBMap_mfold___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBMap_mfold___main(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_RBMap_mfold___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_mfold(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_mfold___rarg), 4, 0);
return x_5;
}
}
obj* l_RBMap_mfold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBMap_mfold(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(x_0, x_1, x_3, x_2);
return x_4;
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 4);
lean::inc(x_9);
lean::inc(x_1);
x_12 = lean::apply_2(x_1, x_2, x_3);
x_13 = lean::cnstr_get(x_7, 1);
lean::inc(x_13);
lean::dec(x_7);
x_16 = lean::box(0);
x_17 = lean::apply_2(x_13, lean::box(0), x_16);
x_18 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_12, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__1), 4, 3);
lean::closure_set(x_19, 0, x_0);
lean::closure_set(x_19, 1, x_1);
lean::closure_set(x_19, 2, x_4);
x_20 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_18, x_19);
return x_20;
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_25; obj* x_27; obj* x_28; 
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_3, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_3, 2);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_3, 3);
lean::inc(x_18);
lean::dec(x_3);
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::inc(x_1);
lean::inc(x_0);
x_25 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(x_0, x_1, x_2, x_12);
lean::inc(x_21);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2___boxed), 7, 6);
lean::closure_set(x_27, 0, x_0);
lean::closure_set(x_27, 1, x_1);
lean::closure_set(x_27, 2, x_14);
lean::closure_set(x_27, 3, x_16);
lean::closure_set(x_27, 4, x_18);
lean::closure_set(x_27, 5, x_21);
x_28 = lean::apply_4(x_21, lean::box(0), lean::box(0), x_25, x_27);
return x_28;
}
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg), 4, 0);
return x_4;
}
}
obj* l_RBMap_mfor___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(x_0, x_1, x_3, x_2);
return x_4;
}
}
obj* l_RBMap_mfor(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_mfor___rarg), 3, 0);
return x_5;
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_6);
return x_7;
}
}
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBMap_mfor___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_RBMap_mfor(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
uint8 l_RBMap_isEmpty___main___rarg(obj* x_0) {
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
obj* l_RBMap_isEmpty___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_isEmpty___main___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_RBMap_isEmpty___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_RBMap_isEmpty___main___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBMap_isEmpty___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_isEmpty___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBMap_isEmpty___rarg(obj* x_0) {
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
obj* l_RBMap_isEmpty(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_isEmpty___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_RBMap_isEmpty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_RBMap_isEmpty___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBMap_isEmpty___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_isEmpty(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
lean::dec(x_1);
x_11 = l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___rarg(x_0, x_8);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_6);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_0 = x_13;
x_1 = x_2;
goto _start;
}
}
}
obj* l_RBNode_revFold___main___at_RBMap_toList___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_RBMap_toList___main___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___rarg(x_1, x_0);
return x_2;
}
}
obj* l_RBMap_toList___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_toList___main___rarg), 1, 0);
return x_3;
}
}
obj* l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_revFold___main___at_RBMap_toList___main___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_toList___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_toList___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_toList___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBMap_toList___main___rarg(x_0);
return x_1;
}
}
obj* l_RBMap_toList(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_toList___rarg), 1, 0);
return x_3;
}
}
obj* l_RBMap_toList___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_toList(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_min___main___rarg(obj* x_0) {
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
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12; 
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
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_RBMap_min___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_min___main___rarg), 1, 0);
return x_3;
}
}
obj* l_RBMap_min___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_min___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_min___rarg(obj* x_0) {
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
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12; 
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
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_RBMap_min(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_min___rarg), 1, 0);
return x_3;
}
}
obj* l_RBMap_min___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_min(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_max___main___rarg(obj* x_0) {
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
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12; 
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
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_RBMap_max___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_max___main___rarg), 1, 0);
return x_3;
}
}
obj* l_RBMap_max___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_max___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_max___rarg(obj* x_0) {
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
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_11; obj* x_12; 
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
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_6);
lean::cnstr_set(x_11, 1, x_8);
if (lean::is_scalar(x_5)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_5;
}
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* l_RBMap_max(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_max___rarg), 1, 0);
return x_3;
}
}
obj* l_RBMap_max___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_max(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(obj* x_0, obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
if (x_2 == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_String_splitAux___main___closed__1;
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_33; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
lean::dec(x_3);
lean::inc(x_1);
lean::inc(x_0);
x_14 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_0, x_1, x_2, x_9);
x_15 = lean::cnstr_get(x_7, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_7, 1);
lean::inc(x_17);
lean::dec(x_7);
x_20 = lean::apply_1(x_0, x_15);
x_21 = l_Prod_HasRepr___rarg___closed__1;
x_22 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_24 = l_List_reprAux___main___rarg___closed__1;
x_25 = lean::string_append(x_22, x_24);
x_26 = lean::apply_1(x_1, x_17);
x_27 = lean::string_append(x_25, x_26);
lean::dec(x_26);
x_29 = l_Option_HasRepr___rarg___closed__3;
x_30 = lean::string_append(x_27, x_29);
x_31 = lean::string_append(x_24, x_30);
lean::dec(x_30);
x_33 = lean::string_append(x_31, x_14);
lean::dec(x_14);
return x_33;
}
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_37; 
lean::dec(x_1);
lean::dec(x_0);
x_37 = l_String_splitAux___main___closed__1;
return x_37;
}
else
{
obj* x_38; obj* x_40; uint8 x_43; obj* x_46; obj* x_47; obj* x_49; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
x_38 = lean::cnstr_get(x_3, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_3, 1);
lean::inc(x_40);
lean::dec(x_3);
x_43 = 0;
lean::inc(x_1);
lean::inc(x_0);
x_46 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_0, x_1, x_43, x_40);
x_47 = lean::cnstr_get(x_38, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_38, 1);
lean::inc(x_49);
lean::dec(x_38);
x_52 = lean::apply_1(x_0, x_47);
x_53 = l_Prod_HasRepr___rarg___closed__1;
x_54 = lean::string_append(x_53, x_52);
lean::dec(x_52);
x_56 = l_List_reprAux___main___rarg___closed__1;
x_57 = lean::string_append(x_54, x_56);
x_58 = lean::apply_1(x_1, x_49);
x_59 = lean::string_append(x_57, x_58);
lean::dec(x_58);
x_61 = l_Option_HasRepr___rarg___closed__3;
x_62 = lean::string_append(x_59, x_61);
x_63 = lean::string_append(x_62, x_46);
lean::dec(x_46);
return x_63;
}
}
}
}
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_List_repr___main___at_RBMap_HasRepr___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_List_repr___main___rarg___closed__1;
return x_5;
}
else
{
uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
x_6 = 1;
x_7 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_0, x_1, x_6, x_2);
x_8 = l_List_repr___main___rarg___closed__2;
x_9 = lean::string_append(x_8, x_7);
lean::dec(x_7);
x_11 = l_List_repr___main___rarg___closed__3;
x_12 = lean::string_append(x_9, x_11);
return x_12;
}
}
}
obj* l_List_repr___main___at_RBMap_HasRepr___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_repr___main___at_RBMap_HasRepr___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* _init_l_RBMap_HasRepr___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("rbmapOf ");
return x_0;
}
}
obj* l_RBMap_HasRepr___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_RBMap_toList___main___rarg(x_2);
x_4 = l_List_repr___main___at_RBMap_HasRepr___spec__1___rarg(x_0, x_1, x_3);
x_5 = l_RBMap_HasRepr___rarg___closed__1;
x_6 = lean::string_append(x_5, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l_RBMap_HasRepr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_HasRepr___rarg), 3, 0);
return x_3;
}
}
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_0, x_1, x_4, x_3);
return x_5;
}
}
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_repr___main___at_RBMap_HasRepr___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_repr___main___at_RBMap_HasRepr___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_HasRepr___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_HasRepr(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBMap_insert___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___rarg(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBMap_insert___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_insert___main___rarg), 4, 0);
return x_2;
}
}
obj* l_RBMap_insert___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_insert___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___rarg(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBMap_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_insert___rarg), 4, 0);
return x_2;
}
}
obj* l_RBMap_insert___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_insert(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_ofList___main___rarg(obj* x_0, obj* x_1) {
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
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15; uint8 x_16; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
lean::inc(x_0);
x_15 = l_RBMap_ofList___main___rarg(x_0, x_6);
x_16 = l_RBNode_isRed___main___rarg(x_15);
if (x_16 == 0)
{
obj* x_17; 
x_17 = l_RBNode_ins___main___rarg(x_0, x_15, x_9, x_11);
return x_17;
}
else
{
obj* x_18; obj* x_19; 
x_18 = l_RBNode_ins___main___rarg(x_0, x_15, x_9, x_11);
x_19 = l_RBNode_setBlack___main___rarg(x_18);
return x_19;
}
}
}
}
obj* l_RBMap_ofList___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_ofList___main___rarg), 2, 0);
return x_2;
}
}
obj* l_RBMap_ofList___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_ofList___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_ofList___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_ofList___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBMap_ofList(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_ofList___rarg), 2, 0);
return x_2;
}
}
obj* l_RBMap_ofList___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_ofList(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_findCore___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_findCore___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_findCore___main___rarg), 3, 0);
return x_2;
}
}
obj* l_RBMap_findCore___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_findCore___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_findCore___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_findCore(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_findCore___rarg), 3, 0);
return x_2;
}
}
obj* l_RBMap_findCore___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_findCore(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_find___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_RBMap_find___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_find___main___rarg), 3, 0);
return x_2;
}
}
obj* l_RBMap_find___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_find___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_find___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___rarg(x_0, lean::box(0), x_1, x_2);
return x_3;
}
}
obj* l_RBMap_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_find___rarg), 3, 0);
return x_2;
}
}
obj* l_RBMap_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_lowerBound___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_RBNode_lowerBound___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_lowerBound___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_lowerBound___main___rarg), 3, 0);
return x_2;
}
}
obj* l_RBMap_lowerBound___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_lowerBound___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_lowerBound___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_RBNode_lowerBound___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_lowerBound(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_lowerBound___rarg), 3, 0);
return x_2;
}
}
obj* l_RBMap_lowerBound___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_lowerBound(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBMap_contains___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___rarg(x_0, lean::box(0), x_1, x_2);
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
obj* l_RBMap_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_contains___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBMap_contains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBMap_contains___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBMap_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_contains(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_foldl___main___at_RBMap_fromList___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; uint8 x_14; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
x_14 = l_RBNode_isRed___main___rarg(x_1);
if (x_14 == 0)
{
obj* x_16; 
lean::inc(x_0);
x_16 = l_RBNode_ins___main___rarg(x_0, x_1, x_9, x_11);
x_1 = x_16;
x_2 = x_6;
goto _start;
}
else
{
obj* x_19; obj* x_20; 
lean::inc(x_0);
x_19 = l_RBNode_ins___main___rarg(x_0, x_1, x_9, x_11);
x_20 = l_RBNode_setBlack___main___rarg(x_19);
x_1 = x_20;
x_2 = x_6;
goto _start;
}
}
}
}
obj* l_List_foldl___main___at_RBMap_fromList___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_RBMap_fromList___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_RBMap_fromList___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_List_foldl___main___at_RBMap_fromList___spec__1___rarg(x_1, x_2, x_0);
return x_3;
}
}
obj* l_RBMap_fromList(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_fromList___rarg), 2, 0);
return x_2;
}
}
obj* l_List_foldl___main___at_RBMap_fromList___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldl___main___at_RBMap_fromList___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_fromList___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_fromList(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBMap_all___main___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_RBNode_all___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_RBMap_all___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_all___main___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBMap_all___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBMap_all___main___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBMap_all___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_all___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBMap_all___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_RBNode_all___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_RBMap_all(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_all___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBMap_all___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBMap_all___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBMap_all___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_all(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBMap_any___main___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_RBNode_any___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_RBMap_any___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_any___main___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBMap_any___main___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBMap_any___main___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBMap_any___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_any___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_RBMap_any___rarg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_RBNode_any___main___rarg(x_1, x_0);
return x_2;
}
}
obj* l_RBMap_any(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_any___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_RBMap_any___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_RBMap_any___rarg(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_RBMap_any___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_any(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_List_foldl___main___at_rbmapOf___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; uint8 x_14; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
x_14 = l_RBNode_isRed___main___rarg(x_1);
if (x_14 == 0)
{
obj* x_16; 
lean::inc(x_0);
x_16 = l_RBNode_ins___main___rarg(x_0, x_1, x_9, x_11);
x_1 = x_16;
x_2 = x_6;
goto _start;
}
else
{
obj* x_19; obj* x_20; 
lean::inc(x_0);
x_19 = l_RBNode_ins___main___rarg(x_0, x_1, x_9, x_11);
x_20 = l_RBNode_setBlack___main___rarg(x_19);
x_1 = x_20;
x_2 = x_6;
goto _start;
}
}
}
}
obj* l_List_foldl___main___at_rbmapOf___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_rbmapOf___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_rbmapOf___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_List_foldl___main___at_rbmapOf___spec__1___rarg(x_1, x_2, x_0);
return x_3;
}
}
obj* l_rbmapOf(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmapOf___rarg), 2, 0);
return x_2;
}
}
obj* l_List_foldl___main___at_rbmapOf___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldl___main___at_rbmapOf___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmapOf___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmapOf(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_data_repr(obj*);
obj* initialize_init_data_option_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_rbmap_basic(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_repr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (io_result_is_error(w)) return w;
 l_RBMap_HasRepr___rarg___closed__1 = _init_l_RBMap_HasRepr___rarg___closed__1();
lean::mark_persistent(l_RBMap_HasRepr___rarg___closed__1);
return w;
}
