// Lean compiler output
// Module: Init.Data.RBMap.Basic
// Imports: Init.Data.Repr Init.Data.Option.Basic
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
lean_object* l_RBMap_erase___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_maxDepth___rarg___boxed(lean_object*);
uint8_t l_RBMap_all___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_revFold___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_RBNode_isRed___rarg(lean_object*);
lean_object* l_RBMap_fromList___rarg(lean_object*, lean_object*);
lean_object* l_RBMap_HasRepr___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_contains___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_del(lean_object*, lean_object*);
lean_object* l_RBMap_maxDepth___rarg___closed__1;
lean_object* l_RBMap_toList___rarg(lean_object*);
lean_object* l_RBNode_erase___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_find(lean_object*);
lean_object* l_RBMap_insert(lean_object*, lean_object*);
lean_object* l_RBNode_fold___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_balance2___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_setRed___rarg(lean_object*);
lean_object* l_rbmapOf___rarg(lean_object*, lean_object*);
lean_object* l_RBMap_min___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_RBNode_min___rarg___boxed(lean_object*);
lean_object* l_RBNode_appendTrees___main___boxed(lean_object*, lean_object*);
lean_object* l_RBMap_lowerBound(lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___at_RBMap_mfor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_del___main___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_any___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_max___main___rarg___boxed(lean_object*);
lean_object* l_RBNode_ins___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_RBNode_appendTrees(lean_object*, lean_object*);
lean_object* l_RBNode_mfold(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_any___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_setBlack___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_insert___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_setBlack(lean_object*, lean_object*);
lean_object* l_RBNode_lowerBound___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_RBMap_any___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_findCore___main___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_min___main___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___at_RBMap_size___spec__1(lean_object*, lean_object*);
lean_object* l_RBNode_fold___main(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_lowerBound___main___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_RBNode_revFold___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_findD(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_RBMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_ofList___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_balance_u2083___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_ins___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_contains(lean_object*, lean_object*);
lean_object* l_RBNode_insert(lean_object*, lean_object*);
lean_object* l_RBMap_find(lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkRBMap___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_RBNode_revFold___main(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_findCore___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_lowerBound___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_mfold___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_depth___main(lean_object*, lean_object*);
lean_object* l_RBNode_del___main(lean_object*, lean_object*);
lean_object* l_List_repr___at_RBMap_HasRepr___spec__1(lean_object*, lean_object*);
lean_object* l_RBNode_all___main___boxed(lean_object*, lean_object*);
lean_object* l_RBMap_findCore(lean_object*, lean_object*);
lean_object* l_RBNode_all___boxed(lean_object*, lean_object*);
lean_object* l_RBMap_size(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_isRed___rarg___boxed(lean_object*);
lean_object* l_RBNode_mfold___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_appendTrees___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_max___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_findCore___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_all(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_findD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_depth___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_lowerBound___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_find___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_singleton(lean_object*, lean_object*);
lean_object* l_RBMap_max___rarg(lean_object*);
lean_object* l_RBNode_del___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_revFold___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_balance1___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_min___main(lean_object*, lean_object*);
lean_object* l_RBMap_all___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_fold(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_HasRepr___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_isBlack___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_balLeft___boxed(lean_object*, lean_object*);
lean_object* l_RBMap_all___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_RBNode_all___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_revFold___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_any___main(lean_object*, lean_object*);
lean_object* l_RBMap_mfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_toList___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_depth___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_isEmpty___rarg___boxed(lean_object*);
lean_object* l_RBMap_HasEmptyc(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_HasEmptyc___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_RBNode_isRed___boxed(lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_RBMap_max(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_max___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_mfor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_size___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_depth___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_erase___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_revFold(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_appendTrees___main(lean_object*, lean_object*);
lean_object* l_RBNode_min___main___rarg(lean_object*);
lean_object* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_mfold___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_mfor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_rbmapOf___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_lowerBound___boxed(lean_object*, lean_object*);
uint8_t l_RBNode_any___main___rarg(lean_object*, lean_object*);
lean_object* l_RBMap_max___rarg___boxed(lean_object*);
lean_object* l_RBMap_fromList(lean_object*, lean_object*);
lean_object* l_RBNode_singleton___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_findCore___main(lean_object*, lean_object*);
lean_object* l_rbmapOf(lean_object*, lean_object*);
lean_object* l_RBMap_fold(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_isEmpty(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_RBMap_min___rarg(lean_object*);
lean_object* l_RBNode_balance1(lean_object*, lean_object*);
lean_object* l_RBMap_ofList(lean_object*, lean_object*);
lean_object* l_RBMap_toList(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_balance_u2083(lean_object*, lean_object*);
lean_object* l_RBNode_isBlack___rarg___boxed(lean_object*);
lean_object* l_RBNode_lowerBound(lean_object*, lean_object*);
lean_object* l_RBNode_any___main___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBMap_any(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_min___main___rarg___boxed(lean_object*);
lean_object* l_RBNode_setRed(lean_object*, lean_object*);
lean_object* l_RBNode_findCore___boxed(lean_object*, lean_object*);
lean_object* l_RBMap_maxDepth(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_del___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_mfor___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_RBNode_depth___main___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_max(lean_object*, lean_object*);
lean_object* l_RBMap_depth(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_all___main(lean_object*, lean_object*);
lean_object* l_RBNode_depth___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_all___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_depth___main___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBMap_maxDepth___rarg(lean_object*);
lean_object* l_RBNode_max___main(lean_object*, lean_object*);
lean_object* l_RBNode_del___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_balance2(lean_object*, lean_object*);
lean_object* l_RBMap_erase(lean_object*, lean_object*);
lean_object* l_RBNode_find___main(lean_object*);
lean_object* l_RBMap_min(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_min___rarg(lean_object*);
lean_object* l_RBNode_find___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_appendTrees___main___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_max___main___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_ins(lean_object*, lean_object*);
lean_object* l_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_balLeft(lean_object*, lean_object*);
lean_object* l_RBMap_depth___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_any(lean_object*, lean_object*);
lean_object* l_RBMap_size___rarg___boxed(lean_object*);
lean_object* l_RBNode_mfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_empty___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_balRight___boxed(lean_object*, lean_object*);
lean_object* l_mkRBMap(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_depth___main___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_max___main___rarg(lean_object*);
uint8_t l_RBNode_any___rarg(lean_object*, lean_object*);
lean_object* l_RBMap_findD___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_min___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_setBlack___rarg(lean_object*);
lean_object* l_RBNode_balance1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_max___boxed(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_RBMap_fromList___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_revFold___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_isRed(lean_object*, lean_object*);
lean_object* l_RBMap_fold___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_all___main___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBMap_ofList___main___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_revFold(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_isBlack(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_RBMap_fromList___spec__1(lean_object*, lean_object*);
lean_object* l_RBNode_min(lean_object*, lean_object*);
lean_object* l_RBNode_find___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_findCore___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_HasRepr___rarg___closed__1;
lean_object* l_RBNode_fold___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_RBNode_all___main___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_balance_u2083___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_balRight(lean_object*, lean_object*);
lean_object* l_RBNode_depth(lean_object*, lean_object*);
lean_object* l_RBMap_maxDepth___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_ins___boxed(lean_object*, lean_object*);
lean_object* l_RBMap_empty(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_erase(lean_object*, lean_object*);
lean_object* l_RBNode_any___boxed(lean_object*, lean_object*);
lean_object* l_RBMap_HasRepr(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_appendTrees___boxed(lean_object*, lean_object*);
lean_object* l_RBMap_revFold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___at_RBMap_HasRepr___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_toList___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_any___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_any___main___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_depth___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_balance2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_max___rarg(lean_object*);
uint8_t l_RBMap_isEmpty___rarg(lean_object*);
lean_object* l_RBMap_toList___rarg___closed__1;
lean_object* l_RBNode_ins___main___boxed(lean_object*, lean_object*);
lean_object* l_RBMap_min___rarg___boxed(lean_object*);
lean_object* l_RBNode_setRed___boxed(lean_object*, lean_object*);
lean_object* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_RBMap_mfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_size___rarg(lean_object*);
lean_object* l_RBNode_all(lean_object*, lean_object*);
lean_object* l_RBNode_max___rarg___boxed(lean_object*);
lean_object* l_List_foldl___main___at_rbmapOf___spec__1(lean_object*, lean_object*);
uint8_t l_RBNode_isBlack___rarg(lean_object*);
uint8_t l_RBMap_contains___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reprAux___main___at_RBMap_HasRepr___spec__2(lean_object*, lean_object*);
lean_object* l_RBMap_ofList___main(lean_object*, lean_object*);
lean_object* l_RBNode_lowerBound___main(lean_object*, lean_object*);
lean_object* l_RBNode_findCore(lean_object*, lean_object*);
lean_object* l_RBNode_singleton___rarg(lean_object*, lean_object*);
lean_object* l_RBNode_ins___main(lean_object*, lean_object*);
lean_object* l_RBNode_mfold___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBMap_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_depth___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
x_6 = l_RBNode_depth___main___rarg(x_1, x_4);
lean_inc(x_1);
x_7 = l_RBNode_depth___main___rarg(x_1, x_5);
x_8 = lean_apply_2(x_1, x_6, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
}
lean_object* l_RBNode_depth___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_depth___main___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_RBNode_depth___main___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_depth___main___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_depth___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_depth___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_depth___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_depth___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_RBNode_depth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_depth___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_RBNode_depth___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_depth___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_depth___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_depth(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_min___main___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
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
lean_object* l_RBNode_min___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_min___main___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_RBNode_min___main___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBNode_min___main___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_RBNode_min___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_min___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_min___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBNode_min___main___rarg(x_1);
return x_2;
}
}
lean_object* l_RBNode_min(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_min___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_RBNode_min___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBNode_min___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_RBNode_min___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_min(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_max___main___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
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
lean_object* l_RBNode_max___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_max___main___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_RBNode_max___main___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBNode_max___main___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_RBNode_max___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_max___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_max___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBNode_max___main___rarg(x_1);
return x_2;
}
}
lean_object* l_RBNode_max(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_max___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_RBNode_max___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBNode_max___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_RBNode_max___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_max(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_fold___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_1);
x_8 = l_RBNode_fold___main___rarg(x_1, x_2, x_4);
lean_inc(x_1);
x_9 = lean_apply_3(x_1, x_8, x_5, x_6);
x_2 = x_9;
x_3 = x_7;
goto _start;
}
}
}
lean_object* l_RBNode_fold___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBNode_fold___main___rarg), 3, 0);
return x_4;
}
}
lean_object* l_RBNode_fold___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_fold___main(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_RBNode_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_fold___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_RBNode_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBNode_fold___rarg), 3, 0);
return x_4;
}
}
lean_object* l_RBNode_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_fold(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_RBNode_mfold___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_mfold___main___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_RBNode_mfold___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_8 = lean_apply_3(x_1, x_7, x_2, x_3);
x_9 = lean_alloc_closure((void*)(l_RBNode_mfold___main___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_RBNode_mfold___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_RBNode_mfold___main___rarg(x_1, x_2, x_3, x_8);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_RBNode_mfold___main___rarg___lambda__2), 7, 6);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_10);
lean_closure_set(x_14, 3, x_1);
lean_closure_set(x_14, 4, x_11);
lean_closure_set(x_14, 5, x_12);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
lean_object* l_RBNode_mfold___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_RBNode_mfold___main___rarg), 4, 0);
return x_5;
}
}
lean_object* l_RBNode_mfold___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_mfold___main(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_RBNode_mfold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_mfold___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_RBNode_mfold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_RBNode_mfold___rarg), 4, 0);
return x_5;
}
}
lean_object* l_RBNode_mfold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_mfold(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_RBNode_revFold___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_1);
x_8 = l_RBNode_revFold___main___rarg(x_1, x_2, x_7);
lean_inc(x_1);
x_9 = lean_apply_3(x_1, x_8, x_5, x_6);
x_2 = x_9;
x_3 = x_4;
goto _start;
}
}
}
lean_object* l_RBNode_revFold___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBNode_revFold___main___rarg), 3, 0);
return x_4;
}
}
lean_object* l_RBNode_revFold___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_revFold___main(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_RBNode_revFold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_revFold___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_RBNode_revFold(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBNode_revFold___rarg), 3, 0);
return x_4;
}
}
lean_object* l_RBNode_revFold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_revFold(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l_RBNode_all___main___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_6);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
lean_inc(x_1);
x_11 = l_RBNode_all___main___rarg(x_1, x_4);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_1);
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
lean_object* l_RBNode_all___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_all___main___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_RBNode_all___main___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_RBNode_all___main___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_RBNode_all___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_all___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_RBNode_all___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_RBNode_all___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_RBNode_all(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_all___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_RBNode_all___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_RBNode_all___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_RBNode_all___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_all(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_RBNode_any___main___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_6);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_inc(x_1);
x_10 = l_RBNode_any___main___rarg(x_1, x_4);
if (x_10 == 0)
{
x_2 = x_7;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_13 = 1;
return x_13;
}
}
}
}
lean_object* l_RBNode_any___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_any___main___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_RBNode_any___main___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_RBNode_any___main___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_RBNode_any___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_any___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_RBNode_any___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_RBNode_any___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_RBNode_any(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_any___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_RBNode_any___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_RBNode_any___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_RBNode_any___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_any(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_singleton___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = 0;
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
}
lean_object* l_RBNode_singleton(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_singleton___rarg), 2, 0);
return x_3;
}
}
lean_object* l_RBNode_singleton___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_singleton(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_balance1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_4, 3);
lean_dec(x_8);
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = 0;
lean_ctor_set(x_4, 0, x_6);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_10);
x_11 = 1;
x_12 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 2, x_2);
lean_ctor_set(x_12, 3, x_3);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = 0;
x_16 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_6);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_15);
x_17 = 1;
x_18 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_18, 2, x_2);
lean_ctor_set(x_18, 3, x_3);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_6, sizeof(void*)*4);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_4, 2);
x_23 = lean_ctor_get(x_4, 3);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
x_28 = lean_ctor_get(x_6, 2);
x_29 = lean_ctor_get(x_6, 3);
x_30 = 1;
lean_ctor_set(x_6, 3, x_26);
lean_ctor_set(x_6, 2, x_22);
lean_ctor_set(x_6, 1, x_21);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_30);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 0, x_29);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_30);
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_4);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_19);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
x_34 = lean_ctor_get(x_6, 2);
x_35 = lean_ctor_get(x_6, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_36 = 1;
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_21);
lean_ctor_set(x_37, 2, x_22);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_36);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 0, x_35);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_36);
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_4);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_19);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_4, 1);
x_40 = lean_ctor_get(x_4, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_4);
x_41 = lean_ctor_get(x_6, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_6, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_6, 3);
lean_inc(x_44);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 x_45 = x_6;
} else {
 lean_dec_ref(x_6);
 x_45 = lean_box(0);
}
x_46 = 1;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(1, 4, 1);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_39);
lean_ctor_set(x_47, 2, x_40);
lean_ctor_set(x_47, 3, x_41);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_46);
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_1);
lean_ctor_set(x_48, 2, x_2);
lean_ctor_set(x_48, 3, x_3);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_46);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_19);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_4);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_4, 3);
lean_dec(x_51);
x_52 = lean_ctor_get(x_4, 0);
lean_dec(x_52);
x_53 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_53);
x_54 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_54, 0, x_4);
lean_ctor_set(x_54, 1, x_1);
lean_ctor_set(x_54, 2, x_2);
lean_ctor_set(x_54, 3, x_3);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_19);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_4, 1);
x_56 = lean_ctor_get(x_4, 2);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_4);
x_57 = 0;
x_58 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_58, 0, x_5);
lean_ctor_set(x_58, 1, x_55);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_6);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_57);
x_59 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_1);
lean_ctor_set(x_59, 2, x_2);
lean_ctor_set(x_59, 3, x_3);
lean_ctor_set_uint8(x_59, sizeof(void*)*4, x_19);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_5, sizeof(void*)*4);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_4);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_4, 1);
x_63 = lean_ctor_get(x_4, 2);
x_64 = lean_ctor_get(x_4, 3);
x_65 = lean_ctor_get(x_4, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_5);
if (x_66 == 0)
{
uint8_t x_67; lean_object* x_68; 
x_67 = 1;
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_67);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 0, x_64);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_67);
x_68 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_68, 0, x_5);
lean_ctor_set(x_68, 1, x_62);
lean_ctor_set(x_68, 2, x_63);
lean_ctor_set(x_68, 3, x_4);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_60);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_5, 0);
x_70 = lean_ctor_get(x_5, 1);
x_71 = lean_ctor_get(x_5, 2);
x_72 = lean_ctor_get(x_5, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_5);
x_73 = 1;
x_74 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set(x_74, 2, x_71);
lean_ctor_set(x_74, 3, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*4, x_73);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 0, x_64);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_73);
x_75 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_62);
lean_ctor_set(x_75, 2, x_63);
lean_ctor_set(x_75, 3, x_4);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_60);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_76 = lean_ctor_get(x_4, 1);
x_77 = lean_ctor_get(x_4, 2);
x_78 = lean_ctor_get(x_4, 3);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_4);
x_79 = lean_ctor_get(x_5, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_5, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_5, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_5, 3);
lean_inc(x_82);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_83 = x_5;
} else {
 lean_dec_ref(x_5);
 x_83 = lean_box(0);
}
x_84 = 1;
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(1, 4, 1);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_80);
lean_ctor_set(x_85, 2, x_81);
lean_ctor_set(x_85, 3, x_82);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_84);
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_78);
lean_ctor_set(x_86, 1, x_1);
lean_ctor_set(x_86, 2, x_2);
lean_ctor_set(x_86, 3, x_3);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_84);
x_87 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_76);
lean_ctor_set(x_87, 2, x_77);
lean_ctor_set(x_87, 3, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*4, x_60);
return x_87;
}
}
else
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_4, 3);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_4);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_4, 3);
lean_dec(x_90);
x_91 = lean_ctor_get(x_4, 0);
lean_dec(x_91);
x_92 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_92);
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_4);
lean_ctor_set(x_93, 1, x_1);
lean_ctor_set(x_93, 2, x_2);
lean_ctor_set(x_93, 3, x_3);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_60);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_4, 1);
x_95 = lean_ctor_get(x_4, 2);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_4);
x_96 = 0;
x_97 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_97, 0, x_5);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_88);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_96);
x_98 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_1);
lean_ctor_set(x_98, 2, x_2);
lean_ctor_set(x_98, 3, x_3);
lean_ctor_set_uint8(x_98, sizeof(void*)*4, x_60);
return x_98;
}
}
else
{
uint8_t x_99; 
x_99 = lean_ctor_get_uint8(x_88, sizeof(void*)*4);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_4);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_101 = lean_ctor_get(x_4, 1);
x_102 = lean_ctor_get(x_4, 2);
x_103 = lean_ctor_get(x_4, 3);
lean_dec(x_103);
x_104 = lean_ctor_get(x_4, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_88);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_106 = lean_ctor_get(x_88, 0);
x_107 = lean_ctor_get(x_88, 1);
x_108 = lean_ctor_get(x_88, 2);
x_109 = lean_ctor_get(x_88, 3);
lean_inc(x_5);
lean_ctor_set(x_88, 3, x_106);
lean_ctor_set(x_88, 2, x_102);
lean_ctor_set(x_88, 1, x_101);
lean_ctor_set(x_88, 0, x_5);
x_110 = !lean_is_exclusive(x_5);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_5, 3);
lean_dec(x_111);
x_112 = lean_ctor_get(x_5, 2);
lean_dec(x_112);
x_113 = lean_ctor_get(x_5, 1);
lean_dec(x_113);
x_114 = lean_ctor_get(x_5, 0);
lean_dec(x_114);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_60);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 0, x_109);
lean_ctor_set(x_4, 3, x_5);
lean_ctor_set(x_4, 2, x_108);
lean_ctor_set(x_4, 1, x_107);
lean_ctor_set(x_4, 0, x_88);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_99);
return x_4;
}
else
{
lean_object* x_115; 
lean_dec(x_5);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_60);
x_115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_1);
lean_ctor_set(x_115, 2, x_2);
lean_ctor_set(x_115, 3, x_3);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_60);
lean_ctor_set(x_4, 3, x_115);
lean_ctor_set(x_4, 2, x_108);
lean_ctor_set(x_4, 1, x_107);
lean_ctor_set(x_4, 0, x_88);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_99);
return x_4;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_88, 0);
x_117 = lean_ctor_get(x_88, 1);
x_118 = lean_ctor_get(x_88, 2);
x_119 = lean_ctor_get(x_88, 3);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_88);
lean_inc(x_5);
x_120 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_120, 0, x_5);
lean_ctor_set(x_120, 1, x_101);
lean_ctor_set(x_120, 2, x_102);
lean_ctor_set(x_120, 3, x_116);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_121 = x_5;
} else {
 lean_dec_ref(x_5);
 x_121 = lean_box(0);
}
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_60);
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 4, 1);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_1);
lean_ctor_set(x_122, 2, x_2);
lean_ctor_set(x_122, 3, x_3);
lean_ctor_set_uint8(x_122, sizeof(void*)*4, x_60);
lean_ctor_set(x_4, 3, x_122);
lean_ctor_set(x_4, 2, x_118);
lean_ctor_set(x_4, 1, x_117);
lean_ctor_set(x_4, 0, x_120);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_99);
return x_4;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_123 = lean_ctor_get(x_4, 1);
x_124 = lean_ctor_get(x_4, 2);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_4);
x_125 = lean_ctor_get(x_88, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_88, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_88, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_88, 3);
lean_inc(x_128);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 x_129 = x_88;
} else {
 lean_dec_ref(x_88);
 x_129 = lean_box(0);
}
lean_inc(x_5);
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 4, 1);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_5);
lean_ctor_set(x_130, 1, x_123);
lean_ctor_set(x_130, 2, x_124);
lean_ctor_set(x_130, 3, x_125);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_131 = x_5;
} else {
 lean_dec_ref(x_5);
 x_131 = lean_box(0);
}
lean_ctor_set_uint8(x_130, sizeof(void*)*4, x_60);
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 4, 1);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_1);
lean_ctor_set(x_132, 2, x_2);
lean_ctor_set(x_132, 3, x_3);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_60);
x_133 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_126);
lean_ctor_set(x_133, 2, x_127);
lean_ctor_set(x_133, 3, x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*4, x_99);
return x_133;
}
}
else
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_4);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_4, 3);
lean_dec(x_135);
x_136 = lean_ctor_get(x_4, 0);
lean_dec(x_136);
x_137 = !lean_is_exclusive(x_5);
if (x_137 == 0)
{
uint8_t x_138; lean_object* x_139; 
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_99);
x_138 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_138);
x_139 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_139, 0, x_4);
lean_ctor_set(x_139, 1, x_1);
lean_ctor_set(x_139, 2, x_2);
lean_ctor_set(x_139, 3, x_3);
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_99);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; 
x_140 = lean_ctor_get(x_5, 0);
x_141 = lean_ctor_get(x_5, 1);
x_142 = lean_ctor_get(x_5, 2);
x_143 = lean_ctor_get(x_5, 3);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_5);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_141);
lean_ctor_set(x_144, 2, x_142);
lean_ctor_set(x_144, 3, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_99);
x_145 = 0;
lean_ctor_set(x_4, 0, x_144);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_145);
x_146 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_146, 0, x_4);
lean_ctor_set(x_146, 1, x_1);
lean_ctor_set(x_146, 2, x_2);
lean_ctor_set(x_146, 3, x_3);
lean_ctor_set_uint8(x_146, sizeof(void*)*4, x_99);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; 
x_147 = lean_ctor_get(x_4, 1);
x_148 = lean_ctor_get(x_4, 2);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_4);
x_149 = lean_ctor_get(x_5, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_5, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_5, 2);
lean_inc(x_151);
x_152 = lean_ctor_get(x_5, 3);
lean_inc(x_152);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_153 = x_5;
} else {
 lean_dec_ref(x_5);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 4, 1);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_149);
lean_ctor_set(x_154, 1, x_150);
lean_ctor_set(x_154, 2, x_151);
lean_ctor_set(x_154, 3, x_152);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_99);
x_155 = 0;
x_156 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_147);
lean_ctor_set(x_156, 2, x_148);
lean_ctor_set(x_156, 3, x_88);
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_155);
x_157 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_1);
lean_ctor_set(x_157, 2, x_2);
lean_ctor_set(x_157, 3, x_3);
lean_ctor_set_uint8(x_157, sizeof(void*)*4, x_99);
return x_157;
}
}
}
}
}
}
}
}
lean_object* l_RBNode_balance1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_balance1___rarg), 4, 0);
return x_3;
}
}
lean_object* l_RBNode_balance1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_balance1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_balance2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_4, 3);
lean_dec(x_8);
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = 0;
lean_ctor_set(x_4, 0, x_6);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_10);
x_11 = 1;
x_12 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_4);
lean_ctor_set_uint8(x_12, sizeof(void*)*4, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = 0;
x_16 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_6);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_15);
x_17 = 1;
x_18 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_3);
lean_ctor_set(x_18, 3, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_6, sizeof(void*)*4);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_4, 2);
x_23 = lean_ctor_get(x_4, 3);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
x_28 = lean_ctor_get(x_6, 2);
x_29 = lean_ctor_get(x_6, 3);
x_30 = 1;
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_30);
lean_ctor_set(x_4, 3, x_29);
lean_ctor_set(x_4, 2, x_28);
lean_ctor_set(x_4, 1, x_27);
lean_ctor_set(x_4, 0, x_26);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_30);
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_21);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_4);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_19);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
x_34 = lean_ctor_get(x_6, 2);
x_35 = lean_ctor_get(x_6, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_36 = 1;
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_2);
lean_ctor_set(x_37, 2, x_3);
lean_ctor_set(x_37, 3, x_5);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_36);
lean_ctor_set(x_4, 3, x_35);
lean_ctor_set(x_4, 2, x_34);
lean_ctor_set(x_4, 1, x_33);
lean_ctor_set(x_4, 0, x_32);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_36);
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_21);
lean_ctor_set(x_38, 2, x_22);
lean_ctor_set(x_38, 3, x_4);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_19);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_4, 1);
x_40 = lean_ctor_get(x_4, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_4);
x_41 = lean_ctor_get(x_6, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_6, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_6, 3);
lean_inc(x_44);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 x_45 = x_6;
} else {
 lean_dec_ref(x_6);
 x_45 = lean_box(0);
}
x_46 = 1;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(1, 4, 1);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_2);
lean_ctor_set(x_47, 2, x_3);
lean_ctor_set(x_47, 3, x_5);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_46);
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_42);
lean_ctor_set(x_48, 2, x_43);
lean_ctor_set(x_48, 3, x_44);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_46);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_39);
lean_ctor_set(x_49, 2, x_40);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_19);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_4);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_4, 3);
lean_dec(x_51);
x_52 = lean_ctor_get(x_4, 0);
lean_dec(x_52);
x_53 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_53);
x_54 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_2);
lean_ctor_set(x_54, 2, x_3);
lean_ctor_set(x_54, 3, x_4);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_19);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_4, 1);
x_56 = lean_ctor_get(x_4, 2);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_4);
x_57 = 0;
x_58 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_58, 0, x_5);
lean_ctor_set(x_58, 1, x_55);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_6);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_57);
x_59 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_2);
lean_ctor_set(x_59, 2, x_3);
lean_ctor_set(x_59, 3, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*4, x_19);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_5, sizeof(void*)*4);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_4);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_4, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_5);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_5, 0);
x_65 = lean_ctor_get(x_5, 1);
x_66 = lean_ctor_get(x_5, 2);
x_67 = lean_ctor_get(x_5, 3);
x_68 = 1;
lean_ctor_set(x_5, 3, x_64);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_68);
lean_ctor_set(x_4, 0, x_67);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_68);
x_69 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_69, 0, x_5);
lean_ctor_set(x_69, 1, x_65);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_4);
lean_ctor_set_uint8(x_69, sizeof(void*)*4, x_60);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_5, 0);
x_71 = lean_ctor_get(x_5, 1);
x_72 = lean_ctor_get(x_5, 2);
x_73 = lean_ctor_get(x_5, 3);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_5);
x_74 = 1;
x_75 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_2);
lean_ctor_set(x_75, 2, x_3);
lean_ctor_set(x_75, 3, x_70);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_74);
lean_ctor_set(x_4, 0, x_73);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_74);
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_71);
lean_ctor_set(x_76, 2, x_72);
lean_ctor_set(x_76, 3, x_4);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_60);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_77 = lean_ctor_get(x_4, 1);
x_78 = lean_ctor_get(x_4, 2);
x_79 = lean_ctor_get(x_4, 3);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_4);
x_80 = lean_ctor_get(x_5, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_5, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_5, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_5, 3);
lean_inc(x_83);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_84 = x_5;
} else {
 lean_dec_ref(x_5);
 x_84 = lean_box(0);
}
x_85 = 1;
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(1, 4, 1);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_2);
lean_ctor_set(x_86, 2, x_3);
lean_ctor_set(x_86, 3, x_80);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_85);
x_87 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_77);
lean_ctor_set(x_87, 2, x_78);
lean_ctor_set(x_87, 3, x_79);
lean_ctor_set_uint8(x_87, sizeof(void*)*4, x_85);
x_88 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_81);
lean_ctor_set(x_88, 2, x_82);
lean_ctor_set(x_88, 3, x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_60);
return x_88;
}
}
else
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_4, 3);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_4);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_4, 3);
lean_dec(x_91);
x_92 = lean_ctor_get(x_4, 0);
lean_dec(x_92);
x_93 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_93);
x_94 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_2);
lean_ctor_set(x_94, 2, x_3);
lean_ctor_set(x_94, 3, x_4);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_60);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_4, 1);
x_96 = lean_ctor_get(x_4, 2);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_4);
x_97 = 0;
x_98 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_98, 0, x_5);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set(x_98, 2, x_96);
lean_ctor_set(x_98, 3, x_89);
lean_ctor_set_uint8(x_98, sizeof(void*)*4, x_97);
x_99 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_99, 0, x_1);
lean_ctor_set(x_99, 1, x_2);
lean_ctor_set(x_99, 2, x_3);
lean_ctor_set(x_99, 3, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*4, x_60);
return x_99;
}
}
else
{
uint8_t x_100; 
x_100 = lean_ctor_get_uint8(x_89, sizeof(void*)*4);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_4);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_4, 3);
lean_dec(x_102);
x_103 = lean_ctor_get(x_4, 0);
lean_dec(x_103);
x_104 = !lean_is_exclusive(x_89);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_105 = lean_ctor_get(x_89, 0);
x_106 = lean_ctor_get(x_89, 1);
x_107 = lean_ctor_get(x_89, 2);
x_108 = lean_ctor_get(x_89, 3);
lean_inc(x_5);
lean_ctor_set(x_89, 3, x_5);
lean_ctor_set(x_89, 2, x_3);
lean_ctor_set(x_89, 1, x_2);
lean_ctor_set(x_89, 0, x_1);
x_109 = !lean_is_exclusive(x_5);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_5, 3);
lean_dec(x_110);
x_111 = lean_ctor_get(x_5, 2);
lean_dec(x_111);
x_112 = lean_ctor_get(x_5, 1);
lean_dec(x_112);
x_113 = lean_ctor_get(x_5, 0);
lean_dec(x_113);
lean_ctor_set_uint8(x_89, sizeof(void*)*4, x_60);
lean_ctor_set(x_5, 3, x_108);
lean_ctor_set(x_5, 2, x_107);
lean_ctor_set(x_5, 1, x_106);
lean_ctor_set(x_5, 0, x_105);
lean_ctor_set(x_4, 3, x_5);
lean_ctor_set(x_4, 0, x_89);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_100);
return x_4;
}
else
{
lean_object* x_114; 
lean_dec(x_5);
lean_ctor_set_uint8(x_89, sizeof(void*)*4, x_60);
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_105);
lean_ctor_set(x_114, 1, x_106);
lean_ctor_set(x_114, 2, x_107);
lean_ctor_set(x_114, 3, x_108);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_60);
lean_ctor_set(x_4, 3, x_114);
lean_ctor_set(x_4, 0, x_89);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_100);
return x_4;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_89, 0);
x_116 = lean_ctor_get(x_89, 1);
x_117 = lean_ctor_get(x_89, 2);
x_118 = lean_ctor_get(x_89, 3);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_89);
lean_inc(x_5);
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_1);
lean_ctor_set(x_119, 1, x_2);
lean_ctor_set(x_119, 2, x_3);
lean_ctor_set(x_119, 3, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_120 = x_5;
} else {
 lean_dec_ref(x_5);
 x_120 = lean_box(0);
}
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_60);
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 4, 1);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_115);
lean_ctor_set(x_121, 1, x_116);
lean_ctor_set(x_121, 2, x_117);
lean_ctor_set(x_121, 3, x_118);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_60);
lean_ctor_set(x_4, 3, x_121);
lean_ctor_set(x_4, 0, x_119);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_100);
return x_4;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_122 = lean_ctor_get(x_4, 1);
x_123 = lean_ctor_get(x_4, 2);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_4);
x_124 = lean_ctor_get(x_89, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_89, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_89, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_89, 3);
lean_inc(x_127);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 x_128 = x_89;
} else {
 lean_dec_ref(x_89);
 x_128 = lean_box(0);
}
lean_inc(x_5);
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 4, 1);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_1);
lean_ctor_set(x_129, 1, x_2);
lean_ctor_set(x_129, 2, x_3);
lean_ctor_set(x_129, 3, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_130 = x_5;
} else {
 lean_dec_ref(x_5);
 x_130 = lean_box(0);
}
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_60);
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 4, 1);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_124);
lean_ctor_set(x_131, 1, x_125);
lean_ctor_set(x_131, 2, x_126);
lean_ctor_set(x_131, 3, x_127);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_60);
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_122);
lean_ctor_set(x_132, 2, x_123);
lean_ctor_set(x_132, 3, x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_100);
return x_132;
}
}
else
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_4);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_4, 3);
lean_dec(x_134);
x_135 = lean_ctor_get(x_4, 0);
lean_dec(x_135);
x_136 = !lean_is_exclusive(x_5);
if (x_136 == 0)
{
uint8_t x_137; lean_object* x_138; 
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_100);
x_137 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_137);
x_138 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_138, 0, x_1);
lean_ctor_set(x_138, 1, x_2);
lean_ctor_set(x_138, 2, x_3);
lean_ctor_set(x_138, 3, x_4);
lean_ctor_set_uint8(x_138, sizeof(void*)*4, x_100);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_5, 0);
x_140 = lean_ctor_get(x_5, 1);
x_141 = lean_ctor_get(x_5, 2);
x_142 = lean_ctor_get(x_5, 3);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_5);
x_143 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_140);
lean_ctor_set(x_143, 2, x_141);
lean_ctor_set(x_143, 3, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*4, x_100);
x_144 = 0;
lean_ctor_set(x_4, 0, x_143);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_144);
x_145 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_145, 0, x_1);
lean_ctor_set(x_145, 1, x_2);
lean_ctor_set(x_145, 2, x_3);
lean_ctor_set(x_145, 3, x_4);
lean_ctor_set_uint8(x_145, sizeof(void*)*4, x_100);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
x_146 = lean_ctor_get(x_4, 1);
x_147 = lean_ctor_get(x_4, 2);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_4);
x_148 = lean_ctor_get(x_5, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_5, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_5, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_5, 3);
lean_inc(x_151);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_152 = x_5;
} else {
 lean_dec_ref(x_5);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 4, 1);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_148);
lean_ctor_set(x_153, 1, x_149);
lean_ctor_set(x_153, 2, x_150);
lean_ctor_set(x_153, 3, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_100);
x_154 = 0;
x_155 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_146);
lean_ctor_set(x_155, 2, x_147);
lean_ctor_set(x_155, 3, x_89);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_154);
x_156 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_156, 0, x_1);
lean_ctor_set(x_156, 1, x_2);
lean_ctor_set(x_156, 2, x_3);
lean_ctor_set(x_156, 3, x_155);
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_100);
return x_156;
}
}
}
}
}
}
}
}
lean_object* l_RBNode_balance2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_balance2___rarg), 4, 0);
return x_3;
}
}
lean_object* l_RBNode_balance2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_balance2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_RBNode_isRed___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
}
lean_object* l_RBNode_isRed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_isRed___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_RBNode_isRed___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_RBNode_isRed___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_RBNode_isRed___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_isRed(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_RBNode_isBlack___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
}
}
lean_object* l_RBNode_isBlack(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_isBlack___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_RBNode_isBlack___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_RBNode_isBlack___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_RBNode_isBlack___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_isBlack(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_ins___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_3);
x_13 = lean_apply_2(x_1, x_3, x_10);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_10);
x_15 = lean_apply_2(x_1, x_10, x_3);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
return x_2;
}
else
{
lean_object* x_17; 
x_17 = l_RBNode_ins___main___rarg(x_1, x_12, x_3, x_4);
lean_ctor_set(x_2, 3, x_17);
return x_2;
}
}
else
{
lean_object* x_18; 
x_18 = l_RBNode_ins___main___rarg(x_1, x_9, x_3, x_4);
lean_ctor_set(x_2, 0, x_18);
return x_2;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_20);
lean_inc(x_3);
x_23 = lean_apply_2(x_1, x_3, x_20);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_20);
x_25 = lean_apply_2(x_1, x_20, x_3);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_1);
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_4);
lean_ctor_set(x_27, 3, x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_7);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_RBNode_ins___main___rarg(x_1, x_22, x_3, x_4);
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_20);
lean_ctor_set(x_29, 2, x_21);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_7);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_RBNode_ins___main___rarg(x_1, x_19, x_3, x_4);
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_22);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_7);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_ctor_get(x_2, 3);
lean_inc(x_1);
lean_inc(x_34);
lean_inc(x_3);
x_37 = lean_apply_2(x_1, x_3, x_34);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_34);
x_39 = lean_apply_2(x_1, x_34, x_3);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
return x_2;
}
else
{
uint8_t x_41; 
x_41 = l_RBNode_isRed___rarg(x_36);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_RBNode_ins___main___rarg(x_1, x_36, x_3, x_4);
lean_ctor_set(x_2, 3, x_42);
return x_2;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_RBNode_ins___main___rarg(x_1, x_36, x_3, x_4);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 3);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_43, 3);
lean_dec(x_47);
x_48 = lean_ctor_get(x_43, 0);
lean_dec(x_48);
x_49 = 0;
lean_ctor_set(x_43, 0, x_45);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_49);
x_50 = 1;
lean_ctor_set(x_2, 3, x_43);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_50);
return x_2;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_43, 1);
x_52 = lean_ctor_get(x_43, 2);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_43);
x_53 = 0;
x_54 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_45);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_53);
x_55 = 1;
lean_ctor_set(x_2, 3, x_54);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_55);
return x_2;
}
}
else
{
uint8_t x_56; 
x_56 = lean_ctor_get_uint8(x_45, sizeof(void*)*4);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_43);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_43, 1);
x_59 = lean_ctor_get(x_43, 2);
x_60 = lean_ctor_get(x_43, 3);
lean_dec(x_60);
x_61 = lean_ctor_get(x_43, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_45);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_45, 0);
x_64 = lean_ctor_get(x_45, 1);
x_65 = lean_ctor_get(x_45, 2);
x_66 = lean_ctor_get(x_45, 3);
x_67 = 1;
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_45, 2, x_35);
lean_ctor_set(x_45, 1, x_34);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_67);
lean_ctor_set(x_43, 3, x_66);
lean_ctor_set(x_43, 2, x_65);
lean_ctor_set(x_43, 1, x_64);
lean_ctor_set(x_43, 0, x_63);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_67);
lean_ctor_set(x_2, 3, x_43);
lean_ctor_set(x_2, 2, x_59);
lean_ctor_set(x_2, 1, x_58);
lean_ctor_set(x_2, 0, x_45);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_56);
return x_2;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_45, 0);
x_69 = lean_ctor_get(x_45, 1);
x_70 = lean_ctor_get(x_45, 2);
x_71 = lean_ctor_get(x_45, 3);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_45);
x_72 = 1;
x_73 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_73, 0, x_33);
lean_ctor_set(x_73, 1, x_34);
lean_ctor_set(x_73, 2, x_35);
lean_ctor_set(x_73, 3, x_44);
lean_ctor_set_uint8(x_73, sizeof(void*)*4, x_72);
lean_ctor_set(x_43, 3, x_71);
lean_ctor_set(x_43, 2, x_70);
lean_ctor_set(x_43, 1, x_69);
lean_ctor_set(x_43, 0, x_68);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_72);
lean_ctor_set(x_2, 3, x_43);
lean_ctor_set(x_2, 2, x_59);
lean_ctor_set(x_2, 1, x_58);
lean_ctor_set(x_2, 0, x_73);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_56);
return x_2;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_74 = lean_ctor_get(x_43, 1);
x_75 = lean_ctor_get(x_43, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_43);
x_76 = lean_ctor_get(x_45, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_45, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_45, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_45, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_80 = x_45;
} else {
 lean_dec_ref(x_45);
 x_80 = lean_box(0);
}
x_81 = 1;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 4, 1);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_33);
lean_ctor_set(x_82, 1, x_34);
lean_ctor_set(x_82, 2, x_35);
lean_ctor_set(x_82, 3, x_44);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_81);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_78);
lean_ctor_set(x_83, 3, x_79);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_81);
lean_ctor_set(x_2, 3, x_83);
lean_ctor_set(x_2, 2, x_75);
lean_ctor_set(x_2, 1, x_74);
lean_ctor_set(x_2, 0, x_82);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_56);
return x_2;
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_43);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_43, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_43, 0);
lean_dec(x_86);
x_87 = 0;
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_87);
lean_ctor_set(x_2, 3, x_43);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_56);
return x_2;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_43, 1);
x_89 = lean_ctor_get(x_43, 2);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_43);
x_90 = 0;
x_91 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_91, 0, x_44);
lean_ctor_set(x_91, 1, x_88);
lean_ctor_set(x_91, 2, x_89);
lean_ctor_set(x_91, 3, x_45);
lean_ctor_set_uint8(x_91, sizeof(void*)*4, x_90);
lean_ctor_set(x_2, 3, x_91);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_56);
return x_2;
}
}
}
}
else
{
uint8_t x_92; 
x_92 = lean_ctor_get_uint8(x_44, sizeof(void*)*4);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_43);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_43, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_44);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_96 = lean_ctor_get(x_44, 0);
x_97 = lean_ctor_get(x_44, 1);
x_98 = lean_ctor_get(x_44, 2);
x_99 = lean_ctor_get(x_44, 3);
x_100 = 1;
lean_ctor_set(x_44, 3, x_96);
lean_ctor_set(x_44, 2, x_35);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_100);
lean_ctor_set(x_43, 0, x_99);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_100);
lean_ctor_set(x_2, 3, x_43);
lean_ctor_set(x_2, 2, x_98);
lean_ctor_set(x_2, 1, x_97);
lean_ctor_set(x_2, 0, x_44);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_92);
return x_2;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_44, 0);
x_102 = lean_ctor_get(x_44, 1);
x_103 = lean_ctor_get(x_44, 2);
x_104 = lean_ctor_get(x_44, 3);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_44);
x_105 = 1;
x_106 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_106, 0, x_33);
lean_ctor_set(x_106, 1, x_34);
lean_ctor_set(x_106, 2, x_35);
lean_ctor_set(x_106, 3, x_101);
lean_ctor_set_uint8(x_106, sizeof(void*)*4, x_105);
lean_ctor_set(x_43, 0, x_104);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_105);
lean_ctor_set(x_2, 3, x_43);
lean_ctor_set(x_2, 2, x_103);
lean_ctor_set(x_2, 1, x_102);
lean_ctor_set(x_2, 0, x_106);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_92);
return x_2;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_107 = lean_ctor_get(x_43, 1);
x_108 = lean_ctor_get(x_43, 2);
x_109 = lean_ctor_get(x_43, 3);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_43);
x_110 = lean_ctor_get(x_44, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_44, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_44, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_44, 3);
lean_inc(x_113);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_114 = x_44;
} else {
 lean_dec_ref(x_44);
 x_114 = lean_box(0);
}
x_115 = 1;
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(1, 4, 1);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_33);
lean_ctor_set(x_116, 1, x_34);
lean_ctor_set(x_116, 2, x_35);
lean_ctor_set(x_116, 3, x_110);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_115);
x_117 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_107);
lean_ctor_set(x_117, 2, x_108);
lean_ctor_set(x_117, 3, x_109);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_115);
lean_ctor_set(x_2, 3, x_117);
lean_ctor_set(x_2, 2, x_112);
lean_ctor_set(x_2, 1, x_111);
lean_ctor_set(x_2, 0, x_116);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_92);
return x_2;
}
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_43, 3);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_43);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_43, 3);
lean_dec(x_120);
x_121 = lean_ctor_get(x_43, 0);
lean_dec(x_121);
x_122 = 0;
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_122);
lean_ctor_set(x_2, 3, x_43);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_92);
return x_2;
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_43, 1);
x_124 = lean_ctor_get(x_43, 2);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_43);
x_125 = 0;
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_44);
lean_ctor_set(x_126, 1, x_123);
lean_ctor_set(x_126, 2, x_124);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_125);
lean_ctor_set(x_2, 3, x_126);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_92);
return x_2;
}
}
else
{
uint8_t x_127; 
x_127 = lean_ctor_get_uint8(x_118, sizeof(void*)*4);
if (x_127 == 0)
{
uint8_t x_128; 
lean_free_object(x_2);
x_128 = !lean_is_exclusive(x_43);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_ctor_get(x_43, 3);
lean_dec(x_129);
x_130 = lean_ctor_get(x_43, 0);
lean_dec(x_130);
x_131 = !lean_is_exclusive(x_118);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_118, 0);
x_133 = lean_ctor_get(x_118, 1);
x_134 = lean_ctor_get(x_118, 2);
x_135 = lean_ctor_get(x_118, 3);
lean_inc(x_44);
lean_ctor_set(x_118, 3, x_44);
lean_ctor_set(x_118, 2, x_35);
lean_ctor_set(x_118, 1, x_34);
lean_ctor_set(x_118, 0, x_33);
x_136 = !lean_is_exclusive(x_44);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_44, 3);
lean_dec(x_137);
x_138 = lean_ctor_get(x_44, 2);
lean_dec(x_138);
x_139 = lean_ctor_get(x_44, 1);
lean_dec(x_139);
x_140 = lean_ctor_get(x_44, 0);
lean_dec(x_140);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_92);
lean_ctor_set(x_44, 3, x_135);
lean_ctor_set(x_44, 2, x_134);
lean_ctor_set(x_44, 1, x_133);
lean_ctor_set(x_44, 0, x_132);
lean_ctor_set(x_43, 3, x_44);
lean_ctor_set(x_43, 0, x_118);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
else
{
lean_object* x_141; 
lean_dec(x_44);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_92);
x_141 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_141, 0, x_132);
lean_ctor_set(x_141, 1, x_133);
lean_ctor_set(x_141, 2, x_134);
lean_ctor_set(x_141, 3, x_135);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_92);
lean_ctor_set(x_43, 3, x_141);
lean_ctor_set(x_43, 0, x_118);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_142 = lean_ctor_get(x_118, 0);
x_143 = lean_ctor_get(x_118, 1);
x_144 = lean_ctor_get(x_118, 2);
x_145 = lean_ctor_get(x_118, 3);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_118);
lean_inc(x_44);
x_146 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_146, 0, x_33);
lean_ctor_set(x_146, 1, x_34);
lean_ctor_set(x_146, 2, x_35);
lean_ctor_set(x_146, 3, x_44);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_147 = x_44;
} else {
 lean_dec_ref(x_44);
 x_147 = lean_box(0);
}
lean_ctor_set_uint8(x_146, sizeof(void*)*4, x_92);
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 4, 1);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_142);
lean_ctor_set(x_148, 1, x_143);
lean_ctor_set(x_148, 2, x_144);
lean_ctor_set(x_148, 3, x_145);
lean_ctor_set_uint8(x_148, sizeof(void*)*4, x_92);
lean_ctor_set(x_43, 3, x_148);
lean_ctor_set(x_43, 0, x_146);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_149 = lean_ctor_get(x_43, 1);
x_150 = lean_ctor_get(x_43, 2);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_43);
x_151 = lean_ctor_get(x_118, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_118, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_118, 2);
lean_inc(x_153);
x_154 = lean_ctor_get(x_118, 3);
lean_inc(x_154);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 x_155 = x_118;
} else {
 lean_dec_ref(x_118);
 x_155 = lean_box(0);
}
lean_inc(x_44);
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 4, 1);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_33);
lean_ctor_set(x_156, 1, x_34);
lean_ctor_set(x_156, 2, x_35);
lean_ctor_set(x_156, 3, x_44);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_157 = x_44;
} else {
 lean_dec_ref(x_44);
 x_157 = lean_box(0);
}
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_92);
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 4, 1);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_151);
lean_ctor_set(x_158, 1, x_152);
lean_ctor_set(x_158, 2, x_153);
lean_ctor_set(x_158, 3, x_154);
lean_ctor_set_uint8(x_158, sizeof(void*)*4, x_92);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_149);
lean_ctor_set(x_159, 2, x_150);
lean_ctor_set(x_159, 3, x_158);
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_127);
return x_159;
}
}
else
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_43);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_43, 3);
lean_dec(x_161);
x_162 = lean_ctor_get(x_43, 0);
lean_dec(x_162);
x_163 = !lean_is_exclusive(x_44);
if (x_163 == 0)
{
uint8_t x_164; 
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_127);
x_164 = 0;
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_164);
lean_ctor_set(x_2, 3, x_43);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_127);
return x_2;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_165 = lean_ctor_get(x_44, 0);
x_166 = lean_ctor_get(x_44, 1);
x_167 = lean_ctor_get(x_44, 2);
x_168 = lean_ctor_get(x_44, 3);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_44);
x_169 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_166);
lean_ctor_set(x_169, 2, x_167);
lean_ctor_set(x_169, 3, x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_127);
x_170 = 0;
lean_ctor_set(x_43, 0, x_169);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_170);
lean_ctor_set(x_2, 3, x_43);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_127);
return x_2;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; 
x_171 = lean_ctor_get(x_43, 1);
x_172 = lean_ctor_get(x_43, 2);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_43);
x_173 = lean_ctor_get(x_44, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_44, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_44, 2);
lean_inc(x_175);
x_176 = lean_ctor_get(x_44, 3);
lean_inc(x_176);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_177 = x_44;
} else {
 lean_dec_ref(x_44);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 4, 1);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_173);
lean_ctor_set(x_178, 1, x_174);
lean_ctor_set(x_178, 2, x_175);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_127);
x_179 = 0;
x_180 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_171);
lean_ctor_set(x_180, 2, x_172);
lean_ctor_set(x_180, 3, x_118);
lean_ctor_set_uint8(x_180, sizeof(void*)*4, x_179);
lean_ctor_set(x_2, 3, x_180);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_127);
return x_2;
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
uint8_t x_181; 
x_181 = l_RBNode_isRed___rarg(x_33);
if (x_181 == 0)
{
lean_object* x_182; 
x_182 = l_RBNode_ins___main___rarg(x_1, x_33, x_3, x_4);
lean_ctor_set(x_2, 0, x_182);
return x_2;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = l_RBNode_ins___main___rarg(x_1, x_33, x_3, x_4);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_183, 3);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_183);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_190; 
x_187 = lean_ctor_get(x_183, 3);
lean_dec(x_187);
x_188 = lean_ctor_get(x_183, 0);
lean_dec(x_188);
x_189 = 0;
lean_ctor_set(x_183, 0, x_185);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_189);
x_190 = 1;
lean_ctor_set(x_2, 0, x_183);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_190);
return x_2;
}
else
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; uint8_t x_195; 
x_191 = lean_ctor_get(x_183, 1);
x_192 = lean_ctor_get(x_183, 2);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_183);
x_193 = 0;
x_194 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_194, 0, x_185);
lean_ctor_set(x_194, 1, x_191);
lean_ctor_set(x_194, 2, x_192);
lean_ctor_set(x_194, 3, x_185);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_193);
x_195 = 1;
lean_ctor_set(x_2, 0, x_194);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_195);
return x_2;
}
}
else
{
uint8_t x_196; 
x_196 = lean_ctor_get_uint8(x_185, sizeof(void*)*4);
if (x_196 == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_183);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_198 = lean_ctor_get(x_183, 1);
x_199 = lean_ctor_get(x_183, 2);
x_200 = lean_ctor_get(x_183, 3);
lean_dec(x_200);
x_201 = lean_ctor_get(x_183, 0);
lean_dec(x_201);
x_202 = !lean_is_exclusive(x_185);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_203 = lean_ctor_get(x_185, 0);
x_204 = lean_ctor_get(x_185, 1);
x_205 = lean_ctor_get(x_185, 2);
x_206 = lean_ctor_get(x_185, 3);
x_207 = 1;
lean_ctor_set(x_185, 3, x_203);
lean_ctor_set(x_185, 2, x_199);
lean_ctor_set(x_185, 1, x_198);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set_uint8(x_185, sizeof(void*)*4, x_207);
lean_ctor_set(x_183, 3, x_36);
lean_ctor_set(x_183, 2, x_35);
lean_ctor_set(x_183, 1, x_34);
lean_ctor_set(x_183, 0, x_206);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_207);
lean_ctor_set(x_2, 3, x_183);
lean_ctor_set(x_2, 2, x_205);
lean_ctor_set(x_2, 1, x_204);
lean_ctor_set(x_2, 0, x_185);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_196);
return x_2;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; 
x_208 = lean_ctor_get(x_185, 0);
x_209 = lean_ctor_get(x_185, 1);
x_210 = lean_ctor_get(x_185, 2);
x_211 = lean_ctor_get(x_185, 3);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_185);
x_212 = 1;
x_213 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_213, 0, x_184);
lean_ctor_set(x_213, 1, x_198);
lean_ctor_set(x_213, 2, x_199);
lean_ctor_set(x_213, 3, x_208);
lean_ctor_set_uint8(x_213, sizeof(void*)*4, x_212);
lean_ctor_set(x_183, 3, x_36);
lean_ctor_set(x_183, 2, x_35);
lean_ctor_set(x_183, 1, x_34);
lean_ctor_set(x_183, 0, x_211);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_212);
lean_ctor_set(x_2, 3, x_183);
lean_ctor_set(x_2, 2, x_210);
lean_ctor_set(x_2, 1, x_209);
lean_ctor_set(x_2, 0, x_213);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_196);
return x_2;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; 
x_214 = lean_ctor_get(x_183, 1);
x_215 = lean_ctor_get(x_183, 2);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_183);
x_216 = lean_ctor_get(x_185, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_185, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_185, 2);
lean_inc(x_218);
x_219 = lean_ctor_get(x_185, 3);
lean_inc(x_219);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 x_220 = x_185;
} else {
 lean_dec_ref(x_185);
 x_220 = lean_box(0);
}
x_221 = 1;
if (lean_is_scalar(x_220)) {
 x_222 = lean_alloc_ctor(1, 4, 1);
} else {
 x_222 = x_220;
}
lean_ctor_set(x_222, 0, x_184);
lean_ctor_set(x_222, 1, x_214);
lean_ctor_set(x_222, 2, x_215);
lean_ctor_set(x_222, 3, x_216);
lean_ctor_set_uint8(x_222, sizeof(void*)*4, x_221);
x_223 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_223, 0, x_219);
lean_ctor_set(x_223, 1, x_34);
lean_ctor_set(x_223, 2, x_35);
lean_ctor_set(x_223, 3, x_36);
lean_ctor_set_uint8(x_223, sizeof(void*)*4, x_221);
lean_ctor_set(x_2, 3, x_223);
lean_ctor_set(x_2, 2, x_218);
lean_ctor_set(x_2, 1, x_217);
lean_ctor_set(x_2, 0, x_222);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_196);
return x_2;
}
}
else
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_183);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_225 = lean_ctor_get(x_183, 3);
lean_dec(x_225);
x_226 = lean_ctor_get(x_183, 0);
lean_dec(x_226);
x_227 = 0;
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_227);
lean_ctor_set(x_2, 0, x_183);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_196);
return x_2;
}
else
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_183, 1);
x_229 = lean_ctor_get(x_183, 2);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_183);
x_230 = 0;
x_231 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_231, 0, x_184);
lean_ctor_set(x_231, 1, x_228);
lean_ctor_set(x_231, 2, x_229);
lean_ctor_set(x_231, 3, x_185);
lean_ctor_set_uint8(x_231, sizeof(void*)*4, x_230);
lean_ctor_set(x_2, 0, x_231);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_196);
return x_2;
}
}
}
}
else
{
uint8_t x_232; 
x_232 = lean_ctor_get_uint8(x_184, sizeof(void*)*4);
if (x_232 == 0)
{
uint8_t x_233; 
x_233 = !lean_is_exclusive(x_183);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_234 = lean_ctor_get(x_183, 1);
x_235 = lean_ctor_get(x_183, 2);
x_236 = lean_ctor_get(x_183, 3);
x_237 = lean_ctor_get(x_183, 0);
lean_dec(x_237);
x_238 = !lean_is_exclusive(x_184);
if (x_238 == 0)
{
uint8_t x_239; 
x_239 = 1;
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_239);
lean_ctor_set(x_183, 3, x_36);
lean_ctor_set(x_183, 2, x_35);
lean_ctor_set(x_183, 1, x_34);
lean_ctor_set(x_183, 0, x_236);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_239);
lean_ctor_set(x_2, 3, x_183);
lean_ctor_set(x_2, 2, x_235);
lean_ctor_set(x_2, 1, x_234);
lean_ctor_set(x_2, 0, x_184);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_232);
return x_2;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; 
x_240 = lean_ctor_get(x_184, 0);
x_241 = lean_ctor_get(x_184, 1);
x_242 = lean_ctor_get(x_184, 2);
x_243 = lean_ctor_get(x_184, 3);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_184);
x_244 = 1;
x_245 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_245, 0, x_240);
lean_ctor_set(x_245, 1, x_241);
lean_ctor_set(x_245, 2, x_242);
lean_ctor_set(x_245, 3, x_243);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
lean_ctor_set(x_183, 3, x_36);
lean_ctor_set(x_183, 2, x_35);
lean_ctor_set(x_183, 1, x_34);
lean_ctor_set(x_183, 0, x_236);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_244);
lean_ctor_set(x_2, 3, x_183);
lean_ctor_set(x_2, 2, x_235);
lean_ctor_set(x_2, 1, x_234);
lean_ctor_set(x_2, 0, x_245);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_232);
return x_2;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; 
x_246 = lean_ctor_get(x_183, 1);
x_247 = lean_ctor_get(x_183, 2);
x_248 = lean_ctor_get(x_183, 3);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_183);
x_249 = lean_ctor_get(x_184, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_184, 1);
lean_inc(x_250);
x_251 = lean_ctor_get(x_184, 2);
lean_inc(x_251);
x_252 = lean_ctor_get(x_184, 3);
lean_inc(x_252);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 x_253 = x_184;
} else {
 lean_dec_ref(x_184);
 x_253 = lean_box(0);
}
x_254 = 1;
if (lean_is_scalar(x_253)) {
 x_255 = lean_alloc_ctor(1, 4, 1);
} else {
 x_255 = x_253;
}
lean_ctor_set(x_255, 0, x_249);
lean_ctor_set(x_255, 1, x_250);
lean_ctor_set(x_255, 2, x_251);
lean_ctor_set(x_255, 3, x_252);
lean_ctor_set_uint8(x_255, sizeof(void*)*4, x_254);
x_256 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_256, 0, x_248);
lean_ctor_set(x_256, 1, x_34);
lean_ctor_set(x_256, 2, x_35);
lean_ctor_set(x_256, 3, x_36);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_254);
lean_ctor_set(x_2, 3, x_256);
lean_ctor_set(x_2, 2, x_247);
lean_ctor_set(x_2, 1, x_246);
lean_ctor_set(x_2, 0, x_255);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_232);
return x_2;
}
}
else
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_183, 3);
lean_inc(x_257);
if (lean_obj_tag(x_257) == 0)
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_183);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_259 = lean_ctor_get(x_183, 3);
lean_dec(x_259);
x_260 = lean_ctor_get(x_183, 0);
lean_dec(x_260);
x_261 = 0;
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_261);
lean_ctor_set(x_2, 0, x_183);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_232);
return x_2;
}
else
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; lean_object* x_265; 
x_262 = lean_ctor_get(x_183, 1);
x_263 = lean_ctor_get(x_183, 2);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_183);
x_264 = 0;
x_265 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_265, 0, x_184);
lean_ctor_set(x_265, 1, x_262);
lean_ctor_set(x_265, 2, x_263);
lean_ctor_set(x_265, 3, x_257);
lean_ctor_set_uint8(x_265, sizeof(void*)*4, x_264);
lean_ctor_set(x_2, 0, x_265);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_232);
return x_2;
}
}
else
{
uint8_t x_266; 
x_266 = lean_ctor_get_uint8(x_257, sizeof(void*)*4);
if (x_266 == 0)
{
uint8_t x_267; 
lean_free_object(x_2);
x_267 = !lean_is_exclusive(x_183);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_268 = lean_ctor_get(x_183, 1);
x_269 = lean_ctor_get(x_183, 2);
x_270 = lean_ctor_get(x_183, 3);
lean_dec(x_270);
x_271 = lean_ctor_get(x_183, 0);
lean_dec(x_271);
x_272 = !lean_is_exclusive(x_257);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_273 = lean_ctor_get(x_257, 0);
x_274 = lean_ctor_get(x_257, 1);
x_275 = lean_ctor_get(x_257, 2);
x_276 = lean_ctor_get(x_257, 3);
lean_inc(x_184);
lean_ctor_set(x_257, 3, x_273);
lean_ctor_set(x_257, 2, x_269);
lean_ctor_set(x_257, 1, x_268);
lean_ctor_set(x_257, 0, x_184);
x_277 = !lean_is_exclusive(x_184);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_278 = lean_ctor_get(x_184, 3);
lean_dec(x_278);
x_279 = lean_ctor_get(x_184, 2);
lean_dec(x_279);
x_280 = lean_ctor_get(x_184, 1);
lean_dec(x_280);
x_281 = lean_ctor_get(x_184, 0);
lean_dec(x_281);
lean_ctor_set_uint8(x_257, sizeof(void*)*4, x_232);
lean_ctor_set(x_184, 3, x_36);
lean_ctor_set(x_184, 2, x_35);
lean_ctor_set(x_184, 1, x_34);
lean_ctor_set(x_184, 0, x_276);
lean_ctor_set(x_183, 3, x_184);
lean_ctor_set(x_183, 2, x_275);
lean_ctor_set(x_183, 1, x_274);
lean_ctor_set(x_183, 0, x_257);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_266);
return x_183;
}
else
{
lean_object* x_282; 
lean_dec(x_184);
lean_ctor_set_uint8(x_257, sizeof(void*)*4, x_232);
x_282 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_282, 0, x_276);
lean_ctor_set(x_282, 1, x_34);
lean_ctor_set(x_282, 2, x_35);
lean_ctor_set(x_282, 3, x_36);
lean_ctor_set_uint8(x_282, sizeof(void*)*4, x_232);
lean_ctor_set(x_183, 3, x_282);
lean_ctor_set(x_183, 2, x_275);
lean_ctor_set(x_183, 1, x_274);
lean_ctor_set(x_183, 0, x_257);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_266);
return x_183;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_283 = lean_ctor_get(x_257, 0);
x_284 = lean_ctor_get(x_257, 1);
x_285 = lean_ctor_get(x_257, 2);
x_286 = lean_ctor_get(x_257, 3);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_257);
lean_inc(x_184);
x_287 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_287, 0, x_184);
lean_ctor_set(x_287, 1, x_268);
lean_ctor_set(x_287, 2, x_269);
lean_ctor_set(x_287, 3, x_283);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 x_288 = x_184;
} else {
 lean_dec_ref(x_184);
 x_288 = lean_box(0);
}
lean_ctor_set_uint8(x_287, sizeof(void*)*4, x_232);
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 4, 1);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_34);
lean_ctor_set(x_289, 2, x_35);
lean_ctor_set(x_289, 3, x_36);
lean_ctor_set_uint8(x_289, sizeof(void*)*4, x_232);
lean_ctor_set(x_183, 3, x_289);
lean_ctor_set(x_183, 2, x_285);
lean_ctor_set(x_183, 1, x_284);
lean_ctor_set(x_183, 0, x_287);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_266);
return x_183;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_290 = lean_ctor_get(x_183, 1);
x_291 = lean_ctor_get(x_183, 2);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_183);
x_292 = lean_ctor_get(x_257, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_257, 1);
lean_inc(x_293);
x_294 = lean_ctor_get(x_257, 2);
lean_inc(x_294);
x_295 = lean_ctor_get(x_257, 3);
lean_inc(x_295);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 lean_ctor_release(x_257, 2);
 lean_ctor_release(x_257, 3);
 x_296 = x_257;
} else {
 lean_dec_ref(x_257);
 x_296 = lean_box(0);
}
lean_inc(x_184);
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 4, 1);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_184);
lean_ctor_set(x_297, 1, x_290);
lean_ctor_set(x_297, 2, x_291);
lean_ctor_set(x_297, 3, x_292);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 x_298 = x_184;
} else {
 lean_dec_ref(x_184);
 x_298 = lean_box(0);
}
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_232);
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 4, 1);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_295);
lean_ctor_set(x_299, 1, x_34);
lean_ctor_set(x_299, 2, x_35);
lean_ctor_set(x_299, 3, x_36);
lean_ctor_set_uint8(x_299, sizeof(void*)*4, x_232);
x_300 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_293);
lean_ctor_set(x_300, 2, x_294);
lean_ctor_set(x_300, 3, x_299);
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_266);
return x_300;
}
}
else
{
uint8_t x_301; 
x_301 = !lean_is_exclusive(x_183);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_302 = lean_ctor_get(x_183, 3);
lean_dec(x_302);
x_303 = lean_ctor_get(x_183, 0);
lean_dec(x_303);
x_304 = !lean_is_exclusive(x_184);
if (x_304 == 0)
{
uint8_t x_305; 
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_266);
x_305 = 0;
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_305);
lean_ctor_set(x_2, 0, x_183);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_266);
return x_2;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_306 = lean_ctor_get(x_184, 0);
x_307 = lean_ctor_get(x_184, 1);
x_308 = lean_ctor_get(x_184, 2);
x_309 = lean_ctor_get(x_184, 3);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_184);
x_310 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_310, 0, x_306);
lean_ctor_set(x_310, 1, x_307);
lean_ctor_set(x_310, 2, x_308);
lean_ctor_set(x_310, 3, x_309);
lean_ctor_set_uint8(x_310, sizeof(void*)*4, x_266);
x_311 = 0;
lean_ctor_set(x_183, 0, x_310);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_311);
lean_ctor_set(x_2, 0, x_183);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_266);
return x_2;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; 
x_312 = lean_ctor_get(x_183, 1);
x_313 = lean_ctor_get(x_183, 2);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_183);
x_314 = lean_ctor_get(x_184, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_184, 1);
lean_inc(x_315);
x_316 = lean_ctor_get(x_184, 2);
lean_inc(x_316);
x_317 = lean_ctor_get(x_184, 3);
lean_inc(x_317);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 x_318 = x_184;
} else {
 lean_dec_ref(x_184);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 4, 1);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_314);
lean_ctor_set(x_319, 1, x_315);
lean_ctor_set(x_319, 2, x_316);
lean_ctor_set(x_319, 3, x_317);
lean_ctor_set_uint8(x_319, sizeof(void*)*4, x_266);
x_320 = 0;
x_321 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_312);
lean_ctor_set(x_321, 2, x_313);
lean_ctor_set(x_321, 3, x_257);
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_320);
lean_ctor_set(x_2, 0, x_321);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_266);
return x_2;
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
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_322 = lean_ctor_get(x_2, 0);
x_323 = lean_ctor_get(x_2, 1);
x_324 = lean_ctor_get(x_2, 2);
x_325 = lean_ctor_get(x_2, 3);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_323);
lean_inc(x_3);
x_326 = lean_apply_2(x_1, x_3, x_323);
x_327 = lean_unbox(x_326);
lean_dec(x_326);
if (x_327 == 0)
{
lean_object* x_328; uint8_t x_329; 
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_323);
x_328 = lean_apply_2(x_1, x_323, x_3);
x_329 = lean_unbox(x_328);
lean_dec(x_328);
if (x_329 == 0)
{
lean_object* x_330; 
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_1);
x_330 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_330, 0, x_322);
lean_ctor_set(x_330, 1, x_3);
lean_ctor_set(x_330, 2, x_4);
lean_ctor_set(x_330, 3, x_325);
lean_ctor_set_uint8(x_330, sizeof(void*)*4, x_7);
return x_330;
}
else
{
uint8_t x_331; 
x_331 = l_RBNode_isRed___rarg(x_325);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; 
x_332 = l_RBNode_ins___main___rarg(x_1, x_325, x_3, x_4);
x_333 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_333, 0, x_322);
lean_ctor_set(x_333, 1, x_323);
lean_ctor_set(x_333, 2, x_324);
lean_ctor_set(x_333, 3, x_332);
lean_ctor_set_uint8(x_333, sizeof(void*)*4, x_7);
return x_333;
}
else
{
lean_object* x_334; lean_object* x_335; 
x_334 = l_RBNode_ins___main___rarg(x_1, x_325, x_3, x_4);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_334, 3);
lean_inc(x_336);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; lean_object* x_341; uint8_t x_342; lean_object* x_343; 
x_337 = lean_ctor_get(x_334, 1);
lean_inc(x_337);
x_338 = lean_ctor_get(x_334, 2);
lean_inc(x_338);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 lean_ctor_release(x_334, 2);
 lean_ctor_release(x_334, 3);
 x_339 = x_334;
} else {
 lean_dec_ref(x_334);
 x_339 = lean_box(0);
}
x_340 = 0;
if (lean_is_scalar(x_339)) {
 x_341 = lean_alloc_ctor(1, 4, 1);
} else {
 x_341 = x_339;
}
lean_ctor_set(x_341, 0, x_336);
lean_ctor_set(x_341, 1, x_337);
lean_ctor_set(x_341, 2, x_338);
lean_ctor_set(x_341, 3, x_336);
lean_ctor_set_uint8(x_341, sizeof(void*)*4, x_340);
x_342 = 1;
x_343 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_343, 0, x_322);
lean_ctor_set(x_343, 1, x_323);
lean_ctor_set(x_343, 2, x_324);
lean_ctor_set(x_343, 3, x_341);
lean_ctor_set_uint8(x_343, sizeof(void*)*4, x_342);
return x_343;
}
else
{
uint8_t x_344; 
x_344 = lean_ctor_get_uint8(x_336, sizeof(void*)*4);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_345 = lean_ctor_get(x_334, 1);
lean_inc(x_345);
x_346 = lean_ctor_get(x_334, 2);
lean_inc(x_346);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 lean_ctor_release(x_334, 2);
 lean_ctor_release(x_334, 3);
 x_347 = x_334;
} else {
 lean_dec_ref(x_334);
 x_347 = lean_box(0);
}
x_348 = lean_ctor_get(x_336, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_336, 1);
lean_inc(x_349);
x_350 = lean_ctor_get(x_336, 2);
lean_inc(x_350);
x_351 = lean_ctor_get(x_336, 3);
lean_inc(x_351);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_352 = x_336;
} else {
 lean_dec_ref(x_336);
 x_352 = lean_box(0);
}
x_353 = 1;
if (lean_is_scalar(x_352)) {
 x_354 = lean_alloc_ctor(1, 4, 1);
} else {
 x_354 = x_352;
}
lean_ctor_set(x_354, 0, x_322);
lean_ctor_set(x_354, 1, x_323);
lean_ctor_set(x_354, 2, x_324);
lean_ctor_set(x_354, 3, x_335);
lean_ctor_set_uint8(x_354, sizeof(void*)*4, x_353);
if (lean_is_scalar(x_347)) {
 x_355 = lean_alloc_ctor(1, 4, 1);
} else {
 x_355 = x_347;
}
lean_ctor_set(x_355, 0, x_348);
lean_ctor_set(x_355, 1, x_349);
lean_ctor_set(x_355, 2, x_350);
lean_ctor_set(x_355, 3, x_351);
lean_ctor_set_uint8(x_355, sizeof(void*)*4, x_353);
x_356 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_345);
lean_ctor_set(x_356, 2, x_346);
lean_ctor_set(x_356, 3, x_355);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_344);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; lean_object* x_361; lean_object* x_362; 
x_357 = lean_ctor_get(x_334, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_334, 2);
lean_inc(x_358);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 lean_ctor_release(x_334, 2);
 lean_ctor_release(x_334, 3);
 x_359 = x_334;
} else {
 lean_dec_ref(x_334);
 x_359 = lean_box(0);
}
x_360 = 0;
if (lean_is_scalar(x_359)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_359;
}
lean_ctor_set(x_361, 0, x_335);
lean_ctor_set(x_361, 1, x_357);
lean_ctor_set(x_361, 2, x_358);
lean_ctor_set(x_361, 3, x_336);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_360);
x_362 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_362, 0, x_322);
lean_ctor_set(x_362, 1, x_323);
lean_ctor_set(x_362, 2, x_324);
lean_ctor_set(x_362, 3, x_361);
lean_ctor_set_uint8(x_362, sizeof(void*)*4, x_344);
return x_362;
}
}
}
else
{
uint8_t x_363; 
x_363 = lean_ctor_get_uint8(x_335, sizeof(void*)*4);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_364 = lean_ctor_get(x_334, 1);
lean_inc(x_364);
x_365 = lean_ctor_get(x_334, 2);
lean_inc(x_365);
x_366 = lean_ctor_get(x_334, 3);
lean_inc(x_366);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 lean_ctor_release(x_334, 2);
 lean_ctor_release(x_334, 3);
 x_367 = x_334;
} else {
 lean_dec_ref(x_334);
 x_367 = lean_box(0);
}
x_368 = lean_ctor_get(x_335, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_335, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_335, 2);
lean_inc(x_370);
x_371 = lean_ctor_get(x_335, 3);
lean_inc(x_371);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 lean_ctor_release(x_335, 2);
 lean_ctor_release(x_335, 3);
 x_372 = x_335;
} else {
 lean_dec_ref(x_335);
 x_372 = lean_box(0);
}
x_373 = 1;
if (lean_is_scalar(x_372)) {
 x_374 = lean_alloc_ctor(1, 4, 1);
} else {
 x_374 = x_372;
}
lean_ctor_set(x_374, 0, x_322);
lean_ctor_set(x_374, 1, x_323);
lean_ctor_set(x_374, 2, x_324);
lean_ctor_set(x_374, 3, x_368);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_373);
if (lean_is_scalar(x_367)) {
 x_375 = lean_alloc_ctor(1, 4, 1);
} else {
 x_375 = x_367;
}
lean_ctor_set(x_375, 0, x_371);
lean_ctor_set(x_375, 1, x_364);
lean_ctor_set(x_375, 2, x_365);
lean_ctor_set(x_375, 3, x_366);
lean_ctor_set_uint8(x_375, sizeof(void*)*4, x_373);
x_376 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_369);
lean_ctor_set(x_376, 2, x_370);
lean_ctor_set(x_376, 3, x_375);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_363);
return x_376;
}
else
{
lean_object* x_377; 
x_377 = lean_ctor_get(x_334, 3);
lean_inc(x_377);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_382; lean_object* x_383; 
x_378 = lean_ctor_get(x_334, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_334, 2);
lean_inc(x_379);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 lean_ctor_release(x_334, 2);
 lean_ctor_release(x_334, 3);
 x_380 = x_334;
} else {
 lean_dec_ref(x_334);
 x_380 = lean_box(0);
}
x_381 = 0;
if (lean_is_scalar(x_380)) {
 x_382 = lean_alloc_ctor(1, 4, 1);
} else {
 x_382 = x_380;
}
lean_ctor_set(x_382, 0, x_335);
lean_ctor_set(x_382, 1, x_378);
lean_ctor_set(x_382, 2, x_379);
lean_ctor_set(x_382, 3, x_377);
lean_ctor_set_uint8(x_382, sizeof(void*)*4, x_381);
x_383 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_383, 0, x_322);
lean_ctor_set(x_383, 1, x_323);
lean_ctor_set(x_383, 2, x_324);
lean_ctor_set(x_383, 3, x_382);
lean_ctor_set_uint8(x_383, sizeof(void*)*4, x_363);
return x_383;
}
else
{
uint8_t x_384; 
x_384 = lean_ctor_get_uint8(x_377, sizeof(void*)*4);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_385 = lean_ctor_get(x_334, 1);
lean_inc(x_385);
x_386 = lean_ctor_get(x_334, 2);
lean_inc(x_386);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 lean_ctor_release(x_334, 2);
 lean_ctor_release(x_334, 3);
 x_387 = x_334;
} else {
 lean_dec_ref(x_334);
 x_387 = lean_box(0);
}
x_388 = lean_ctor_get(x_377, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_377, 1);
lean_inc(x_389);
x_390 = lean_ctor_get(x_377, 2);
lean_inc(x_390);
x_391 = lean_ctor_get(x_377, 3);
lean_inc(x_391);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_392 = x_377;
} else {
 lean_dec_ref(x_377);
 x_392 = lean_box(0);
}
lean_inc(x_335);
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 4, 1);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_322);
lean_ctor_set(x_393, 1, x_323);
lean_ctor_set(x_393, 2, x_324);
lean_ctor_set(x_393, 3, x_335);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 lean_ctor_release(x_335, 2);
 lean_ctor_release(x_335, 3);
 x_394 = x_335;
} else {
 lean_dec_ref(x_335);
 x_394 = lean_box(0);
}
lean_ctor_set_uint8(x_393, sizeof(void*)*4, x_363);
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 4, 1);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_388);
lean_ctor_set(x_395, 1, x_389);
lean_ctor_set(x_395, 2, x_390);
lean_ctor_set(x_395, 3, x_391);
lean_ctor_set_uint8(x_395, sizeof(void*)*4, x_363);
if (lean_is_scalar(x_387)) {
 x_396 = lean_alloc_ctor(1, 4, 1);
} else {
 x_396 = x_387;
}
lean_ctor_set(x_396, 0, x_393);
lean_ctor_set(x_396, 1, x_385);
lean_ctor_set(x_396, 2, x_386);
lean_ctor_set(x_396, 3, x_395);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_384);
return x_396;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; lean_object* x_408; 
x_397 = lean_ctor_get(x_334, 1);
lean_inc(x_397);
x_398 = lean_ctor_get(x_334, 2);
lean_inc(x_398);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 lean_ctor_release(x_334, 2);
 lean_ctor_release(x_334, 3);
 x_399 = x_334;
} else {
 lean_dec_ref(x_334);
 x_399 = lean_box(0);
}
x_400 = lean_ctor_get(x_335, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_335, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_335, 2);
lean_inc(x_402);
x_403 = lean_ctor_get(x_335, 3);
lean_inc(x_403);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 lean_ctor_release(x_335, 2);
 lean_ctor_release(x_335, 3);
 x_404 = x_335;
} else {
 lean_dec_ref(x_335);
 x_404 = lean_box(0);
}
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_400);
lean_ctor_set(x_405, 1, x_401);
lean_ctor_set(x_405, 2, x_402);
lean_ctor_set(x_405, 3, x_403);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_384);
x_406 = 0;
if (lean_is_scalar(x_399)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_399;
}
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_397);
lean_ctor_set(x_407, 2, x_398);
lean_ctor_set(x_407, 3, x_377);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
x_408 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_408, 0, x_322);
lean_ctor_set(x_408, 1, x_323);
lean_ctor_set(x_408, 2, x_324);
lean_ctor_set(x_408, 3, x_407);
lean_ctor_set_uint8(x_408, sizeof(void*)*4, x_384);
return x_408;
}
}
}
}
}
}
}
else
{
uint8_t x_409; 
x_409 = l_RBNode_isRed___rarg(x_322);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; 
x_410 = l_RBNode_ins___main___rarg(x_1, x_322, x_3, x_4);
x_411 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_323);
lean_ctor_set(x_411, 2, x_324);
lean_ctor_set(x_411, 3, x_325);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_7);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; 
x_412 = l_RBNode_ins___main___rarg(x_1, x_322, x_3, x_4);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; 
x_414 = lean_ctor_get(x_412, 3);
lean_inc(x_414);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; uint8_t x_420; lean_object* x_421; 
x_415 = lean_ctor_get(x_412, 1);
lean_inc(x_415);
x_416 = lean_ctor_get(x_412, 2);
lean_inc(x_416);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 lean_ctor_release(x_412, 2);
 lean_ctor_release(x_412, 3);
 x_417 = x_412;
} else {
 lean_dec_ref(x_412);
 x_417 = lean_box(0);
}
x_418 = 0;
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(1, 4, 1);
} else {
 x_419 = x_417;
}
lean_ctor_set(x_419, 0, x_414);
lean_ctor_set(x_419, 1, x_415);
lean_ctor_set(x_419, 2, x_416);
lean_ctor_set(x_419, 3, x_414);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
x_420 = 1;
x_421 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_323);
lean_ctor_set(x_421, 2, x_324);
lean_ctor_set(x_421, 3, x_325);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_420);
return x_421;
}
else
{
uint8_t x_422; 
x_422 = lean_ctor_get_uint8(x_414, sizeof(void*)*4);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_423 = lean_ctor_get(x_412, 1);
lean_inc(x_423);
x_424 = lean_ctor_get(x_412, 2);
lean_inc(x_424);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 lean_ctor_release(x_412, 2);
 lean_ctor_release(x_412, 3);
 x_425 = x_412;
} else {
 lean_dec_ref(x_412);
 x_425 = lean_box(0);
}
x_426 = lean_ctor_get(x_414, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_414, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_414, 2);
lean_inc(x_428);
x_429 = lean_ctor_get(x_414, 3);
lean_inc(x_429);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 lean_ctor_release(x_414, 2);
 lean_ctor_release(x_414, 3);
 x_430 = x_414;
} else {
 lean_dec_ref(x_414);
 x_430 = lean_box(0);
}
x_431 = 1;
if (lean_is_scalar(x_430)) {
 x_432 = lean_alloc_ctor(1, 4, 1);
} else {
 x_432 = x_430;
}
lean_ctor_set(x_432, 0, x_413);
lean_ctor_set(x_432, 1, x_423);
lean_ctor_set(x_432, 2, x_424);
lean_ctor_set(x_432, 3, x_426);
lean_ctor_set_uint8(x_432, sizeof(void*)*4, x_431);
if (lean_is_scalar(x_425)) {
 x_433 = lean_alloc_ctor(1, 4, 1);
} else {
 x_433 = x_425;
}
lean_ctor_set(x_433, 0, x_429);
lean_ctor_set(x_433, 1, x_323);
lean_ctor_set(x_433, 2, x_324);
lean_ctor_set(x_433, 3, x_325);
lean_ctor_set_uint8(x_433, sizeof(void*)*4, x_431);
x_434 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_427);
lean_ctor_set(x_434, 2, x_428);
lean_ctor_set(x_434, 3, x_433);
lean_ctor_set_uint8(x_434, sizeof(void*)*4, x_422);
return x_434;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; 
x_435 = lean_ctor_get(x_412, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_412, 2);
lean_inc(x_436);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 lean_ctor_release(x_412, 2);
 lean_ctor_release(x_412, 3);
 x_437 = x_412;
} else {
 lean_dec_ref(x_412);
 x_437 = lean_box(0);
}
x_438 = 0;
if (lean_is_scalar(x_437)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_437;
}
lean_ctor_set(x_439, 0, x_413);
lean_ctor_set(x_439, 1, x_435);
lean_ctor_set(x_439, 2, x_436);
lean_ctor_set(x_439, 3, x_414);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
x_440 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_323);
lean_ctor_set(x_440, 2, x_324);
lean_ctor_set(x_440, 3, x_325);
lean_ctor_set_uint8(x_440, sizeof(void*)*4, x_422);
return x_440;
}
}
}
else
{
uint8_t x_441; 
x_441 = lean_ctor_get_uint8(x_413, sizeof(void*)*4);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_442 = lean_ctor_get(x_412, 1);
lean_inc(x_442);
x_443 = lean_ctor_get(x_412, 2);
lean_inc(x_443);
x_444 = lean_ctor_get(x_412, 3);
lean_inc(x_444);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 lean_ctor_release(x_412, 2);
 lean_ctor_release(x_412, 3);
 x_445 = x_412;
} else {
 lean_dec_ref(x_412);
 x_445 = lean_box(0);
}
x_446 = lean_ctor_get(x_413, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_413, 1);
lean_inc(x_447);
x_448 = lean_ctor_get(x_413, 2);
lean_inc(x_448);
x_449 = lean_ctor_get(x_413, 3);
lean_inc(x_449);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 lean_ctor_release(x_413, 2);
 lean_ctor_release(x_413, 3);
 x_450 = x_413;
} else {
 lean_dec_ref(x_413);
 x_450 = lean_box(0);
}
x_451 = 1;
if (lean_is_scalar(x_450)) {
 x_452 = lean_alloc_ctor(1, 4, 1);
} else {
 x_452 = x_450;
}
lean_ctor_set(x_452, 0, x_446);
lean_ctor_set(x_452, 1, x_447);
lean_ctor_set(x_452, 2, x_448);
lean_ctor_set(x_452, 3, x_449);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_451);
if (lean_is_scalar(x_445)) {
 x_453 = lean_alloc_ctor(1, 4, 1);
} else {
 x_453 = x_445;
}
lean_ctor_set(x_453, 0, x_444);
lean_ctor_set(x_453, 1, x_323);
lean_ctor_set(x_453, 2, x_324);
lean_ctor_set(x_453, 3, x_325);
lean_ctor_set_uint8(x_453, sizeof(void*)*4, x_451);
x_454 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_442);
lean_ctor_set(x_454, 2, x_443);
lean_ctor_set(x_454, 3, x_453);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_441);
return x_454;
}
else
{
lean_object* x_455; 
x_455 = lean_ctor_get(x_412, 3);
lean_inc(x_455);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; lean_object* x_460; lean_object* x_461; 
x_456 = lean_ctor_get(x_412, 1);
lean_inc(x_456);
x_457 = lean_ctor_get(x_412, 2);
lean_inc(x_457);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 lean_ctor_release(x_412, 2);
 lean_ctor_release(x_412, 3);
 x_458 = x_412;
} else {
 lean_dec_ref(x_412);
 x_458 = lean_box(0);
}
x_459 = 0;
if (lean_is_scalar(x_458)) {
 x_460 = lean_alloc_ctor(1, 4, 1);
} else {
 x_460 = x_458;
}
lean_ctor_set(x_460, 0, x_413);
lean_ctor_set(x_460, 1, x_456);
lean_ctor_set(x_460, 2, x_457);
lean_ctor_set(x_460, 3, x_455);
lean_ctor_set_uint8(x_460, sizeof(void*)*4, x_459);
x_461 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_323);
lean_ctor_set(x_461, 2, x_324);
lean_ctor_set(x_461, 3, x_325);
lean_ctor_set_uint8(x_461, sizeof(void*)*4, x_441);
return x_461;
}
else
{
uint8_t x_462; 
x_462 = lean_ctor_get_uint8(x_455, sizeof(void*)*4);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_463 = lean_ctor_get(x_412, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_412, 2);
lean_inc(x_464);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 lean_ctor_release(x_412, 2);
 lean_ctor_release(x_412, 3);
 x_465 = x_412;
} else {
 lean_dec_ref(x_412);
 x_465 = lean_box(0);
}
x_466 = lean_ctor_get(x_455, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_455, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_455, 2);
lean_inc(x_468);
x_469 = lean_ctor_get(x_455, 3);
lean_inc(x_469);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 lean_ctor_release(x_455, 2);
 lean_ctor_release(x_455, 3);
 x_470 = x_455;
} else {
 lean_dec_ref(x_455);
 x_470 = lean_box(0);
}
lean_inc(x_413);
if (lean_is_scalar(x_470)) {
 x_471 = lean_alloc_ctor(1, 4, 1);
} else {
 x_471 = x_470;
}
lean_ctor_set(x_471, 0, x_413);
lean_ctor_set(x_471, 1, x_463);
lean_ctor_set(x_471, 2, x_464);
lean_ctor_set(x_471, 3, x_466);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 lean_ctor_release(x_413, 2);
 lean_ctor_release(x_413, 3);
 x_472 = x_413;
} else {
 lean_dec_ref(x_413);
 x_472 = lean_box(0);
}
lean_ctor_set_uint8(x_471, sizeof(void*)*4, x_441);
if (lean_is_scalar(x_472)) {
 x_473 = lean_alloc_ctor(1, 4, 1);
} else {
 x_473 = x_472;
}
lean_ctor_set(x_473, 0, x_469);
lean_ctor_set(x_473, 1, x_323);
lean_ctor_set(x_473, 2, x_324);
lean_ctor_set(x_473, 3, x_325);
lean_ctor_set_uint8(x_473, sizeof(void*)*4, x_441);
if (lean_is_scalar(x_465)) {
 x_474 = lean_alloc_ctor(1, 4, 1);
} else {
 x_474 = x_465;
}
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_467);
lean_ctor_set(x_474, 2, x_468);
lean_ctor_set(x_474, 3, x_473);
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_462);
return x_474;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; lean_object* x_485; lean_object* x_486; 
x_475 = lean_ctor_get(x_412, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_412, 2);
lean_inc(x_476);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 lean_ctor_release(x_412, 2);
 lean_ctor_release(x_412, 3);
 x_477 = x_412;
} else {
 lean_dec_ref(x_412);
 x_477 = lean_box(0);
}
x_478 = lean_ctor_get(x_413, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_413, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_413, 2);
lean_inc(x_480);
x_481 = lean_ctor_get(x_413, 3);
lean_inc(x_481);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 lean_ctor_release(x_413, 2);
 lean_ctor_release(x_413, 3);
 x_482 = x_413;
} else {
 lean_dec_ref(x_413);
 x_482 = lean_box(0);
}
if (lean_is_scalar(x_482)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_482;
}
lean_ctor_set(x_483, 0, x_478);
lean_ctor_set(x_483, 1, x_479);
lean_ctor_set(x_483, 2, x_480);
lean_ctor_set(x_483, 3, x_481);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_462);
x_484 = 0;
if (lean_is_scalar(x_477)) {
 x_485 = lean_alloc_ctor(1, 4, 1);
} else {
 x_485 = x_477;
}
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_475);
lean_ctor_set(x_485, 2, x_476);
lean_ctor_set(x_485, 3, x_455);
lean_ctor_set_uint8(x_485, sizeof(void*)*4, x_484);
x_486 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_323);
lean_ctor_set(x_486, 2, x_324);
lean_ctor_set(x_486, 3, x_325);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_462);
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
lean_object* l_RBNode_ins___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_ins___main___rarg), 4, 0);
return x_3;
}
}
lean_object* l_RBNode_ins___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_ins___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_ins___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_ins___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_RBNode_ins(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_ins___rarg), 4, 0);
return x_3;
}
}
lean_object* l_RBNode_ins___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_ins(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_setBlack___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_3);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_8 = 1;
x_9 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_8);
return x_9;
}
}
}
}
lean_object* l_RBNode_setBlack(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_setBlack___rarg), 1, 0);
return x_3;
}
}
lean_object* l_RBNode_setBlack___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_setBlack(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_RBNode_isRed___rarg(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_RBNode_ins___main___rarg(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_RBNode_ins___main___rarg(x_1, x_2, x_3, x_4);
x_8 = l_RBNode_setBlack___rarg(x_7);
return x_8;
}
}
}
lean_object* l_RBNode_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_insert___rarg), 4, 0);
return x_3;
}
}
lean_object* l_RBNode_insert___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_insert(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_balance_u2083___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 3);
lean_dec(x_11);
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
lean_ctor_set(x_4, 0, x_9);
x_13 = 1;
x_14 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*4, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*4, x_7);
x_18 = 1;
x_19 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_3);
lean_ctor_set(x_19, 3, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_9, sizeof(void*)*4);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 2);
x_24 = lean_ctor_get(x_4, 3);
lean_dec(x_24);
x_25 = lean_ctor_get(x_4, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
x_29 = lean_ctor_get(x_9, 2);
x_30 = lean_ctor_get(x_9, 3);
x_31 = 1;
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_31);
lean_ctor_set(x_4, 3, x_30);
lean_ctor_set(x_4, 2, x_29);
lean_ctor_set(x_4, 1, x_28);
lean_ctor_set(x_4, 0, x_27);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_31);
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_9);
lean_ctor_set(x_32, 1, x_22);
lean_ctor_set(x_32, 2, x_23);
lean_ctor_set(x_32, 3, x_4);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_20);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
x_35 = lean_ctor_get(x_9, 2);
x_36 = lean_ctor_get(x_9, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
x_37 = 1;
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_8);
lean_ctor_set(x_38, 1, x_2);
lean_ctor_set(x_38, 2, x_3);
lean_ctor_set(x_38, 3, x_8);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_37);
lean_ctor_set(x_4, 3, x_36);
lean_ctor_set(x_4, 2, x_35);
lean_ctor_set(x_4, 1, x_34);
lean_ctor_set(x_4, 0, x_33);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_37);
x_39 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_22);
lean_ctor_set(x_39, 2, x_23);
lean_ctor_set(x_39, 3, x_4);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_20);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_4, 1);
x_41 = lean_ctor_get(x_4, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_4);
x_42 = lean_ctor_get(x_9, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_9, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_9, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_9, 3);
lean_inc(x_45);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 x_46 = x_9;
} else {
 lean_dec_ref(x_9);
 x_46 = lean_box(0);
}
x_47 = 1;
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(1, 4, 1);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_8);
lean_ctor_set(x_48, 1, x_2);
lean_ctor_set(x_48, 2, x_3);
lean_ctor_set(x_48, 3, x_8);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_47);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set(x_49, 2, x_44);
lean_ctor_set(x_49, 3, x_45);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_47);
x_50 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_40);
lean_ctor_set(x_50, 2, x_41);
lean_ctor_set(x_50, 3, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_20);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_9);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_9, 3);
lean_dec(x_52);
x_53 = lean_ctor_get(x_9, 2);
lean_dec(x_53);
x_54 = lean_ctor_get(x_9, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_9, 0);
lean_dec(x_55);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_56; 
lean_dec(x_9);
x_56 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_56, 0, x_8);
lean_ctor_set(x_56, 1, x_2);
lean_ctor_set(x_56, 2, x_3);
lean_ctor_set(x_56, 3, x_4);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_20);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_8, sizeof(void*)*4);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_4, 3);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_4);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_4, 3);
lean_dec(x_60);
x_61 = lean_ctor_get(x_4, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_8);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_8, 0);
x_64 = lean_ctor_get(x_8, 1);
x_65 = lean_ctor_get(x_8, 2);
x_66 = lean_ctor_get(x_8, 3);
x_67 = 1;
lean_ctor_set(x_8, 3, x_63);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_58);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_67);
lean_ctor_set(x_4, 0, x_66);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_67);
x_68 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_68, 0, x_8);
lean_ctor_set(x_68, 1, x_64);
lean_ctor_set(x_68, 2, x_65);
lean_ctor_set(x_68, 3, x_4);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_57);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_8, 0);
x_70 = lean_ctor_get(x_8, 1);
x_71 = lean_ctor_get(x_8, 2);
x_72 = lean_ctor_get(x_8, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_8);
x_73 = 1;
x_74 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_74, 0, x_58);
lean_ctor_set(x_74, 1, x_2);
lean_ctor_set(x_74, 2, x_3);
lean_ctor_set(x_74, 3, x_69);
lean_ctor_set_uint8(x_74, sizeof(void*)*4, x_73);
lean_ctor_set(x_4, 0, x_72);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_73);
x_75 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
lean_ctor_set(x_75, 2, x_71);
lean_ctor_set(x_75, 3, x_4);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_57);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_76 = lean_ctor_get(x_4, 1);
x_77 = lean_ctor_get(x_4, 2);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_4);
x_78 = lean_ctor_get(x_8, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_8, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_8, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_8, 3);
lean_inc(x_81);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_82 = x_8;
} else {
 lean_dec_ref(x_8);
 x_82 = lean_box(0);
}
x_83 = 1;
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(1, 4, 1);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_58);
lean_ctor_set(x_84, 1, x_2);
lean_ctor_set(x_84, 2, x_3);
lean_ctor_set(x_84, 3, x_78);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_83);
x_85 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_76);
lean_ctor_set(x_85, 2, x_77);
lean_ctor_set(x_85, 3, x_58);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_83);
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_79);
lean_ctor_set(x_86, 2, x_80);
lean_ctor_set(x_86, 3, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_57);
return x_86;
}
}
else
{
uint8_t x_87; 
x_87 = lean_ctor_get_uint8(x_58, sizeof(void*)*4);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_4);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_4, 1);
x_90 = lean_ctor_get(x_4, 2);
x_91 = lean_ctor_get(x_4, 3);
lean_dec(x_91);
x_92 = lean_ctor_get(x_4, 0);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_8);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_58);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_95 = lean_ctor_get(x_8, 0);
x_96 = lean_ctor_get(x_8, 1);
x_97 = lean_ctor_get(x_8, 2);
x_98 = lean_ctor_get(x_8, 3);
x_99 = lean_ctor_get(x_58, 0);
x_100 = lean_ctor_get(x_58, 1);
x_101 = lean_ctor_get(x_58, 2);
x_102 = lean_ctor_get(x_58, 3);
lean_ctor_set(x_58, 3, x_98);
lean_ctor_set(x_58, 2, x_97);
lean_ctor_set(x_58, 1, x_96);
lean_ctor_set(x_58, 0, x_95);
x_103 = 1;
lean_ctor_set(x_8, 3, x_58);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_103);
lean_ctor_set(x_4, 3, x_102);
lean_ctor_set(x_4, 2, x_101);
lean_ctor_set(x_4, 1, x_100);
lean_ctor_set(x_4, 0, x_99);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_103);
x_104 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_104, 0, x_8);
lean_ctor_set(x_104, 1, x_89);
lean_ctor_set(x_104, 2, x_90);
lean_ctor_set(x_104, 3, x_4);
lean_ctor_set_uint8(x_104, sizeof(void*)*4, x_87);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; 
x_105 = lean_ctor_get(x_8, 0);
x_106 = lean_ctor_get(x_8, 1);
x_107 = lean_ctor_get(x_8, 2);
x_108 = lean_ctor_get(x_8, 3);
x_109 = lean_ctor_get(x_58, 0);
x_110 = lean_ctor_get(x_58, 1);
x_111 = lean_ctor_get(x_58, 2);
x_112 = lean_ctor_get(x_58, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_58);
x_113 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_113, 0, x_105);
lean_ctor_set(x_113, 1, x_106);
lean_ctor_set(x_113, 2, x_107);
lean_ctor_set(x_113, 3, x_108);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_87);
x_114 = 1;
lean_ctor_set(x_8, 3, x_113);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_114);
lean_ctor_set(x_4, 3, x_112);
lean_ctor_set(x_4, 2, x_111);
lean_ctor_set(x_4, 1, x_110);
lean_ctor_set(x_4, 0, x_109);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_114);
x_115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_115, 0, x_8);
lean_ctor_set(x_115, 1, x_89);
lean_ctor_set(x_115, 2, x_90);
lean_ctor_set(x_115, 3, x_4);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_87);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
x_116 = lean_ctor_get(x_8, 0);
x_117 = lean_ctor_get(x_8, 1);
x_118 = lean_ctor_get(x_8, 2);
x_119 = lean_ctor_get(x_8, 3);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_8);
x_120 = lean_ctor_get(x_58, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_58, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_58, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_58, 3);
lean_inc(x_123);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 x_124 = x_58;
} else {
 lean_dec_ref(x_58);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 4, 1);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_116);
lean_ctor_set(x_125, 1, x_117);
lean_ctor_set(x_125, 2, x_118);
lean_ctor_set(x_125, 3, x_119);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_87);
x_126 = 1;
x_127 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_2);
lean_ctor_set(x_127, 2, x_3);
lean_ctor_set(x_127, 3, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_126);
lean_ctor_set(x_4, 3, x_123);
lean_ctor_set(x_4, 2, x_122);
lean_ctor_set(x_4, 1, x_121);
lean_ctor_set(x_4, 0, x_120);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_126);
x_128 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_89);
lean_ctor_set(x_128, 2, x_90);
lean_ctor_set(x_128, 3, x_4);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_87);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_129 = lean_ctor_get(x_4, 1);
x_130 = lean_ctor_get(x_4, 2);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_4);
x_131 = lean_ctor_get(x_8, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_8, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_8, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_8, 3);
lean_inc(x_134);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_135 = x_8;
} else {
 lean_dec_ref(x_8);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_58, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_58, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_58, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_58, 3);
lean_inc(x_139);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 x_140 = x_58;
} else {
 lean_dec_ref(x_58);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 4, 1);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_131);
lean_ctor_set(x_141, 1, x_132);
lean_ctor_set(x_141, 2, x_133);
lean_ctor_set(x_141, 3, x_134);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_87);
x_142 = 1;
if (lean_is_scalar(x_135)) {
 x_143 = lean_alloc_ctor(1, 4, 1);
} else {
 x_143 = x_135;
}
lean_ctor_set(x_143, 0, x_1);
lean_ctor_set(x_143, 1, x_2);
lean_ctor_set(x_143, 2, x_3);
lean_ctor_set(x_143, 3, x_141);
lean_ctor_set_uint8(x_143, sizeof(void*)*4, x_142);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_137);
lean_ctor_set(x_144, 2, x_138);
lean_ctor_set(x_144, 3, x_139);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_142);
x_145 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_129);
lean_ctor_set(x_145, 2, x_130);
lean_ctor_set(x_145, 3, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*4, x_87);
return x_145;
}
}
else
{
uint8_t x_146; 
x_146 = !lean_is_exclusive(x_4);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_ctor_get(x_4, 3);
lean_dec(x_147);
x_148 = lean_ctor_get(x_4, 0);
lean_dec(x_148);
x_149 = !lean_is_exclusive(x_8);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_8, 0);
x_151 = lean_ctor_get(x_8, 1);
x_152 = lean_ctor_get(x_8, 2);
x_153 = lean_ctor_get(x_8, 3);
lean_ctor_set(x_8, 3, x_150);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_87);
lean_ctor_set(x_4, 0, x_153);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_87);
x_154 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_154, 0, x_8);
lean_ctor_set(x_154, 1, x_151);
lean_ctor_set(x_154, 2, x_152);
lean_ctor_set(x_154, 3, x_4);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_57);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_ctor_get(x_8, 0);
x_156 = lean_ctor_get(x_8, 1);
x_157 = lean_ctor_get(x_8, 2);
x_158 = lean_ctor_get(x_8, 3);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_8);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_1);
lean_ctor_set(x_159, 1, x_2);
lean_ctor_set(x_159, 2, x_3);
lean_ctor_set(x_159, 3, x_155);
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_87);
lean_ctor_set(x_4, 0, x_158);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_87);
x_160 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_156);
lean_ctor_set(x_160, 2, x_157);
lean_ctor_set(x_160, 3, x_4);
lean_ctor_set_uint8(x_160, sizeof(void*)*4, x_57);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_161 = lean_ctor_get(x_4, 1);
x_162 = lean_ctor_get(x_4, 2);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_4);
x_163 = lean_ctor_get(x_8, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_8, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_8, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_8, 3);
lean_inc(x_166);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_167 = x_8;
} else {
 lean_dec_ref(x_8);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 4, 1);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_1);
lean_ctor_set(x_168, 1, x_2);
lean_ctor_set(x_168, 2, x_3);
lean_ctor_set(x_168, 3, x_163);
lean_ctor_set_uint8(x_168, sizeof(void*)*4, x_87);
x_169 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_161);
lean_ctor_set(x_169, 2, x_162);
lean_ctor_set(x_169, 3, x_58);
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_87);
x_170 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_164);
lean_ctor_set(x_170, 2, x_165);
lean_ctor_set(x_170, 3, x_169);
lean_ctor_set_uint8(x_170, sizeof(void*)*4, x_57);
return x_170;
}
}
}
}
else
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_4, 3);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_8);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_8, 3);
lean_dec(x_173);
x_174 = lean_ctor_get(x_8, 2);
lean_dec(x_174);
x_175 = lean_ctor_get(x_8, 1);
lean_dec(x_175);
x_176 = lean_ctor_get(x_8, 0);
lean_dec(x_176);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_171);
return x_8;
}
else
{
lean_object* x_177; 
lean_dec(x_8);
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_171);
lean_ctor_set(x_177, 1, x_2);
lean_ctor_set(x_177, 2, x_3);
lean_ctor_set(x_177, 3, x_4);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_57);
return x_177;
}
}
else
{
uint8_t x_178; 
x_178 = lean_ctor_get_uint8(x_171, sizeof(void*)*4);
if (x_178 == 0)
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_4);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_4, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_4, 0);
lean_dec(x_181);
x_182 = !lean_is_exclusive(x_171);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_183 = lean_ctor_get(x_171, 0);
x_184 = lean_ctor_get(x_171, 1);
x_185 = lean_ctor_get(x_171, 2);
x_186 = lean_ctor_get(x_171, 3);
lean_inc(x_8);
lean_ctor_set(x_171, 3, x_8);
lean_ctor_set(x_171, 2, x_3);
lean_ctor_set(x_171, 1, x_2);
lean_ctor_set(x_171, 0, x_1);
x_187 = !lean_is_exclusive(x_8);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_8, 3);
lean_dec(x_188);
x_189 = lean_ctor_get(x_8, 2);
lean_dec(x_189);
x_190 = lean_ctor_get(x_8, 1);
lean_dec(x_190);
x_191 = lean_ctor_get(x_8, 0);
lean_dec(x_191);
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_57);
lean_ctor_set(x_8, 3, x_186);
lean_ctor_set(x_8, 2, x_185);
lean_ctor_set(x_8, 1, x_184);
lean_ctor_set(x_8, 0, x_183);
lean_ctor_set(x_4, 3, x_8);
lean_ctor_set(x_4, 0, x_171);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_178);
return x_4;
}
else
{
lean_object* x_192; 
lean_dec(x_8);
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_57);
x_192 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_192, 0, x_183);
lean_ctor_set(x_192, 1, x_184);
lean_ctor_set(x_192, 2, x_185);
lean_ctor_set(x_192, 3, x_186);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_57);
lean_ctor_set(x_4, 3, x_192);
lean_ctor_set(x_4, 0, x_171);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_178);
return x_4;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_193 = lean_ctor_get(x_171, 0);
x_194 = lean_ctor_get(x_171, 1);
x_195 = lean_ctor_get(x_171, 2);
x_196 = lean_ctor_get(x_171, 3);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_171);
lean_inc(x_8);
x_197 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_197, 0, x_1);
lean_ctor_set(x_197, 1, x_2);
lean_ctor_set(x_197, 2, x_3);
lean_ctor_set(x_197, 3, x_8);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_198 = x_8;
} else {
 lean_dec_ref(x_8);
 x_198 = lean_box(0);
}
lean_ctor_set_uint8(x_197, sizeof(void*)*4, x_57);
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 4, 1);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_193);
lean_ctor_set(x_199, 1, x_194);
lean_ctor_set(x_199, 2, x_195);
lean_ctor_set(x_199, 3, x_196);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_57);
lean_ctor_set(x_4, 3, x_199);
lean_ctor_set(x_4, 0, x_197);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_178);
return x_4;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_200 = lean_ctor_get(x_4, 1);
x_201 = lean_ctor_get(x_4, 2);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_4);
x_202 = lean_ctor_get(x_171, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_171, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_171, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_171, 3);
lean_inc(x_205);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 lean_ctor_release(x_171, 3);
 x_206 = x_171;
} else {
 lean_dec_ref(x_171);
 x_206 = lean_box(0);
}
lean_inc(x_8);
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 4, 1);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_1);
lean_ctor_set(x_207, 1, x_2);
lean_ctor_set(x_207, 2, x_3);
lean_ctor_set(x_207, 3, x_8);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_208 = x_8;
} else {
 lean_dec_ref(x_8);
 x_208 = lean_box(0);
}
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_57);
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 4, 1);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_202);
lean_ctor_set(x_209, 1, x_203);
lean_ctor_set(x_209, 2, x_204);
lean_ctor_set(x_209, 3, x_205);
lean_ctor_set_uint8(x_209, sizeof(void*)*4, x_57);
x_210 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_200);
lean_ctor_set(x_210, 2, x_201);
lean_ctor_set(x_210, 3, x_209);
lean_ctor_set_uint8(x_210, sizeof(void*)*4, x_178);
return x_210;
}
}
else
{
uint8_t x_211; 
x_211 = !lean_is_exclusive(x_4);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_212 = lean_ctor_get(x_4, 3);
lean_dec(x_212);
x_213 = lean_ctor_get(x_4, 0);
lean_dec(x_213);
x_214 = !lean_is_exclusive(x_8);
if (x_214 == 0)
{
lean_object* x_215; 
lean_ctor_set_uint8(x_8, sizeof(void*)*4, x_178);
x_215 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_215, 0, x_1);
lean_ctor_set(x_215, 1, x_2);
lean_ctor_set(x_215, 2, x_3);
lean_ctor_set(x_215, 3, x_4);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_178);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_216 = lean_ctor_get(x_8, 0);
x_217 = lean_ctor_get(x_8, 1);
x_218 = lean_ctor_get(x_8, 2);
x_219 = lean_ctor_get(x_8, 3);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_8);
x_220 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_220, 0, x_216);
lean_ctor_set(x_220, 1, x_217);
lean_ctor_set(x_220, 2, x_218);
lean_ctor_set(x_220, 3, x_219);
lean_ctor_set_uint8(x_220, sizeof(void*)*4, x_178);
lean_ctor_set(x_4, 0, x_220);
x_221 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_221, 0, x_1);
lean_ctor_set(x_221, 1, x_2);
lean_ctor_set(x_221, 2, x_3);
lean_ctor_set(x_221, 3, x_4);
lean_ctor_set_uint8(x_221, sizeof(void*)*4, x_178);
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_222 = lean_ctor_get(x_4, 1);
x_223 = lean_ctor_get(x_4, 2);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_4);
x_224 = lean_ctor_get(x_8, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_8, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_8, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_8, 3);
lean_inc(x_227);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_228 = x_8;
} else {
 lean_dec_ref(x_8);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 4, 1);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_224);
lean_ctor_set(x_229, 1, x_225);
lean_ctor_set(x_229, 2, x_226);
lean_ctor_set(x_229, 3, x_227);
lean_ctor_set_uint8(x_229, sizeof(void*)*4, x_178);
x_230 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_222);
lean_ctor_set(x_230, 2, x_223);
lean_ctor_set(x_230, 3, x_171);
lean_ctor_set_uint8(x_230, sizeof(void*)*4, x_7);
x_231 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_231, 0, x_1);
lean_ctor_set(x_231, 1, x_2);
lean_ctor_set(x_231, 2, x_3);
lean_ctor_set(x_231, 3, x_230);
lean_ctor_set_uint8(x_231, sizeof(void*)*4, x_178);
return x_231;
}
}
}
}
}
}
else
{
lean_object* x_232; 
x_232 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_232, 0, x_1);
lean_ctor_set(x_232, 1, x_2);
lean_ctor_set(x_232, 2, x_3);
lean_ctor_set(x_232, 3, x_4);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_7);
return x_232;
}
}
}
else
{
uint8_t x_233; 
x_233 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_233 == 0)
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_1, 0);
lean_inc(x_234);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_1, 3);
lean_inc(x_235);
if (lean_obj_tag(x_235) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_236; 
x_236 = !lean_is_exclusive(x_1);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; lean_object* x_240; 
x_237 = lean_ctor_get(x_1, 3);
lean_dec(x_237);
x_238 = lean_ctor_get(x_1, 0);
lean_dec(x_238);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 0, x_4);
x_239 = 1;
x_240 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_240, 0, x_1);
lean_ctor_set(x_240, 1, x_2);
lean_ctor_set(x_240, 2, x_3);
lean_ctor_set(x_240, 3, x_4);
lean_ctor_set_uint8(x_240, sizeof(void*)*4, x_239);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; 
x_241 = lean_ctor_get(x_1, 1);
x_242 = lean_ctor_get(x_1, 2);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_1);
x_243 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_243, 0, x_4);
lean_ctor_set(x_243, 1, x_241);
lean_ctor_set(x_243, 2, x_242);
lean_ctor_set(x_243, 3, x_4);
lean_ctor_set_uint8(x_243, sizeof(void*)*4, x_233);
x_244 = 1;
x_245 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_2);
lean_ctor_set(x_245, 2, x_3);
lean_ctor_set(x_245, 3, x_4);
lean_ctor_set_uint8(x_245, sizeof(void*)*4, x_244);
return x_245;
}
}
else
{
uint8_t x_246; 
x_246 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_246 == 0)
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_4, 0);
lean_inc(x_247);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_4, 3);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
uint8_t x_249; 
x_249 = !lean_is_exclusive(x_1);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_250 = lean_ctor_get(x_1, 1);
x_251 = lean_ctor_get(x_1, 2);
x_252 = lean_ctor_get(x_1, 3);
lean_dec(x_252);
x_253 = lean_ctor_get(x_1, 0);
lean_dec(x_253);
x_254 = !lean_is_exclusive(x_4);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; 
x_255 = lean_ctor_get(x_4, 1);
x_256 = lean_ctor_get(x_4, 2);
x_257 = lean_ctor_get(x_4, 3);
lean_dec(x_257);
x_258 = lean_ctor_get(x_4, 0);
lean_dec(x_258);
lean_ctor_set(x_4, 2, x_251);
lean_ctor_set(x_4, 1, x_250);
lean_ctor_set(x_4, 0, x_248);
lean_ctor_set(x_1, 3, x_248);
lean_ctor_set(x_1, 2, x_256);
lean_ctor_set(x_1, 1, x_255);
lean_ctor_set(x_1, 0, x_248);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
x_259 = 1;
x_260 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_260, 0, x_4);
lean_ctor_set(x_260, 1, x_2);
lean_ctor_set(x_260, 2, x_3);
lean_ctor_set(x_260, 3, x_1);
lean_ctor_set_uint8(x_260, sizeof(void*)*4, x_259);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; lean_object* x_265; 
x_261 = lean_ctor_get(x_4, 1);
x_262 = lean_ctor_get(x_4, 2);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_4);
x_263 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_263, 0, x_248);
lean_ctor_set(x_263, 1, x_250);
lean_ctor_set(x_263, 2, x_251);
lean_ctor_set(x_263, 3, x_248);
lean_ctor_set_uint8(x_263, sizeof(void*)*4, x_246);
lean_ctor_set(x_1, 3, x_248);
lean_ctor_set(x_1, 2, x_262);
lean_ctor_set(x_1, 1, x_261);
lean_ctor_set(x_1, 0, x_248);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
x_264 = 1;
x_265 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_2);
lean_ctor_set(x_265, 2, x_3);
lean_ctor_set(x_265, 3, x_1);
lean_ctor_set_uint8(x_265, sizeof(void*)*4, x_264);
return x_265;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; 
x_266 = lean_ctor_get(x_1, 1);
x_267 = lean_ctor_get(x_1, 2);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_1);
x_268 = lean_ctor_get(x_4, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_4, 2);
lean_inc(x_269);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_270 = x_4;
} else {
 lean_dec_ref(x_4);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 4, 1);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_248);
lean_ctor_set(x_271, 1, x_266);
lean_ctor_set(x_271, 2, x_267);
lean_ctor_set(x_271, 3, x_248);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_246);
x_272 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_272, 0, x_248);
lean_ctor_set(x_272, 1, x_268);
lean_ctor_set(x_272, 2, x_269);
lean_ctor_set(x_272, 3, x_248);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_246);
x_273 = 1;
x_274 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_2);
lean_ctor_set(x_274, 2, x_3);
lean_ctor_set(x_274, 3, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_273);
return x_274;
}
}
else
{
uint8_t x_275; 
x_275 = lean_ctor_get_uint8(x_248, sizeof(void*)*4);
if (x_275 == 0)
{
uint8_t x_276; 
x_276 = !lean_is_exclusive(x_1);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_277 = lean_ctor_get(x_1, 1);
x_278 = lean_ctor_get(x_1, 2);
x_279 = lean_ctor_get(x_1, 3);
lean_dec(x_279);
x_280 = lean_ctor_get(x_1, 0);
lean_dec(x_280);
x_281 = !lean_is_exclusive(x_4);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_282 = lean_ctor_get(x_4, 1);
x_283 = lean_ctor_get(x_4, 2);
x_284 = lean_ctor_get(x_4, 3);
lean_dec(x_284);
x_285 = lean_ctor_get(x_4, 0);
lean_dec(x_285);
x_286 = !lean_is_exclusive(x_248);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; 
x_287 = lean_ctor_get(x_248, 0);
x_288 = lean_ctor_get(x_248, 1);
x_289 = lean_ctor_get(x_248, 2);
x_290 = lean_ctor_get(x_248, 3);
lean_ctor_set(x_248, 3, x_247);
lean_ctor_set(x_248, 2, x_278);
lean_ctor_set(x_248, 1, x_277);
lean_ctor_set(x_248, 0, x_247);
x_291 = 1;
lean_ctor_set(x_4, 3, x_247);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_248);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_291);
lean_ctor_set(x_1, 3, x_290);
lean_ctor_set(x_1, 2, x_289);
lean_ctor_set(x_1, 1, x_288);
lean_ctor_set(x_1, 0, x_287);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_291);
x_292 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_292, 0, x_4);
lean_ctor_set(x_292, 1, x_282);
lean_ctor_set(x_292, 2, x_283);
lean_ctor_set(x_292, 3, x_1);
lean_ctor_set_uint8(x_292, sizeof(void*)*4, x_275);
return x_292;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; lean_object* x_299; 
x_293 = lean_ctor_get(x_248, 0);
x_294 = lean_ctor_get(x_248, 1);
x_295 = lean_ctor_get(x_248, 2);
x_296 = lean_ctor_get(x_248, 3);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_248);
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_247);
lean_ctor_set(x_297, 1, x_277);
lean_ctor_set(x_297, 2, x_278);
lean_ctor_set(x_297, 3, x_247);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_275);
x_298 = 1;
lean_ctor_set(x_4, 3, x_247);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_297);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_298);
lean_ctor_set(x_1, 3, x_296);
lean_ctor_set(x_1, 2, x_295);
lean_ctor_set(x_1, 1, x_294);
lean_ctor_set(x_1, 0, x_293);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_298);
x_299 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_299, 0, x_4);
lean_ctor_set(x_299, 1, x_282);
lean_ctor_set(x_299, 2, x_283);
lean_ctor_set(x_299, 3, x_1);
lean_ctor_set_uint8(x_299, sizeof(void*)*4, x_275);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; lean_object* x_309; lean_object* x_310; 
x_300 = lean_ctor_get(x_4, 1);
x_301 = lean_ctor_get(x_4, 2);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_4);
x_302 = lean_ctor_get(x_248, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_248, 1);
lean_inc(x_303);
x_304 = lean_ctor_get(x_248, 2);
lean_inc(x_304);
x_305 = lean_ctor_get(x_248, 3);
lean_inc(x_305);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 lean_ctor_release(x_248, 2);
 lean_ctor_release(x_248, 3);
 x_306 = x_248;
} else {
 lean_dec_ref(x_248);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 4, 1);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_247);
lean_ctor_set(x_307, 1, x_277);
lean_ctor_set(x_307, 2, x_278);
lean_ctor_set(x_307, 3, x_247);
lean_ctor_set_uint8(x_307, sizeof(void*)*4, x_275);
x_308 = 1;
x_309 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_2);
lean_ctor_set(x_309, 2, x_3);
lean_ctor_set(x_309, 3, x_247);
lean_ctor_set_uint8(x_309, sizeof(void*)*4, x_308);
lean_ctor_set(x_1, 3, x_305);
lean_ctor_set(x_1, 2, x_304);
lean_ctor_set(x_1, 1, x_303);
lean_ctor_set(x_1, 0, x_302);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_308);
x_310 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_300);
lean_ctor_set(x_310, 2, x_301);
lean_ctor_set(x_310, 3, x_1);
lean_ctor_set_uint8(x_310, sizeof(void*)*4, x_275);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_311 = lean_ctor_get(x_1, 1);
x_312 = lean_ctor_get(x_1, 2);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_1);
x_313 = lean_ctor_get(x_4, 1);
lean_inc(x_313);
x_314 = lean_ctor_get(x_4, 2);
lean_inc(x_314);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_315 = x_4;
} else {
 lean_dec_ref(x_4);
 x_315 = lean_box(0);
}
x_316 = lean_ctor_get(x_248, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_248, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_248, 2);
lean_inc(x_318);
x_319 = lean_ctor_get(x_248, 3);
lean_inc(x_319);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 lean_ctor_release(x_248, 2);
 lean_ctor_release(x_248, 3);
 x_320 = x_248;
} else {
 lean_dec_ref(x_248);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 4, 1);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_247);
lean_ctor_set(x_321, 1, x_311);
lean_ctor_set(x_321, 2, x_312);
lean_ctor_set(x_321, 3, x_247);
lean_ctor_set_uint8(x_321, sizeof(void*)*4, x_275);
x_322 = 1;
if (lean_is_scalar(x_315)) {
 x_323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_323 = x_315;
}
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_2);
lean_ctor_set(x_323, 2, x_3);
lean_ctor_set(x_323, 3, x_247);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_322);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_316);
lean_ctor_set(x_324, 1, x_317);
lean_ctor_set(x_324, 2, x_318);
lean_ctor_set(x_324, 3, x_319);
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_322);
x_325 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_313);
lean_ctor_set(x_325, 2, x_314);
lean_ctor_set(x_325, 3, x_324);
lean_ctor_set_uint8(x_325, sizeof(void*)*4, x_275);
return x_325;
}
}
else
{
uint8_t x_326; 
x_326 = !lean_is_exclusive(x_248);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_327 = lean_ctor_get(x_248, 3);
lean_dec(x_327);
x_328 = lean_ctor_get(x_248, 2);
lean_dec(x_328);
x_329 = lean_ctor_get(x_248, 1);
lean_dec(x_329);
x_330 = lean_ctor_get(x_248, 0);
lean_dec(x_330);
x_331 = !lean_is_exclusive(x_1);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_332 = lean_ctor_get(x_1, 1);
x_333 = lean_ctor_get(x_1, 2);
x_334 = lean_ctor_get(x_1, 3);
lean_dec(x_334);
x_335 = lean_ctor_get(x_1, 0);
lean_dec(x_335);
lean_ctor_set(x_248, 3, x_247);
lean_ctor_set(x_248, 2, x_333);
lean_ctor_set(x_248, 1, x_332);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_246);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_248);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_275);
return x_1;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_1, 1);
x_337 = lean_ctor_get(x_1, 2);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_1);
lean_ctor_set(x_248, 3, x_247);
lean_ctor_set(x_248, 2, x_337);
lean_ctor_set(x_248, 1, x_336);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_246);
x_338 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_338, 0, x_248);
lean_ctor_set(x_338, 1, x_2);
lean_ctor_set(x_338, 2, x_3);
lean_ctor_set(x_338, 3, x_4);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_275);
return x_338;
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_248);
x_339 = lean_ctor_get(x_1, 1);
lean_inc(x_339);
x_340 = lean_ctor_get(x_1, 2);
lean_inc(x_340);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_341 = x_1;
} else {
 lean_dec_ref(x_1);
 x_341 = lean_box(0);
}
x_342 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_342, 0, x_247);
lean_ctor_set(x_342, 1, x_339);
lean_ctor_set(x_342, 2, x_340);
lean_ctor_set(x_342, 3, x_247);
lean_ctor_set_uint8(x_342, sizeof(void*)*4, x_246);
if (lean_is_scalar(x_341)) {
 x_343 = lean_alloc_ctor(1, 4, 1);
} else {
 x_343 = x_341;
}
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_2);
lean_ctor_set(x_343, 2, x_3);
lean_ctor_set(x_343, 3, x_4);
lean_ctor_set_uint8(x_343, sizeof(void*)*4, x_275);
return x_343;
}
}
}
}
else
{
uint8_t x_344; 
x_344 = lean_ctor_get_uint8(x_247, sizeof(void*)*4);
if (x_344 == 0)
{
lean_object* x_345; 
x_345 = lean_ctor_get(x_4, 3);
lean_inc(x_345);
if (lean_obj_tag(x_345) == 0)
{
uint8_t x_346; 
x_346 = !lean_is_exclusive(x_1);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; 
x_347 = lean_ctor_get(x_1, 1);
x_348 = lean_ctor_get(x_1, 2);
x_349 = lean_ctor_get(x_1, 3);
lean_dec(x_349);
x_350 = lean_ctor_get(x_1, 0);
lean_dec(x_350);
x_351 = !lean_is_exclusive(x_4);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; 
x_352 = lean_ctor_get(x_4, 1);
x_353 = lean_ctor_get(x_4, 2);
x_354 = lean_ctor_get(x_4, 3);
lean_dec(x_354);
x_355 = lean_ctor_get(x_4, 0);
lean_dec(x_355);
x_356 = !lean_is_exclusive(x_247);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; lean_object* x_362; 
x_357 = lean_ctor_get(x_247, 0);
x_358 = lean_ctor_get(x_247, 1);
x_359 = lean_ctor_get(x_247, 2);
x_360 = lean_ctor_get(x_247, 3);
lean_ctor_set(x_247, 3, x_345);
lean_ctor_set(x_247, 2, x_348);
lean_ctor_set(x_247, 1, x_347);
lean_ctor_set(x_247, 0, x_345);
x_361 = 1;
lean_ctor_set(x_4, 3, x_357);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_361);
lean_ctor_set(x_1, 3, x_345);
lean_ctor_set(x_1, 2, x_353);
lean_ctor_set(x_1, 1, x_352);
lean_ctor_set(x_1, 0, x_360);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_361);
x_362 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_362, 0, x_4);
lean_ctor_set(x_362, 1, x_358);
lean_ctor_set(x_362, 2, x_359);
lean_ctor_set(x_362, 3, x_1);
lean_ctor_set_uint8(x_362, sizeof(void*)*4, x_344);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; 
x_363 = lean_ctor_get(x_247, 0);
x_364 = lean_ctor_get(x_247, 1);
x_365 = lean_ctor_get(x_247, 2);
x_366 = lean_ctor_get(x_247, 3);
lean_inc(x_366);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_247);
x_367 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_367, 0, x_345);
lean_ctor_set(x_367, 1, x_347);
lean_ctor_set(x_367, 2, x_348);
lean_ctor_set(x_367, 3, x_345);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_344);
x_368 = 1;
lean_ctor_set(x_4, 3, x_363);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_367);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_368);
lean_ctor_set(x_1, 3, x_345);
lean_ctor_set(x_1, 2, x_353);
lean_ctor_set(x_1, 1, x_352);
lean_ctor_set(x_1, 0, x_366);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_368);
x_369 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_369, 0, x_4);
lean_ctor_set(x_369, 1, x_364);
lean_ctor_set(x_369, 2, x_365);
lean_ctor_set(x_369, 3, x_1);
lean_ctor_set_uint8(x_369, sizeof(void*)*4, x_344);
return x_369;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; lean_object* x_379; lean_object* x_380; 
x_370 = lean_ctor_get(x_4, 1);
x_371 = lean_ctor_get(x_4, 2);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_4);
x_372 = lean_ctor_get(x_247, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_247, 1);
lean_inc(x_373);
x_374 = lean_ctor_get(x_247, 2);
lean_inc(x_374);
x_375 = lean_ctor_get(x_247, 3);
lean_inc(x_375);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 x_376 = x_247;
} else {
 lean_dec_ref(x_247);
 x_376 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_377 = lean_alloc_ctor(1, 4, 1);
} else {
 x_377 = x_376;
}
lean_ctor_set(x_377, 0, x_345);
lean_ctor_set(x_377, 1, x_347);
lean_ctor_set(x_377, 2, x_348);
lean_ctor_set(x_377, 3, x_345);
lean_ctor_set_uint8(x_377, sizeof(void*)*4, x_344);
x_378 = 1;
x_379 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_2);
lean_ctor_set(x_379, 2, x_3);
lean_ctor_set(x_379, 3, x_372);
lean_ctor_set_uint8(x_379, sizeof(void*)*4, x_378);
lean_ctor_set(x_1, 3, x_345);
lean_ctor_set(x_1, 2, x_371);
lean_ctor_set(x_1, 1, x_370);
lean_ctor_set(x_1, 0, x_375);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_378);
x_380 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_373);
lean_ctor_set(x_380, 2, x_374);
lean_ctor_set(x_380, 3, x_1);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_344);
return x_380;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_381 = lean_ctor_get(x_1, 1);
x_382 = lean_ctor_get(x_1, 2);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_1);
x_383 = lean_ctor_get(x_4, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_4, 2);
lean_inc(x_384);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_385 = x_4;
} else {
 lean_dec_ref(x_4);
 x_385 = lean_box(0);
}
x_386 = lean_ctor_get(x_247, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_247, 1);
lean_inc(x_387);
x_388 = lean_ctor_get(x_247, 2);
lean_inc(x_388);
x_389 = lean_ctor_get(x_247, 3);
lean_inc(x_389);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 x_390 = x_247;
} else {
 lean_dec_ref(x_247);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(1, 4, 1);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_345);
lean_ctor_set(x_391, 1, x_381);
lean_ctor_set(x_391, 2, x_382);
lean_ctor_set(x_391, 3, x_345);
lean_ctor_set_uint8(x_391, sizeof(void*)*4, x_344);
x_392 = 1;
if (lean_is_scalar(x_385)) {
 x_393 = lean_alloc_ctor(1, 4, 1);
} else {
 x_393 = x_385;
}
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_2);
lean_ctor_set(x_393, 2, x_3);
lean_ctor_set(x_393, 3, x_386);
lean_ctor_set_uint8(x_393, sizeof(void*)*4, x_392);
x_394 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_394, 0, x_389);
lean_ctor_set(x_394, 1, x_383);
lean_ctor_set(x_394, 2, x_384);
lean_ctor_set(x_394, 3, x_345);
lean_ctor_set_uint8(x_394, sizeof(void*)*4, x_392);
x_395 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_387);
lean_ctor_set(x_395, 2, x_388);
lean_ctor_set(x_395, 3, x_394);
lean_ctor_set_uint8(x_395, sizeof(void*)*4, x_344);
return x_395;
}
}
else
{
uint8_t x_396; 
x_396 = lean_ctor_get_uint8(x_345, sizeof(void*)*4);
if (x_396 == 0)
{
uint8_t x_397; 
x_397 = !lean_is_exclusive(x_1);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; 
x_398 = lean_ctor_get(x_1, 1);
x_399 = lean_ctor_get(x_1, 2);
x_400 = lean_ctor_get(x_1, 3);
lean_dec(x_400);
x_401 = lean_ctor_get(x_1, 0);
lean_dec(x_401);
x_402 = !lean_is_exclusive(x_4);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; 
x_403 = lean_ctor_get(x_4, 1);
x_404 = lean_ctor_get(x_4, 2);
x_405 = lean_ctor_get(x_4, 3);
lean_dec(x_405);
x_406 = lean_ctor_get(x_4, 0);
lean_dec(x_406);
x_407 = !lean_is_exclusive(x_247);
if (x_407 == 0)
{
uint8_t x_408; 
x_408 = !lean_is_exclusive(x_345);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; lean_object* x_414; 
x_409 = lean_ctor_get(x_345, 0);
x_410 = lean_ctor_get(x_345, 1);
x_411 = lean_ctor_get(x_345, 2);
x_412 = lean_ctor_get(x_345, 3);
lean_ctor_set(x_345, 3, x_235);
lean_ctor_set(x_345, 2, x_399);
lean_ctor_set(x_345, 1, x_398);
lean_ctor_set(x_345, 0, x_235);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_396);
x_413 = 1;
lean_ctor_set(x_4, 3, x_247);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_345);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_413);
lean_ctor_set(x_1, 3, x_412);
lean_ctor_set(x_1, 2, x_411);
lean_ctor_set(x_1, 1, x_410);
lean_ctor_set(x_1, 0, x_409);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_413);
x_414 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_414, 0, x_4);
lean_ctor_set(x_414, 1, x_403);
lean_ctor_set(x_414, 2, x_404);
lean_ctor_set(x_414, 3, x_1);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_396);
return x_414;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; lean_object* x_421; 
x_415 = lean_ctor_get(x_345, 0);
x_416 = lean_ctor_get(x_345, 1);
x_417 = lean_ctor_get(x_345, 2);
x_418 = lean_ctor_get(x_345, 3);
lean_inc(x_418);
lean_inc(x_417);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_345);
x_419 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_419, 0, x_235);
lean_ctor_set(x_419, 1, x_398);
lean_ctor_set(x_419, 2, x_399);
lean_ctor_set(x_419, 3, x_235);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_396);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_396);
x_420 = 1;
lean_ctor_set(x_4, 3, x_247);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_419);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_420);
lean_ctor_set(x_1, 3, x_418);
lean_ctor_set(x_1, 2, x_417);
lean_ctor_set(x_1, 1, x_416);
lean_ctor_set(x_1, 0, x_415);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_420);
x_421 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_421, 0, x_4);
lean_ctor_set(x_421, 1, x_403);
lean_ctor_set(x_421, 2, x_404);
lean_ctor_set(x_421, 3, x_1);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_396);
return x_421;
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; lean_object* x_434; 
x_422 = lean_ctor_get(x_247, 0);
x_423 = lean_ctor_get(x_247, 1);
x_424 = lean_ctor_get(x_247, 2);
x_425 = lean_ctor_get(x_247, 3);
lean_inc(x_425);
lean_inc(x_424);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_247);
x_426 = lean_ctor_get(x_345, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_345, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_345, 2);
lean_inc(x_428);
x_429 = lean_ctor_get(x_345, 3);
lean_inc(x_429);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 x_430 = x_345;
} else {
 lean_dec_ref(x_345);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 4, 1);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_235);
lean_ctor_set(x_431, 1, x_398);
lean_ctor_set(x_431, 2, x_399);
lean_ctor_set(x_431, 3, x_235);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_396);
x_432 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_432, 0, x_422);
lean_ctor_set(x_432, 1, x_423);
lean_ctor_set(x_432, 2, x_424);
lean_ctor_set(x_432, 3, x_425);
lean_ctor_set_uint8(x_432, sizeof(void*)*4, x_396);
x_433 = 1;
lean_ctor_set(x_4, 3, x_432);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_431);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_433);
lean_ctor_set(x_1, 3, x_429);
lean_ctor_set(x_1, 2, x_428);
lean_ctor_set(x_1, 1, x_427);
lean_ctor_set(x_1, 0, x_426);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_433);
x_434 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_434, 0, x_4);
lean_ctor_set(x_434, 1, x_403);
lean_ctor_set(x_434, 2, x_404);
lean_ctor_set(x_434, 3, x_1);
lean_ctor_set_uint8(x_434, sizeof(void*)*4, x_396);
return x_434;
}
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; lean_object* x_451; 
x_435 = lean_ctor_get(x_4, 1);
x_436 = lean_ctor_get(x_4, 2);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_4);
x_437 = lean_ctor_get(x_247, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_247, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_247, 2);
lean_inc(x_439);
x_440 = lean_ctor_get(x_247, 3);
lean_inc(x_440);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 x_441 = x_247;
} else {
 lean_dec_ref(x_247);
 x_441 = lean_box(0);
}
x_442 = lean_ctor_get(x_345, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_345, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_345, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_345, 3);
lean_inc(x_445);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 x_446 = x_345;
} else {
 lean_dec_ref(x_345);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(1, 4, 1);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_235);
lean_ctor_set(x_447, 1, x_398);
lean_ctor_set(x_447, 2, x_399);
lean_ctor_set(x_447, 3, x_235);
lean_ctor_set_uint8(x_447, sizeof(void*)*4, x_396);
if (lean_is_scalar(x_441)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_441;
}
lean_ctor_set(x_448, 0, x_437);
lean_ctor_set(x_448, 1, x_438);
lean_ctor_set(x_448, 2, x_439);
lean_ctor_set(x_448, 3, x_440);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_396);
x_449 = 1;
x_450 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_450, 0, x_447);
lean_ctor_set(x_450, 1, x_2);
lean_ctor_set(x_450, 2, x_3);
lean_ctor_set(x_450, 3, x_448);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
lean_ctor_set(x_1, 3, x_445);
lean_ctor_set(x_1, 2, x_444);
lean_ctor_set(x_1, 1, x_443);
lean_ctor_set(x_1, 0, x_442);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_449);
x_451 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_435);
lean_ctor_set(x_451, 2, x_436);
lean_ctor_set(x_451, 3, x_1);
lean_ctor_set_uint8(x_451, sizeof(void*)*4, x_396);
return x_451;
}
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_452 = lean_ctor_get(x_1, 1);
x_453 = lean_ctor_get(x_1, 2);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_1);
x_454 = lean_ctor_get(x_4, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_4, 2);
lean_inc(x_455);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_456 = x_4;
} else {
 lean_dec_ref(x_4);
 x_456 = lean_box(0);
}
x_457 = lean_ctor_get(x_247, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_247, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_247, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_247, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 x_461 = x_247;
} else {
 lean_dec_ref(x_247);
 x_461 = lean_box(0);
}
x_462 = lean_ctor_get(x_345, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_345, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_345, 2);
lean_inc(x_464);
x_465 = lean_ctor_get(x_345, 3);
lean_inc(x_465);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 x_466 = x_345;
} else {
 lean_dec_ref(x_345);
 x_466 = lean_box(0);
}
if (lean_is_scalar(x_466)) {
 x_467 = lean_alloc_ctor(1, 4, 1);
} else {
 x_467 = x_466;
}
lean_ctor_set(x_467, 0, x_235);
lean_ctor_set(x_467, 1, x_452);
lean_ctor_set(x_467, 2, x_453);
lean_ctor_set(x_467, 3, x_235);
lean_ctor_set_uint8(x_467, sizeof(void*)*4, x_396);
if (lean_is_scalar(x_461)) {
 x_468 = lean_alloc_ctor(1, 4, 1);
} else {
 x_468 = x_461;
}
lean_ctor_set(x_468, 0, x_457);
lean_ctor_set(x_468, 1, x_458);
lean_ctor_set(x_468, 2, x_459);
lean_ctor_set(x_468, 3, x_460);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_396);
x_469 = 1;
if (lean_is_scalar(x_456)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_456;
}
lean_ctor_set(x_470, 0, x_467);
lean_ctor_set(x_470, 1, x_2);
lean_ctor_set(x_470, 2, x_3);
lean_ctor_set(x_470, 3, x_468);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
x_471 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_471, 0, x_462);
lean_ctor_set(x_471, 1, x_463);
lean_ctor_set(x_471, 2, x_464);
lean_ctor_set(x_471, 3, x_465);
lean_ctor_set_uint8(x_471, sizeof(void*)*4, x_469);
x_472 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_454);
lean_ctor_set(x_472, 2, x_455);
lean_ctor_set(x_472, 3, x_471);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_396);
return x_472;
}
}
else
{
uint8_t x_473; 
x_473 = !lean_is_exclusive(x_1);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; 
x_474 = lean_ctor_get(x_1, 1);
x_475 = lean_ctor_get(x_1, 2);
x_476 = lean_ctor_get(x_1, 3);
lean_dec(x_476);
x_477 = lean_ctor_get(x_1, 0);
lean_dec(x_477);
x_478 = !lean_is_exclusive(x_4);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; 
x_479 = lean_ctor_get(x_4, 1);
x_480 = lean_ctor_get(x_4, 2);
x_481 = lean_ctor_get(x_4, 3);
lean_dec(x_481);
x_482 = lean_ctor_get(x_4, 0);
lean_dec(x_482);
x_483 = !lean_is_exclusive(x_247);
if (x_483 == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_484 = lean_ctor_get(x_247, 0);
x_485 = lean_ctor_get(x_247, 1);
x_486 = lean_ctor_get(x_247, 2);
x_487 = lean_ctor_get(x_247, 3);
lean_ctor_set(x_247, 3, x_235);
lean_ctor_set(x_247, 2, x_475);
lean_ctor_set(x_247, 1, x_474);
lean_ctor_set(x_247, 0, x_235);
lean_ctor_set(x_4, 3, x_484);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_396);
lean_ctor_set(x_1, 3, x_345);
lean_ctor_set(x_1, 2, x_480);
lean_ctor_set(x_1, 1, x_479);
lean_ctor_set(x_1, 0, x_487);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_396);
x_488 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_488, 0, x_4);
lean_ctor_set(x_488, 1, x_485);
lean_ctor_set(x_488, 2, x_486);
lean_ctor_set(x_488, 3, x_1);
lean_ctor_set_uint8(x_488, sizeof(void*)*4, x_344);
return x_488;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_489 = lean_ctor_get(x_247, 0);
x_490 = lean_ctor_get(x_247, 1);
x_491 = lean_ctor_get(x_247, 2);
x_492 = lean_ctor_get(x_247, 3);
lean_inc(x_492);
lean_inc(x_491);
lean_inc(x_490);
lean_inc(x_489);
lean_dec(x_247);
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_235);
lean_ctor_set(x_493, 1, x_474);
lean_ctor_set(x_493, 2, x_475);
lean_ctor_set(x_493, 3, x_235);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_344);
lean_ctor_set(x_4, 3, x_489);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_493);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_396);
lean_ctor_set(x_1, 3, x_345);
lean_ctor_set(x_1, 2, x_480);
lean_ctor_set(x_1, 1, x_479);
lean_ctor_set(x_1, 0, x_492);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_396);
x_494 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_494, 0, x_4);
lean_ctor_set(x_494, 1, x_490);
lean_ctor_set(x_494, 2, x_491);
lean_ctor_set(x_494, 3, x_1);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_344);
return x_494;
}
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_495 = lean_ctor_get(x_4, 1);
x_496 = lean_ctor_get(x_4, 2);
lean_inc(x_496);
lean_inc(x_495);
lean_dec(x_4);
x_497 = lean_ctor_get(x_247, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_247, 1);
lean_inc(x_498);
x_499 = lean_ctor_get(x_247, 2);
lean_inc(x_499);
x_500 = lean_ctor_get(x_247, 3);
lean_inc(x_500);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 x_501 = x_247;
} else {
 lean_dec_ref(x_247);
 x_501 = lean_box(0);
}
if (lean_is_scalar(x_501)) {
 x_502 = lean_alloc_ctor(1, 4, 1);
} else {
 x_502 = x_501;
}
lean_ctor_set(x_502, 0, x_235);
lean_ctor_set(x_502, 1, x_474);
lean_ctor_set(x_502, 2, x_475);
lean_ctor_set(x_502, 3, x_235);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_344);
x_503 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_2);
lean_ctor_set(x_503, 2, x_3);
lean_ctor_set(x_503, 3, x_497);
lean_ctor_set_uint8(x_503, sizeof(void*)*4, x_396);
lean_ctor_set(x_1, 3, x_345);
lean_ctor_set(x_1, 2, x_496);
lean_ctor_set(x_1, 1, x_495);
lean_ctor_set(x_1, 0, x_500);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_396);
x_504 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_504, 0, x_503);
lean_ctor_set(x_504, 1, x_498);
lean_ctor_set(x_504, 2, x_499);
lean_ctor_set(x_504, 3, x_1);
lean_ctor_set_uint8(x_504, sizeof(void*)*4, x_344);
return x_504;
}
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_505 = lean_ctor_get(x_1, 1);
x_506 = lean_ctor_get(x_1, 2);
lean_inc(x_506);
lean_inc(x_505);
lean_dec(x_1);
x_507 = lean_ctor_get(x_4, 1);
lean_inc(x_507);
x_508 = lean_ctor_get(x_4, 2);
lean_inc(x_508);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_509 = x_4;
} else {
 lean_dec_ref(x_4);
 x_509 = lean_box(0);
}
x_510 = lean_ctor_get(x_247, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_247, 1);
lean_inc(x_511);
x_512 = lean_ctor_get(x_247, 2);
lean_inc(x_512);
x_513 = lean_ctor_get(x_247, 3);
lean_inc(x_513);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 x_514 = x_247;
} else {
 lean_dec_ref(x_247);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(1, 4, 1);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_235);
lean_ctor_set(x_515, 1, x_505);
lean_ctor_set(x_515, 2, x_506);
lean_ctor_set(x_515, 3, x_235);
lean_ctor_set_uint8(x_515, sizeof(void*)*4, x_344);
if (lean_is_scalar(x_509)) {
 x_516 = lean_alloc_ctor(1, 4, 1);
} else {
 x_516 = x_509;
}
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_2);
lean_ctor_set(x_516, 2, x_3);
lean_ctor_set(x_516, 3, x_510);
lean_ctor_set_uint8(x_516, sizeof(void*)*4, x_396);
x_517 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_517, 0, x_513);
lean_ctor_set(x_517, 1, x_507);
lean_ctor_set(x_517, 2, x_508);
lean_ctor_set(x_517, 3, x_345);
lean_ctor_set_uint8(x_517, sizeof(void*)*4, x_396);
x_518 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_511);
lean_ctor_set(x_518, 2, x_512);
lean_ctor_set(x_518, 3, x_517);
lean_ctor_set_uint8(x_518, sizeof(void*)*4, x_344);
return x_518;
}
}
}
}
else
{
lean_object* x_519; 
x_519 = lean_ctor_get(x_4, 3);
lean_inc(x_519);
if (lean_obj_tag(x_519) == 0)
{
uint8_t x_520; 
x_520 = !lean_is_exclusive(x_247);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; uint8_t x_525; 
x_521 = lean_ctor_get(x_247, 3);
lean_dec(x_521);
x_522 = lean_ctor_get(x_247, 2);
lean_dec(x_522);
x_523 = lean_ctor_get(x_247, 1);
lean_dec(x_523);
x_524 = lean_ctor_get(x_247, 0);
lean_dec(x_524);
x_525 = !lean_is_exclusive(x_1);
if (x_525 == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_526 = lean_ctor_get(x_1, 1);
x_527 = lean_ctor_get(x_1, 2);
x_528 = lean_ctor_get(x_1, 3);
lean_dec(x_528);
x_529 = lean_ctor_get(x_1, 0);
lean_dec(x_529);
lean_ctor_set(x_247, 3, x_519);
lean_ctor_set(x_247, 2, x_527);
lean_ctor_set(x_247, 1, x_526);
lean_ctor_set(x_247, 0, x_519);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_247);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_344);
return x_1;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_530 = lean_ctor_get(x_1, 1);
x_531 = lean_ctor_get(x_1, 2);
lean_inc(x_531);
lean_inc(x_530);
lean_dec(x_1);
lean_ctor_set(x_247, 3, x_519);
lean_ctor_set(x_247, 2, x_531);
lean_ctor_set(x_247, 1, x_530);
lean_ctor_set(x_247, 0, x_519);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
x_532 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_532, 0, x_247);
lean_ctor_set(x_532, 1, x_2);
lean_ctor_set(x_532, 2, x_3);
lean_ctor_set(x_532, 3, x_4);
lean_ctor_set_uint8(x_532, sizeof(void*)*4, x_344);
return x_532;
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_247);
x_533 = lean_ctor_get(x_1, 1);
lean_inc(x_533);
x_534 = lean_ctor_get(x_1, 2);
lean_inc(x_534);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_535 = x_1;
} else {
 lean_dec_ref(x_1);
 x_535 = lean_box(0);
}
x_536 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_536, 0, x_519);
lean_ctor_set(x_536, 1, x_533);
lean_ctor_set(x_536, 2, x_534);
lean_ctor_set(x_536, 3, x_519);
lean_ctor_set_uint8(x_536, sizeof(void*)*4, x_246);
if (lean_is_scalar(x_535)) {
 x_537 = lean_alloc_ctor(1, 4, 1);
} else {
 x_537 = x_535;
}
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_2);
lean_ctor_set(x_537, 2, x_3);
lean_ctor_set(x_537, 3, x_4);
lean_ctor_set_uint8(x_537, sizeof(void*)*4, x_344);
return x_537;
}
}
else
{
uint8_t x_538; 
x_538 = lean_ctor_get_uint8(x_519, sizeof(void*)*4);
if (x_538 == 0)
{
uint8_t x_539; 
x_539 = !lean_is_exclusive(x_1);
if (x_539 == 0)
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; uint8_t x_544; 
x_540 = lean_ctor_get(x_1, 1);
x_541 = lean_ctor_get(x_1, 2);
x_542 = lean_ctor_get(x_1, 3);
lean_dec(x_542);
x_543 = lean_ctor_get(x_1, 0);
lean_dec(x_543);
x_544 = !lean_is_exclusive(x_4);
if (x_544 == 0)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_549; 
x_545 = lean_ctor_get(x_4, 1);
x_546 = lean_ctor_get(x_4, 2);
x_547 = lean_ctor_get(x_4, 3);
lean_dec(x_547);
x_548 = lean_ctor_get(x_4, 0);
lean_dec(x_548);
x_549 = !lean_is_exclusive(x_519);
if (x_549 == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_550 = lean_ctor_get(x_519, 0);
x_551 = lean_ctor_get(x_519, 1);
x_552 = lean_ctor_get(x_519, 2);
x_553 = lean_ctor_get(x_519, 3);
lean_ctor_set(x_519, 3, x_235);
lean_ctor_set(x_519, 2, x_541);
lean_ctor_set(x_519, 1, x_540);
lean_ctor_set(x_519, 0, x_235);
lean_ctor_set(x_4, 3, x_247);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_519);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_344);
lean_ctor_set(x_1, 3, x_553);
lean_ctor_set(x_1, 2, x_552);
lean_ctor_set(x_1, 1, x_551);
lean_ctor_set(x_1, 0, x_550);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_344);
x_554 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_554, 0, x_4);
lean_ctor_set(x_554, 1, x_545);
lean_ctor_set(x_554, 2, x_546);
lean_ctor_set(x_554, 3, x_1);
lean_ctor_set_uint8(x_554, sizeof(void*)*4, x_538);
return x_554;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_555 = lean_ctor_get(x_519, 0);
x_556 = lean_ctor_get(x_519, 1);
x_557 = lean_ctor_get(x_519, 2);
x_558 = lean_ctor_get(x_519, 3);
lean_inc(x_558);
lean_inc(x_557);
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_519);
x_559 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_559, 0, x_235);
lean_ctor_set(x_559, 1, x_540);
lean_ctor_set(x_559, 2, x_541);
lean_ctor_set(x_559, 3, x_235);
lean_ctor_set_uint8(x_559, sizeof(void*)*4, x_538);
lean_ctor_set(x_4, 3, x_247);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_559);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_344);
lean_ctor_set(x_1, 3, x_558);
lean_ctor_set(x_1, 2, x_557);
lean_ctor_set(x_1, 1, x_556);
lean_ctor_set(x_1, 0, x_555);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_344);
x_560 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_560, 0, x_4);
lean_ctor_set(x_560, 1, x_545);
lean_ctor_set(x_560, 2, x_546);
lean_ctor_set(x_560, 3, x_1);
lean_ctor_set_uint8(x_560, sizeof(void*)*4, x_538);
return x_560;
}
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_561 = lean_ctor_get(x_4, 1);
x_562 = lean_ctor_get(x_4, 2);
lean_inc(x_562);
lean_inc(x_561);
lean_dec(x_4);
x_563 = lean_ctor_get(x_519, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_519, 1);
lean_inc(x_564);
x_565 = lean_ctor_get(x_519, 2);
lean_inc(x_565);
x_566 = lean_ctor_get(x_519, 3);
lean_inc(x_566);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 lean_ctor_release(x_519, 2);
 lean_ctor_release(x_519, 3);
 x_567 = x_519;
} else {
 lean_dec_ref(x_519);
 x_567 = lean_box(0);
}
if (lean_is_scalar(x_567)) {
 x_568 = lean_alloc_ctor(1, 4, 1);
} else {
 x_568 = x_567;
}
lean_ctor_set(x_568, 0, x_235);
lean_ctor_set(x_568, 1, x_540);
lean_ctor_set(x_568, 2, x_541);
lean_ctor_set(x_568, 3, x_235);
lean_ctor_set_uint8(x_568, sizeof(void*)*4, x_538);
x_569 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_2);
lean_ctor_set(x_569, 2, x_3);
lean_ctor_set(x_569, 3, x_247);
lean_ctor_set_uint8(x_569, sizeof(void*)*4, x_344);
lean_ctor_set(x_1, 3, x_566);
lean_ctor_set(x_1, 2, x_565);
lean_ctor_set(x_1, 1, x_564);
lean_ctor_set(x_1, 0, x_563);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_344);
x_570 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_570, 0, x_569);
lean_ctor_set(x_570, 1, x_561);
lean_ctor_set(x_570, 2, x_562);
lean_ctor_set(x_570, 3, x_1);
lean_ctor_set_uint8(x_570, sizeof(void*)*4, x_538);
return x_570;
}
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_571 = lean_ctor_get(x_1, 1);
x_572 = lean_ctor_get(x_1, 2);
lean_inc(x_572);
lean_inc(x_571);
lean_dec(x_1);
x_573 = lean_ctor_get(x_4, 1);
lean_inc(x_573);
x_574 = lean_ctor_get(x_4, 2);
lean_inc(x_574);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_575 = x_4;
} else {
 lean_dec_ref(x_4);
 x_575 = lean_box(0);
}
x_576 = lean_ctor_get(x_519, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_519, 1);
lean_inc(x_577);
x_578 = lean_ctor_get(x_519, 2);
lean_inc(x_578);
x_579 = lean_ctor_get(x_519, 3);
lean_inc(x_579);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 lean_ctor_release(x_519, 2);
 lean_ctor_release(x_519, 3);
 x_580 = x_519;
} else {
 lean_dec_ref(x_519);
 x_580 = lean_box(0);
}
if (lean_is_scalar(x_580)) {
 x_581 = lean_alloc_ctor(1, 4, 1);
} else {
 x_581 = x_580;
}
lean_ctor_set(x_581, 0, x_235);
lean_ctor_set(x_581, 1, x_571);
lean_ctor_set(x_581, 2, x_572);
lean_ctor_set(x_581, 3, x_235);
lean_ctor_set_uint8(x_581, sizeof(void*)*4, x_538);
if (lean_is_scalar(x_575)) {
 x_582 = lean_alloc_ctor(1, 4, 1);
} else {
 x_582 = x_575;
}
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_2);
lean_ctor_set(x_582, 2, x_3);
lean_ctor_set(x_582, 3, x_247);
lean_ctor_set_uint8(x_582, sizeof(void*)*4, x_344);
x_583 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_583, 0, x_576);
lean_ctor_set(x_583, 1, x_577);
lean_ctor_set(x_583, 2, x_578);
lean_ctor_set(x_583, 3, x_579);
lean_ctor_set_uint8(x_583, sizeof(void*)*4, x_344);
x_584 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_584, 0, x_582);
lean_ctor_set(x_584, 1, x_573);
lean_ctor_set(x_584, 2, x_574);
lean_ctor_set(x_584, 3, x_583);
lean_ctor_set_uint8(x_584, sizeof(void*)*4, x_538);
return x_584;
}
}
else
{
uint8_t x_585; 
x_585 = !lean_is_exclusive(x_1);
if (x_585 == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; uint8_t x_590; 
x_586 = lean_ctor_get(x_1, 1);
x_587 = lean_ctor_get(x_1, 2);
x_588 = lean_ctor_get(x_1, 3);
lean_dec(x_588);
x_589 = lean_ctor_get(x_1, 0);
lean_dec(x_589);
x_590 = !lean_is_exclusive(x_4);
if (x_590 == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; 
x_591 = lean_ctor_get(x_4, 1);
x_592 = lean_ctor_get(x_4, 2);
x_593 = lean_ctor_get(x_4, 3);
lean_dec(x_593);
x_594 = lean_ctor_get(x_4, 0);
lean_dec(x_594);
x_595 = !lean_is_exclusive(x_247);
if (x_595 == 0)
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_596 = lean_ctor_get(x_247, 0);
x_597 = lean_ctor_get(x_247, 1);
x_598 = lean_ctor_get(x_247, 2);
x_599 = lean_ctor_get(x_247, 3);
lean_ctor_set(x_247, 3, x_235);
lean_ctor_set(x_247, 2, x_587);
lean_ctor_set(x_247, 1, x_586);
lean_ctor_set(x_247, 0, x_235);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
lean_ctor_set(x_4, 3, x_599);
lean_ctor_set(x_4, 2, x_598);
lean_ctor_set(x_4, 1, x_597);
lean_ctor_set(x_4, 0, x_596);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_538);
lean_ctor_set(x_1, 3, x_519);
lean_ctor_set(x_1, 2, x_592);
lean_ctor_set(x_1, 1, x_591);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
x_600 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_600, 0, x_247);
lean_ctor_set(x_600, 1, x_2);
lean_ctor_set(x_600, 2, x_3);
lean_ctor_set(x_600, 3, x_1);
lean_ctor_set_uint8(x_600, sizeof(void*)*4, x_538);
return x_600;
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_601 = lean_ctor_get(x_247, 0);
x_602 = lean_ctor_get(x_247, 1);
x_603 = lean_ctor_get(x_247, 2);
x_604 = lean_ctor_get(x_247, 3);
lean_inc(x_604);
lean_inc(x_603);
lean_inc(x_602);
lean_inc(x_601);
lean_dec(x_247);
x_605 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_605, 0, x_235);
lean_ctor_set(x_605, 1, x_586);
lean_ctor_set(x_605, 2, x_587);
lean_ctor_set(x_605, 3, x_235);
lean_ctor_set_uint8(x_605, sizeof(void*)*4, x_246);
lean_ctor_set(x_4, 3, x_604);
lean_ctor_set(x_4, 2, x_603);
lean_ctor_set(x_4, 1, x_602);
lean_ctor_set(x_4, 0, x_601);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_538);
lean_ctor_set(x_1, 3, x_519);
lean_ctor_set(x_1, 2, x_592);
lean_ctor_set(x_1, 1, x_591);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
x_606 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_606, 0, x_605);
lean_ctor_set(x_606, 1, x_2);
lean_ctor_set(x_606, 2, x_3);
lean_ctor_set(x_606, 3, x_1);
lean_ctor_set_uint8(x_606, sizeof(void*)*4, x_538);
return x_606;
}
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_607 = lean_ctor_get(x_4, 1);
x_608 = lean_ctor_get(x_4, 2);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_4);
x_609 = lean_ctor_get(x_247, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_247, 1);
lean_inc(x_610);
x_611 = lean_ctor_get(x_247, 2);
lean_inc(x_611);
x_612 = lean_ctor_get(x_247, 3);
lean_inc(x_612);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 x_613 = x_247;
} else {
 lean_dec_ref(x_247);
 x_613 = lean_box(0);
}
if (lean_is_scalar(x_613)) {
 x_614 = lean_alloc_ctor(1, 4, 1);
} else {
 x_614 = x_613;
}
lean_ctor_set(x_614, 0, x_235);
lean_ctor_set(x_614, 1, x_586);
lean_ctor_set(x_614, 2, x_587);
lean_ctor_set(x_614, 3, x_235);
lean_ctor_set_uint8(x_614, sizeof(void*)*4, x_246);
x_615 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_615, 0, x_609);
lean_ctor_set(x_615, 1, x_610);
lean_ctor_set(x_615, 2, x_611);
lean_ctor_set(x_615, 3, x_612);
lean_ctor_set_uint8(x_615, sizeof(void*)*4, x_538);
lean_ctor_set(x_1, 3, x_519);
lean_ctor_set(x_1, 2, x_608);
lean_ctor_set(x_1, 1, x_607);
lean_ctor_set(x_1, 0, x_615);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_246);
x_616 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_616, 0, x_614);
lean_ctor_set(x_616, 1, x_2);
lean_ctor_set(x_616, 2, x_3);
lean_ctor_set(x_616, 3, x_1);
lean_ctor_set_uint8(x_616, sizeof(void*)*4, x_538);
return x_616;
}
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_617 = lean_ctor_get(x_1, 1);
x_618 = lean_ctor_get(x_1, 2);
lean_inc(x_618);
lean_inc(x_617);
lean_dec(x_1);
x_619 = lean_ctor_get(x_4, 1);
lean_inc(x_619);
x_620 = lean_ctor_get(x_4, 2);
lean_inc(x_620);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_621 = x_4;
} else {
 lean_dec_ref(x_4);
 x_621 = lean_box(0);
}
x_622 = lean_ctor_get(x_247, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_247, 1);
lean_inc(x_623);
x_624 = lean_ctor_get(x_247, 2);
lean_inc(x_624);
x_625 = lean_ctor_get(x_247, 3);
lean_inc(x_625);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 x_626 = x_247;
} else {
 lean_dec_ref(x_247);
 x_626 = lean_box(0);
}
if (lean_is_scalar(x_626)) {
 x_627 = lean_alloc_ctor(1, 4, 1);
} else {
 x_627 = x_626;
}
lean_ctor_set(x_627, 0, x_235);
lean_ctor_set(x_627, 1, x_617);
lean_ctor_set(x_627, 2, x_618);
lean_ctor_set(x_627, 3, x_235);
lean_ctor_set_uint8(x_627, sizeof(void*)*4, x_246);
if (lean_is_scalar(x_621)) {
 x_628 = lean_alloc_ctor(1, 4, 1);
} else {
 x_628 = x_621;
}
lean_ctor_set(x_628, 0, x_622);
lean_ctor_set(x_628, 1, x_623);
lean_ctor_set(x_628, 2, x_624);
lean_ctor_set(x_628, 3, x_625);
lean_ctor_set_uint8(x_628, sizeof(void*)*4, x_538);
x_629 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_629, 0, x_628);
lean_ctor_set(x_629, 1, x_619);
lean_ctor_set(x_629, 2, x_620);
lean_ctor_set(x_629, 3, x_519);
lean_ctor_set_uint8(x_629, sizeof(void*)*4, x_246);
x_630 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_630, 0, x_627);
lean_ctor_set(x_630, 1, x_2);
lean_ctor_set(x_630, 2, x_3);
lean_ctor_set(x_630, 3, x_629);
lean_ctor_set_uint8(x_630, sizeof(void*)*4, x_538);
return x_630;
}
}
}
}
}
}
else
{
uint8_t x_631; 
x_631 = !lean_is_exclusive(x_1);
if (x_631 == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_632 = lean_ctor_get(x_1, 3);
lean_dec(x_632);
x_633 = lean_ctor_get(x_1, 0);
lean_dec(x_633);
lean_ctor_set(x_1, 0, x_235);
x_634 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_634, 0, x_1);
lean_ctor_set(x_634, 1, x_2);
lean_ctor_set(x_634, 2, x_3);
lean_ctor_set(x_634, 3, x_4);
lean_ctor_set_uint8(x_634, sizeof(void*)*4, x_246);
return x_634;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_635 = lean_ctor_get(x_1, 1);
x_636 = lean_ctor_get(x_1, 2);
lean_inc(x_636);
lean_inc(x_635);
lean_dec(x_1);
x_637 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_637, 0, x_235);
lean_ctor_set(x_637, 1, x_635);
lean_ctor_set(x_637, 2, x_636);
lean_ctor_set(x_637, 3, x_235);
lean_ctor_set_uint8(x_637, sizeof(void*)*4, x_233);
x_638 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_638, 0, x_637);
lean_ctor_set(x_638, 1, x_2);
lean_ctor_set(x_638, 2, x_3);
lean_ctor_set(x_638, 3, x_4);
lean_ctor_set_uint8(x_638, sizeof(void*)*4, x_246);
return x_638;
}
}
}
}
else
{
uint8_t x_639; 
x_639 = lean_ctor_get_uint8(x_235, sizeof(void*)*4);
if (x_639 == 0)
{
uint8_t x_640; 
x_640 = !lean_is_exclusive(x_1);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; uint8_t x_645; 
x_641 = lean_ctor_get(x_1, 1);
x_642 = lean_ctor_get(x_1, 2);
x_643 = lean_ctor_get(x_1, 3);
lean_dec(x_643);
x_644 = lean_ctor_get(x_1, 0);
lean_dec(x_644);
x_645 = !lean_is_exclusive(x_235);
if (x_645 == 0)
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; uint8_t x_650; lean_object* x_651; 
x_646 = lean_ctor_get(x_235, 0);
x_647 = lean_ctor_get(x_235, 1);
x_648 = lean_ctor_get(x_235, 2);
x_649 = lean_ctor_get(x_235, 3);
x_650 = 1;
lean_ctor_set(x_235, 3, x_646);
lean_ctor_set(x_235, 2, x_642);
lean_ctor_set(x_235, 1, x_641);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_650);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_649);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_650);
x_651 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_651, 0, x_235);
lean_ctor_set(x_651, 1, x_647);
lean_ctor_set(x_651, 2, x_648);
lean_ctor_set(x_651, 3, x_1);
lean_ctor_set_uint8(x_651, sizeof(void*)*4, x_639);
return x_651;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; uint8_t x_656; lean_object* x_657; lean_object* x_658; 
x_652 = lean_ctor_get(x_235, 0);
x_653 = lean_ctor_get(x_235, 1);
x_654 = lean_ctor_get(x_235, 2);
x_655 = lean_ctor_get(x_235, 3);
lean_inc(x_655);
lean_inc(x_654);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_235);
x_656 = 1;
x_657 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_657, 0, x_234);
lean_ctor_set(x_657, 1, x_641);
lean_ctor_set(x_657, 2, x_642);
lean_ctor_set(x_657, 3, x_652);
lean_ctor_set_uint8(x_657, sizeof(void*)*4, x_656);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_655);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_656);
x_658 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_658, 0, x_657);
lean_ctor_set(x_658, 1, x_653);
lean_ctor_set(x_658, 2, x_654);
lean_ctor_set(x_658, 3, x_1);
lean_ctor_set_uint8(x_658, sizeof(void*)*4, x_639);
return x_658;
}
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; uint8_t x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_659 = lean_ctor_get(x_1, 1);
x_660 = lean_ctor_get(x_1, 2);
lean_inc(x_660);
lean_inc(x_659);
lean_dec(x_1);
x_661 = lean_ctor_get(x_235, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_235, 1);
lean_inc(x_662);
x_663 = lean_ctor_get(x_235, 2);
lean_inc(x_663);
x_664 = lean_ctor_get(x_235, 3);
lean_inc(x_664);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_665 = x_235;
} else {
 lean_dec_ref(x_235);
 x_665 = lean_box(0);
}
x_666 = 1;
if (lean_is_scalar(x_665)) {
 x_667 = lean_alloc_ctor(1, 4, 1);
} else {
 x_667 = x_665;
}
lean_ctor_set(x_667, 0, x_234);
lean_ctor_set(x_667, 1, x_659);
lean_ctor_set(x_667, 2, x_660);
lean_ctor_set(x_667, 3, x_661);
lean_ctor_set_uint8(x_667, sizeof(void*)*4, x_666);
x_668 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_668, 0, x_664);
lean_ctor_set(x_668, 1, x_2);
lean_ctor_set(x_668, 2, x_3);
lean_ctor_set(x_668, 3, x_4);
lean_ctor_set_uint8(x_668, sizeof(void*)*4, x_666);
x_669 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_669, 0, x_667);
lean_ctor_set(x_669, 1, x_662);
lean_ctor_set(x_669, 2, x_663);
lean_ctor_set(x_669, 3, x_668);
lean_ctor_set_uint8(x_669, sizeof(void*)*4, x_639);
return x_669;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_670; 
x_670 = !lean_is_exclusive(x_1);
if (x_670 == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_671 = lean_ctor_get(x_1, 3);
lean_dec(x_671);
x_672 = lean_ctor_get(x_1, 0);
lean_dec(x_672);
lean_ctor_set(x_1, 0, x_4);
x_673 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_673, 0, x_1);
lean_ctor_set(x_673, 1, x_2);
lean_ctor_set(x_673, 2, x_3);
lean_ctor_set(x_673, 3, x_4);
lean_ctor_set_uint8(x_673, sizeof(void*)*4, x_639);
return x_673;
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_674 = lean_ctor_get(x_1, 1);
x_675 = lean_ctor_get(x_1, 2);
lean_inc(x_675);
lean_inc(x_674);
lean_dec(x_1);
x_676 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_676, 0, x_4);
lean_ctor_set(x_676, 1, x_674);
lean_ctor_set(x_676, 2, x_675);
lean_ctor_set(x_676, 3, x_235);
lean_ctor_set_uint8(x_676, sizeof(void*)*4, x_233);
x_677 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_677, 0, x_676);
lean_ctor_set(x_677, 1, x_2);
lean_ctor_set(x_677, 2, x_3);
lean_ctor_set(x_677, 3, x_4);
lean_ctor_set_uint8(x_677, sizeof(void*)*4, x_639);
return x_677;
}
}
else
{
uint8_t x_678; 
x_678 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_678 == 0)
{
lean_object* x_679; 
x_679 = lean_ctor_get(x_4, 0);
lean_inc(x_679);
if (lean_obj_tag(x_679) == 0)
{
lean_object* x_680; 
x_680 = lean_ctor_get(x_4, 3);
lean_inc(x_680);
if (lean_obj_tag(x_680) == 0)
{
uint8_t x_681; 
x_681 = !lean_is_exclusive(x_1);
if (x_681 == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; uint8_t x_686; 
x_682 = lean_ctor_get(x_1, 1);
x_683 = lean_ctor_get(x_1, 2);
x_684 = lean_ctor_get(x_1, 3);
lean_dec(x_684);
x_685 = lean_ctor_get(x_1, 0);
lean_dec(x_685);
x_686 = !lean_is_exclusive(x_4);
if (x_686 == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; uint8_t x_691; 
x_687 = lean_ctor_get(x_4, 1);
x_688 = lean_ctor_get(x_4, 2);
x_689 = lean_ctor_get(x_4, 3);
lean_dec(x_689);
x_690 = lean_ctor_get(x_4, 0);
lean_dec(x_690);
lean_inc(x_235);
lean_ctor_set(x_4, 3, x_235);
lean_ctor_set(x_4, 2, x_683);
lean_ctor_set(x_4, 1, x_682);
lean_ctor_set(x_4, 0, x_680);
x_691 = !lean_is_exclusive(x_235);
if (x_691 == 0)
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_692 = lean_ctor_get(x_235, 3);
lean_dec(x_692);
x_693 = lean_ctor_get(x_235, 2);
lean_dec(x_693);
x_694 = lean_ctor_get(x_235, 1);
lean_dec(x_694);
x_695 = lean_ctor_get(x_235, 0);
lean_dec(x_695);
lean_ctor_set(x_235, 3, x_680);
lean_ctor_set(x_235, 2, x_688);
lean_ctor_set(x_235, 1, x_687);
lean_ctor_set(x_235, 0, x_680);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_678);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_639);
return x_1;
}
else
{
lean_object* x_696; 
lean_dec(x_235);
x_696 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_696, 0, x_680);
lean_ctor_set(x_696, 1, x_687);
lean_ctor_set(x_696, 2, x_688);
lean_ctor_set(x_696, 3, x_680);
lean_ctor_set_uint8(x_696, sizeof(void*)*4, x_678);
lean_ctor_set(x_1, 3, x_696);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_639);
return x_1;
}
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
x_697 = lean_ctor_get(x_4, 1);
x_698 = lean_ctor_get(x_4, 2);
lean_inc(x_698);
lean_inc(x_697);
lean_dec(x_4);
lean_inc(x_235);
x_699 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_699, 0, x_680);
lean_ctor_set(x_699, 1, x_682);
lean_ctor_set(x_699, 2, x_683);
lean_ctor_set(x_699, 3, x_235);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_700 = x_235;
} else {
 lean_dec_ref(x_235);
 x_700 = lean_box(0);
}
lean_ctor_set_uint8(x_699, sizeof(void*)*4, x_678);
if (lean_is_scalar(x_700)) {
 x_701 = lean_alloc_ctor(1, 4, 1);
} else {
 x_701 = x_700;
}
lean_ctor_set(x_701, 0, x_680);
lean_ctor_set(x_701, 1, x_697);
lean_ctor_set(x_701, 2, x_698);
lean_ctor_set(x_701, 3, x_680);
lean_ctor_set_uint8(x_701, sizeof(void*)*4, x_678);
lean_ctor_set(x_1, 3, x_701);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_699);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_639);
return x_1;
}
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; 
x_702 = lean_ctor_get(x_1, 1);
x_703 = lean_ctor_get(x_1, 2);
lean_inc(x_703);
lean_inc(x_702);
lean_dec(x_1);
x_704 = lean_ctor_get(x_4, 1);
lean_inc(x_704);
x_705 = lean_ctor_get(x_4, 2);
lean_inc(x_705);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_706 = x_4;
} else {
 lean_dec_ref(x_4);
 x_706 = lean_box(0);
}
lean_inc(x_235);
if (lean_is_scalar(x_706)) {
 x_707 = lean_alloc_ctor(1, 4, 1);
} else {
 x_707 = x_706;
}
lean_ctor_set(x_707, 0, x_680);
lean_ctor_set(x_707, 1, x_702);
lean_ctor_set(x_707, 2, x_703);
lean_ctor_set(x_707, 3, x_235);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_708 = x_235;
} else {
 lean_dec_ref(x_235);
 x_708 = lean_box(0);
}
lean_ctor_set_uint8(x_707, sizeof(void*)*4, x_678);
if (lean_is_scalar(x_708)) {
 x_709 = lean_alloc_ctor(1, 4, 1);
} else {
 x_709 = x_708;
}
lean_ctor_set(x_709, 0, x_680);
lean_ctor_set(x_709, 1, x_704);
lean_ctor_set(x_709, 2, x_705);
lean_ctor_set(x_709, 3, x_680);
lean_ctor_set_uint8(x_709, sizeof(void*)*4, x_678);
x_710 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_710, 0, x_707);
lean_ctor_set(x_710, 1, x_2);
lean_ctor_set(x_710, 2, x_3);
lean_ctor_set(x_710, 3, x_709);
lean_ctor_set_uint8(x_710, sizeof(void*)*4, x_639);
return x_710;
}
}
else
{
uint8_t x_711; 
x_711 = lean_ctor_get_uint8(x_680, sizeof(void*)*4);
if (x_711 == 0)
{
uint8_t x_712; 
x_712 = !lean_is_exclusive(x_1);
if (x_712 == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; uint8_t x_717; 
x_713 = lean_ctor_get(x_1, 1);
x_714 = lean_ctor_get(x_1, 2);
x_715 = lean_ctor_get(x_1, 3);
lean_dec(x_715);
x_716 = lean_ctor_get(x_1, 0);
lean_dec(x_716);
x_717 = !lean_is_exclusive(x_4);
if (x_717 == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; uint8_t x_722; 
x_718 = lean_ctor_get(x_4, 1);
x_719 = lean_ctor_get(x_4, 2);
x_720 = lean_ctor_get(x_4, 3);
lean_dec(x_720);
x_721 = lean_ctor_get(x_4, 0);
lean_dec(x_721);
x_722 = !lean_is_exclusive(x_680);
if (x_722 == 0)
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; uint8_t x_727; 
x_723 = lean_ctor_get(x_680, 0);
x_724 = lean_ctor_get(x_680, 1);
x_725 = lean_ctor_get(x_680, 2);
x_726 = lean_ctor_get(x_680, 3);
lean_inc(x_235);
lean_ctor_set(x_680, 3, x_235);
lean_ctor_set(x_680, 2, x_714);
lean_ctor_set(x_680, 1, x_713);
lean_ctor_set(x_680, 0, x_679);
x_727 = !lean_is_exclusive(x_235);
if (x_727 == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_728 = lean_ctor_get(x_235, 3);
lean_dec(x_728);
x_729 = lean_ctor_get(x_235, 2);
lean_dec(x_729);
x_730 = lean_ctor_get(x_235, 1);
lean_dec(x_730);
x_731 = lean_ctor_get(x_235, 0);
lean_dec(x_731);
lean_ctor_set(x_4, 3, x_679);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_680);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_639);
lean_ctor_set(x_235, 3, x_726);
lean_ctor_set(x_235, 2, x_725);
lean_ctor_set(x_235, 1, x_724);
lean_ctor_set(x_235, 0, x_723);
lean_ctor_set(x_1, 2, x_719);
lean_ctor_set(x_1, 1, x_718);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_711);
return x_1;
}
else
{
lean_object* x_732; 
lean_dec(x_235);
lean_ctor_set(x_4, 3, x_679);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_680);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_639);
x_732 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_732, 0, x_723);
lean_ctor_set(x_732, 1, x_724);
lean_ctor_set(x_732, 2, x_725);
lean_ctor_set(x_732, 3, x_726);
lean_ctor_set_uint8(x_732, sizeof(void*)*4, x_639);
lean_ctor_set(x_1, 3, x_732);
lean_ctor_set(x_1, 2, x_719);
lean_ctor_set(x_1, 1, x_718);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_711);
return x_1;
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_733 = lean_ctor_get(x_680, 0);
x_734 = lean_ctor_get(x_680, 1);
x_735 = lean_ctor_get(x_680, 2);
x_736 = lean_ctor_get(x_680, 3);
lean_inc(x_736);
lean_inc(x_735);
lean_inc(x_734);
lean_inc(x_733);
lean_dec(x_680);
lean_inc(x_235);
x_737 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_737, 0, x_679);
lean_ctor_set(x_737, 1, x_713);
lean_ctor_set(x_737, 2, x_714);
lean_ctor_set(x_737, 3, x_235);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_738 = x_235;
} else {
 lean_dec_ref(x_235);
 x_738 = lean_box(0);
}
lean_ctor_set_uint8(x_737, sizeof(void*)*4, x_711);
lean_ctor_set(x_4, 3, x_679);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_737);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_639);
if (lean_is_scalar(x_738)) {
 x_739 = lean_alloc_ctor(1, 4, 1);
} else {
 x_739 = x_738;
}
lean_ctor_set(x_739, 0, x_733);
lean_ctor_set(x_739, 1, x_734);
lean_ctor_set(x_739, 2, x_735);
lean_ctor_set(x_739, 3, x_736);
lean_ctor_set_uint8(x_739, sizeof(void*)*4, x_639);
lean_ctor_set(x_1, 3, x_739);
lean_ctor_set(x_1, 2, x_719);
lean_ctor_set(x_1, 1, x_718);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_711);
return x_1;
}
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_740 = lean_ctor_get(x_4, 1);
x_741 = lean_ctor_get(x_4, 2);
lean_inc(x_741);
lean_inc(x_740);
lean_dec(x_4);
x_742 = lean_ctor_get(x_680, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_680, 1);
lean_inc(x_743);
x_744 = lean_ctor_get(x_680, 2);
lean_inc(x_744);
x_745 = lean_ctor_get(x_680, 3);
lean_inc(x_745);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 lean_ctor_release(x_680, 2);
 lean_ctor_release(x_680, 3);
 x_746 = x_680;
} else {
 lean_dec_ref(x_680);
 x_746 = lean_box(0);
}
lean_inc(x_235);
if (lean_is_scalar(x_746)) {
 x_747 = lean_alloc_ctor(1, 4, 1);
} else {
 x_747 = x_746;
}
lean_ctor_set(x_747, 0, x_679);
lean_ctor_set(x_747, 1, x_713);
lean_ctor_set(x_747, 2, x_714);
lean_ctor_set(x_747, 3, x_235);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_748 = x_235;
} else {
 lean_dec_ref(x_235);
 x_748 = lean_box(0);
}
lean_ctor_set_uint8(x_747, sizeof(void*)*4, x_711);
x_749 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_749, 0, x_747);
lean_ctor_set(x_749, 1, x_2);
lean_ctor_set(x_749, 2, x_3);
lean_ctor_set(x_749, 3, x_679);
lean_ctor_set_uint8(x_749, sizeof(void*)*4, x_639);
if (lean_is_scalar(x_748)) {
 x_750 = lean_alloc_ctor(1, 4, 1);
} else {
 x_750 = x_748;
}
lean_ctor_set(x_750, 0, x_742);
lean_ctor_set(x_750, 1, x_743);
lean_ctor_set(x_750, 2, x_744);
lean_ctor_set(x_750, 3, x_745);
lean_ctor_set_uint8(x_750, sizeof(void*)*4, x_639);
lean_ctor_set(x_1, 3, x_750);
lean_ctor_set(x_1, 2, x_741);
lean_ctor_set(x_1, 1, x_740);
lean_ctor_set(x_1, 0, x_749);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_711);
return x_1;
}
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_751 = lean_ctor_get(x_1, 1);
x_752 = lean_ctor_get(x_1, 2);
lean_inc(x_752);
lean_inc(x_751);
lean_dec(x_1);
x_753 = lean_ctor_get(x_4, 1);
lean_inc(x_753);
x_754 = lean_ctor_get(x_4, 2);
lean_inc(x_754);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_755 = x_4;
} else {
 lean_dec_ref(x_4);
 x_755 = lean_box(0);
}
x_756 = lean_ctor_get(x_680, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_680, 1);
lean_inc(x_757);
x_758 = lean_ctor_get(x_680, 2);
lean_inc(x_758);
x_759 = lean_ctor_get(x_680, 3);
lean_inc(x_759);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 lean_ctor_release(x_680, 2);
 lean_ctor_release(x_680, 3);
 x_760 = x_680;
} else {
 lean_dec_ref(x_680);
 x_760 = lean_box(0);
}
lean_inc(x_235);
if (lean_is_scalar(x_760)) {
 x_761 = lean_alloc_ctor(1, 4, 1);
} else {
 x_761 = x_760;
}
lean_ctor_set(x_761, 0, x_679);
lean_ctor_set(x_761, 1, x_751);
lean_ctor_set(x_761, 2, x_752);
lean_ctor_set(x_761, 3, x_235);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_762 = x_235;
} else {
 lean_dec_ref(x_235);
 x_762 = lean_box(0);
}
lean_ctor_set_uint8(x_761, sizeof(void*)*4, x_711);
if (lean_is_scalar(x_755)) {
 x_763 = lean_alloc_ctor(1, 4, 1);
} else {
 x_763 = x_755;
}
lean_ctor_set(x_763, 0, x_761);
lean_ctor_set(x_763, 1, x_2);
lean_ctor_set(x_763, 2, x_3);
lean_ctor_set(x_763, 3, x_679);
lean_ctor_set_uint8(x_763, sizeof(void*)*4, x_639);
if (lean_is_scalar(x_762)) {
 x_764 = lean_alloc_ctor(1, 4, 1);
} else {
 x_764 = x_762;
}
lean_ctor_set(x_764, 0, x_756);
lean_ctor_set(x_764, 1, x_757);
lean_ctor_set(x_764, 2, x_758);
lean_ctor_set(x_764, 3, x_759);
lean_ctor_set_uint8(x_764, sizeof(void*)*4, x_639);
x_765 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_765, 0, x_763);
lean_ctor_set(x_765, 1, x_753);
lean_ctor_set(x_765, 2, x_754);
lean_ctor_set(x_765, 3, x_764);
lean_ctor_set_uint8(x_765, sizeof(void*)*4, x_711);
return x_765;
}
}
else
{
uint8_t x_766; 
x_766 = !lean_is_exclusive(x_680);
if (x_766 == 0)
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; uint8_t x_771; 
x_767 = lean_ctor_get(x_680, 3);
lean_dec(x_767);
x_768 = lean_ctor_get(x_680, 2);
lean_dec(x_768);
x_769 = lean_ctor_get(x_680, 1);
lean_dec(x_769);
x_770 = lean_ctor_get(x_680, 0);
lean_dec(x_770);
x_771 = !lean_is_exclusive(x_1);
if (x_771 == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; uint8_t x_776; 
x_772 = lean_ctor_get(x_1, 1);
x_773 = lean_ctor_get(x_1, 2);
x_774 = lean_ctor_get(x_1, 3);
lean_dec(x_774);
x_775 = lean_ctor_get(x_1, 0);
lean_dec(x_775);
x_776 = !lean_is_exclusive(x_235);
if (x_776 == 0)
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_777 = lean_ctor_get(x_235, 0);
x_778 = lean_ctor_get(x_235, 1);
x_779 = lean_ctor_get(x_235, 2);
x_780 = lean_ctor_get(x_235, 3);
lean_ctor_set(x_680, 3, x_780);
lean_ctor_set(x_680, 2, x_779);
lean_ctor_set(x_680, 1, x_778);
lean_ctor_set(x_680, 0, x_777);
lean_ctor_set(x_235, 3, x_680);
lean_ctor_set(x_235, 2, x_773);
lean_ctor_set(x_235, 1, x_772);
lean_ctor_set(x_235, 0, x_679);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_678);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_711);
return x_1;
}
else
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_781 = lean_ctor_get(x_235, 0);
x_782 = lean_ctor_get(x_235, 1);
x_783 = lean_ctor_get(x_235, 2);
x_784 = lean_ctor_get(x_235, 3);
lean_inc(x_784);
lean_inc(x_783);
lean_inc(x_782);
lean_inc(x_781);
lean_dec(x_235);
lean_ctor_set(x_680, 3, x_784);
lean_ctor_set(x_680, 2, x_783);
lean_ctor_set(x_680, 1, x_782);
lean_ctor_set(x_680, 0, x_781);
x_785 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_785, 0, x_679);
lean_ctor_set(x_785, 1, x_772);
lean_ctor_set(x_785, 2, x_773);
lean_ctor_set(x_785, 3, x_680);
lean_ctor_set_uint8(x_785, sizeof(void*)*4, x_678);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_785);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_711);
return x_1;
}
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_786 = lean_ctor_get(x_1, 1);
x_787 = lean_ctor_get(x_1, 2);
lean_inc(x_787);
lean_inc(x_786);
lean_dec(x_1);
x_788 = lean_ctor_get(x_235, 0);
lean_inc(x_788);
x_789 = lean_ctor_get(x_235, 1);
lean_inc(x_789);
x_790 = lean_ctor_get(x_235, 2);
lean_inc(x_790);
x_791 = lean_ctor_get(x_235, 3);
lean_inc(x_791);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_792 = x_235;
} else {
 lean_dec_ref(x_235);
 x_792 = lean_box(0);
}
lean_ctor_set(x_680, 3, x_791);
lean_ctor_set(x_680, 2, x_790);
lean_ctor_set(x_680, 1, x_789);
lean_ctor_set(x_680, 0, x_788);
if (lean_is_scalar(x_792)) {
 x_793 = lean_alloc_ctor(1, 4, 1);
} else {
 x_793 = x_792;
}
lean_ctor_set(x_793, 0, x_679);
lean_ctor_set(x_793, 1, x_786);
lean_ctor_set(x_793, 2, x_787);
lean_ctor_set(x_793, 3, x_680);
lean_ctor_set_uint8(x_793, sizeof(void*)*4, x_678);
x_794 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_794, 0, x_793);
lean_ctor_set(x_794, 1, x_2);
lean_ctor_set(x_794, 2, x_3);
lean_ctor_set(x_794, 3, x_4);
lean_ctor_set_uint8(x_794, sizeof(void*)*4, x_711);
return x_794;
}
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; 
lean_dec(x_680);
x_795 = lean_ctor_get(x_1, 1);
lean_inc(x_795);
x_796 = lean_ctor_get(x_1, 2);
lean_inc(x_796);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_797 = x_1;
} else {
 lean_dec_ref(x_1);
 x_797 = lean_box(0);
}
x_798 = lean_ctor_get(x_235, 0);
lean_inc(x_798);
x_799 = lean_ctor_get(x_235, 1);
lean_inc(x_799);
x_800 = lean_ctor_get(x_235, 2);
lean_inc(x_800);
x_801 = lean_ctor_get(x_235, 3);
lean_inc(x_801);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_802 = x_235;
} else {
 lean_dec_ref(x_235);
 x_802 = lean_box(0);
}
x_803 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_803, 0, x_798);
lean_ctor_set(x_803, 1, x_799);
lean_ctor_set(x_803, 2, x_800);
lean_ctor_set(x_803, 3, x_801);
lean_ctor_set_uint8(x_803, sizeof(void*)*4, x_711);
if (lean_is_scalar(x_802)) {
 x_804 = lean_alloc_ctor(1, 4, 1);
} else {
 x_804 = x_802;
}
lean_ctor_set(x_804, 0, x_679);
lean_ctor_set(x_804, 1, x_795);
lean_ctor_set(x_804, 2, x_796);
lean_ctor_set(x_804, 3, x_803);
lean_ctor_set_uint8(x_804, sizeof(void*)*4, x_678);
if (lean_is_scalar(x_797)) {
 x_805 = lean_alloc_ctor(1, 4, 1);
} else {
 x_805 = x_797;
}
lean_ctor_set(x_805, 0, x_804);
lean_ctor_set(x_805, 1, x_2);
lean_ctor_set(x_805, 2, x_3);
lean_ctor_set(x_805, 3, x_4);
lean_ctor_set_uint8(x_805, sizeof(void*)*4, x_711);
return x_805;
}
}
}
}
else
{
uint8_t x_806; 
x_806 = lean_ctor_get_uint8(x_679, sizeof(void*)*4);
if (x_806 == 0)
{
lean_object* x_807; 
x_807 = lean_ctor_get(x_4, 3);
lean_inc(x_807);
if (lean_obj_tag(x_807) == 0)
{
uint8_t x_808; 
x_808 = !lean_is_exclusive(x_1);
if (x_808 == 0)
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; uint8_t x_813; 
x_809 = lean_ctor_get(x_1, 1);
x_810 = lean_ctor_get(x_1, 2);
x_811 = lean_ctor_get(x_1, 3);
lean_dec(x_811);
x_812 = lean_ctor_get(x_1, 0);
lean_dec(x_812);
x_813 = !lean_is_exclusive(x_4);
if (x_813 == 0)
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; uint8_t x_818; 
x_814 = lean_ctor_get(x_4, 1);
x_815 = lean_ctor_get(x_4, 2);
x_816 = lean_ctor_get(x_4, 3);
lean_dec(x_816);
x_817 = lean_ctor_get(x_4, 0);
lean_dec(x_817);
x_818 = !lean_is_exclusive(x_679);
if (x_818 == 0)
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; uint8_t x_823; 
x_819 = lean_ctor_get(x_679, 0);
x_820 = lean_ctor_get(x_679, 1);
x_821 = lean_ctor_get(x_679, 2);
x_822 = lean_ctor_get(x_679, 3);
lean_inc(x_235);
lean_ctor_set(x_679, 3, x_235);
lean_ctor_set(x_679, 2, x_810);
lean_ctor_set(x_679, 1, x_809);
lean_ctor_set(x_679, 0, x_807);
x_823 = !lean_is_exclusive(x_235);
if (x_823 == 0)
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_824 = lean_ctor_get(x_235, 3);
lean_dec(x_824);
x_825 = lean_ctor_get(x_235, 2);
lean_dec(x_825);
x_826 = lean_ctor_get(x_235, 1);
lean_dec(x_826);
x_827 = lean_ctor_get(x_235, 0);
lean_dec(x_827);
lean_ctor_set(x_4, 3, x_819);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_639);
lean_ctor_set(x_235, 3, x_807);
lean_ctor_set(x_235, 2, x_815);
lean_ctor_set(x_235, 1, x_814);
lean_ctor_set(x_235, 0, x_822);
lean_ctor_set(x_1, 2, x_821);
lean_ctor_set(x_1, 1, x_820);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_806);
return x_1;
}
else
{
lean_object* x_828; 
lean_dec(x_235);
lean_ctor_set(x_4, 3, x_819);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_639);
x_828 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_828, 0, x_822);
lean_ctor_set(x_828, 1, x_814);
lean_ctor_set(x_828, 2, x_815);
lean_ctor_set(x_828, 3, x_807);
lean_ctor_set_uint8(x_828, sizeof(void*)*4, x_639);
lean_ctor_set(x_1, 3, x_828);
lean_ctor_set(x_1, 2, x_821);
lean_ctor_set(x_1, 1, x_820);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_806);
return x_1;
}
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_829 = lean_ctor_get(x_679, 0);
x_830 = lean_ctor_get(x_679, 1);
x_831 = lean_ctor_get(x_679, 2);
x_832 = lean_ctor_get(x_679, 3);
lean_inc(x_832);
lean_inc(x_831);
lean_inc(x_830);
lean_inc(x_829);
lean_dec(x_679);
lean_inc(x_235);
x_833 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_833, 0, x_807);
lean_ctor_set(x_833, 1, x_809);
lean_ctor_set(x_833, 2, x_810);
lean_ctor_set(x_833, 3, x_235);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_834 = x_235;
} else {
 lean_dec_ref(x_235);
 x_834 = lean_box(0);
}
lean_ctor_set_uint8(x_833, sizeof(void*)*4, x_806);
lean_ctor_set(x_4, 3, x_829);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_833);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_639);
if (lean_is_scalar(x_834)) {
 x_835 = lean_alloc_ctor(1, 4, 1);
} else {
 x_835 = x_834;
}
lean_ctor_set(x_835, 0, x_832);
lean_ctor_set(x_835, 1, x_814);
lean_ctor_set(x_835, 2, x_815);
lean_ctor_set(x_835, 3, x_807);
lean_ctor_set_uint8(x_835, sizeof(void*)*4, x_639);
lean_ctor_set(x_1, 3, x_835);
lean_ctor_set(x_1, 2, x_831);
lean_ctor_set(x_1, 1, x_830);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_806);
return x_1;
}
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
x_836 = lean_ctor_get(x_4, 1);
x_837 = lean_ctor_get(x_4, 2);
lean_inc(x_837);
lean_inc(x_836);
lean_dec(x_4);
x_838 = lean_ctor_get(x_679, 0);
lean_inc(x_838);
x_839 = lean_ctor_get(x_679, 1);
lean_inc(x_839);
x_840 = lean_ctor_get(x_679, 2);
lean_inc(x_840);
x_841 = lean_ctor_get(x_679, 3);
lean_inc(x_841);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 lean_ctor_release(x_679, 2);
 lean_ctor_release(x_679, 3);
 x_842 = x_679;
} else {
 lean_dec_ref(x_679);
 x_842 = lean_box(0);
}
lean_inc(x_235);
if (lean_is_scalar(x_842)) {
 x_843 = lean_alloc_ctor(1, 4, 1);
} else {
 x_843 = x_842;
}
lean_ctor_set(x_843, 0, x_807);
lean_ctor_set(x_843, 1, x_809);
lean_ctor_set(x_843, 2, x_810);
lean_ctor_set(x_843, 3, x_235);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_844 = x_235;
} else {
 lean_dec_ref(x_235);
 x_844 = lean_box(0);
}
lean_ctor_set_uint8(x_843, sizeof(void*)*4, x_806);
x_845 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_845, 0, x_843);
lean_ctor_set(x_845, 1, x_2);
lean_ctor_set(x_845, 2, x_3);
lean_ctor_set(x_845, 3, x_838);
lean_ctor_set_uint8(x_845, sizeof(void*)*4, x_639);
if (lean_is_scalar(x_844)) {
 x_846 = lean_alloc_ctor(1, 4, 1);
} else {
 x_846 = x_844;
}
lean_ctor_set(x_846, 0, x_841);
lean_ctor_set(x_846, 1, x_836);
lean_ctor_set(x_846, 2, x_837);
lean_ctor_set(x_846, 3, x_807);
lean_ctor_set_uint8(x_846, sizeof(void*)*4, x_639);
lean_ctor_set(x_1, 3, x_846);
lean_ctor_set(x_1, 2, x_840);
lean_ctor_set(x_1, 1, x_839);
lean_ctor_set(x_1, 0, x_845);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_806);
return x_1;
}
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_847 = lean_ctor_get(x_1, 1);
x_848 = lean_ctor_get(x_1, 2);
lean_inc(x_848);
lean_inc(x_847);
lean_dec(x_1);
x_849 = lean_ctor_get(x_4, 1);
lean_inc(x_849);
x_850 = lean_ctor_get(x_4, 2);
lean_inc(x_850);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_851 = x_4;
} else {
 lean_dec_ref(x_4);
 x_851 = lean_box(0);
}
x_852 = lean_ctor_get(x_679, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_679, 1);
lean_inc(x_853);
x_854 = lean_ctor_get(x_679, 2);
lean_inc(x_854);
x_855 = lean_ctor_get(x_679, 3);
lean_inc(x_855);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 lean_ctor_release(x_679, 2);
 lean_ctor_release(x_679, 3);
 x_856 = x_679;
} else {
 lean_dec_ref(x_679);
 x_856 = lean_box(0);
}
lean_inc(x_235);
if (lean_is_scalar(x_856)) {
 x_857 = lean_alloc_ctor(1, 4, 1);
} else {
 x_857 = x_856;
}
lean_ctor_set(x_857, 0, x_807);
lean_ctor_set(x_857, 1, x_847);
lean_ctor_set(x_857, 2, x_848);
lean_ctor_set(x_857, 3, x_235);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_858 = x_235;
} else {
 lean_dec_ref(x_235);
 x_858 = lean_box(0);
}
lean_ctor_set_uint8(x_857, sizeof(void*)*4, x_806);
if (lean_is_scalar(x_851)) {
 x_859 = lean_alloc_ctor(1, 4, 1);
} else {
 x_859 = x_851;
}
lean_ctor_set(x_859, 0, x_857);
lean_ctor_set(x_859, 1, x_2);
lean_ctor_set(x_859, 2, x_3);
lean_ctor_set(x_859, 3, x_852);
lean_ctor_set_uint8(x_859, sizeof(void*)*4, x_639);
if (lean_is_scalar(x_858)) {
 x_860 = lean_alloc_ctor(1, 4, 1);
} else {
 x_860 = x_858;
}
lean_ctor_set(x_860, 0, x_855);
lean_ctor_set(x_860, 1, x_849);
lean_ctor_set(x_860, 2, x_850);
lean_ctor_set(x_860, 3, x_807);
lean_ctor_set_uint8(x_860, sizeof(void*)*4, x_639);
x_861 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_861, 0, x_859);
lean_ctor_set(x_861, 1, x_853);
lean_ctor_set(x_861, 2, x_854);
lean_ctor_set(x_861, 3, x_860);
lean_ctor_set_uint8(x_861, sizeof(void*)*4, x_806);
return x_861;
}
}
else
{
uint8_t x_862; 
x_862 = lean_ctor_get_uint8(x_807, sizeof(void*)*4);
if (x_862 == 0)
{
uint8_t x_863; 
x_863 = !lean_is_exclusive(x_1);
if (x_863 == 0)
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; uint8_t x_868; 
x_864 = lean_ctor_get(x_1, 1);
x_865 = lean_ctor_get(x_1, 2);
x_866 = lean_ctor_get(x_1, 3);
lean_dec(x_866);
x_867 = lean_ctor_get(x_1, 0);
lean_dec(x_867);
x_868 = !lean_is_exclusive(x_4);
if (x_868 == 0)
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; uint8_t x_873; 
x_869 = lean_ctor_get(x_4, 1);
x_870 = lean_ctor_get(x_4, 2);
x_871 = lean_ctor_get(x_4, 3);
lean_dec(x_871);
x_872 = lean_ctor_get(x_4, 0);
lean_dec(x_872);
x_873 = !lean_is_exclusive(x_679);
if (x_873 == 0)
{
uint8_t x_874; 
x_874 = !lean_is_exclusive(x_807);
if (x_874 == 0)
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; uint8_t x_879; 
x_875 = lean_ctor_get(x_807, 0);
x_876 = lean_ctor_get(x_807, 1);
x_877 = lean_ctor_get(x_807, 2);
x_878 = lean_ctor_get(x_807, 3);
lean_inc(x_235);
lean_ctor_set(x_807, 3, x_235);
lean_ctor_set(x_807, 2, x_865);
lean_ctor_set(x_807, 1, x_864);
lean_ctor_set(x_807, 0, x_234);
x_879 = !lean_is_exclusive(x_235);
if (x_879 == 0)
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_880 = lean_ctor_get(x_235, 3);
lean_dec(x_880);
x_881 = lean_ctor_get(x_235, 2);
lean_dec(x_881);
x_882 = lean_ctor_get(x_235, 1);
lean_dec(x_882);
x_883 = lean_ctor_get(x_235, 0);
lean_dec(x_883);
lean_ctor_set_uint8(x_679, sizeof(void*)*4, x_862);
lean_ctor_set(x_4, 3, x_679);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_807);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_639);
lean_ctor_set(x_235, 3, x_878);
lean_ctor_set(x_235, 2, x_877);
lean_ctor_set(x_235, 1, x_876);
lean_ctor_set(x_235, 0, x_875);
lean_ctor_set(x_1, 2, x_870);
lean_ctor_set(x_1, 1, x_869);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_862);
return x_1;
}
else
{
lean_object* x_884; 
lean_dec(x_235);
lean_ctor_set_uint8(x_679, sizeof(void*)*4, x_862);
lean_ctor_set(x_4, 3, x_679);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_807);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_639);
x_884 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_884, 0, x_875);
lean_ctor_set(x_884, 1, x_876);
lean_ctor_set(x_884, 2, x_877);
lean_ctor_set(x_884, 3, x_878);
lean_ctor_set_uint8(x_884, sizeof(void*)*4, x_639);
lean_ctor_set(x_1, 3, x_884);
lean_ctor_set(x_1, 2, x_870);
lean_ctor_set(x_1, 1, x_869);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_862);
return x_1;
}
}
else
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; 
x_885 = lean_ctor_get(x_807, 0);
x_886 = lean_ctor_get(x_807, 1);
x_887 = lean_ctor_get(x_807, 2);
x_888 = lean_ctor_get(x_807, 3);
lean_inc(x_888);
lean_inc(x_887);
lean_inc(x_886);
lean_inc(x_885);
lean_dec(x_807);
lean_inc(x_235);
x_889 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_889, 0, x_234);
lean_ctor_set(x_889, 1, x_864);
lean_ctor_set(x_889, 2, x_865);
lean_ctor_set(x_889, 3, x_235);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_890 = x_235;
} else {
 lean_dec_ref(x_235);
 x_890 = lean_box(0);
}
lean_ctor_set_uint8(x_889, sizeof(void*)*4, x_862);
lean_ctor_set_uint8(x_679, sizeof(void*)*4, x_862);
lean_ctor_set(x_4, 3, x_679);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_889);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_639);
if (lean_is_scalar(x_890)) {
 x_891 = lean_alloc_ctor(1, 4, 1);
} else {
 x_891 = x_890;
}
lean_ctor_set(x_891, 0, x_885);
lean_ctor_set(x_891, 1, x_886);
lean_ctor_set(x_891, 2, x_887);
lean_ctor_set(x_891, 3, x_888);
lean_ctor_set_uint8(x_891, sizeof(void*)*4, x_639);
lean_ctor_set(x_1, 3, x_891);
lean_ctor_set(x_1, 2, x_870);
lean_ctor_set(x_1, 1, x_869);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_862);
return x_1;
}
}
else
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; 
x_892 = lean_ctor_get(x_679, 0);
x_893 = lean_ctor_get(x_679, 1);
x_894 = lean_ctor_get(x_679, 2);
x_895 = lean_ctor_get(x_679, 3);
lean_inc(x_895);
lean_inc(x_894);
lean_inc(x_893);
lean_inc(x_892);
lean_dec(x_679);
x_896 = lean_ctor_get(x_807, 0);
lean_inc(x_896);
x_897 = lean_ctor_get(x_807, 1);
lean_inc(x_897);
x_898 = lean_ctor_get(x_807, 2);
lean_inc(x_898);
x_899 = lean_ctor_get(x_807, 3);
lean_inc(x_899);
if (lean_is_exclusive(x_807)) {
 lean_ctor_release(x_807, 0);
 lean_ctor_release(x_807, 1);
 lean_ctor_release(x_807, 2);
 lean_ctor_release(x_807, 3);
 x_900 = x_807;
} else {
 lean_dec_ref(x_807);
 x_900 = lean_box(0);
}
lean_inc(x_235);
if (lean_is_scalar(x_900)) {
 x_901 = lean_alloc_ctor(1, 4, 1);
} else {
 x_901 = x_900;
}
lean_ctor_set(x_901, 0, x_234);
lean_ctor_set(x_901, 1, x_864);
lean_ctor_set(x_901, 2, x_865);
lean_ctor_set(x_901, 3, x_235);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_902 = x_235;
} else {
 lean_dec_ref(x_235);
 x_902 = lean_box(0);
}
lean_ctor_set_uint8(x_901, sizeof(void*)*4, x_862);
x_903 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_903, 0, x_892);
lean_ctor_set(x_903, 1, x_893);
lean_ctor_set(x_903, 2, x_894);
lean_ctor_set(x_903, 3, x_895);
lean_ctor_set_uint8(x_903, sizeof(void*)*4, x_862);
lean_ctor_set(x_4, 3, x_903);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_901);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_639);
if (lean_is_scalar(x_902)) {
 x_904 = lean_alloc_ctor(1, 4, 1);
} else {
 x_904 = x_902;
}
lean_ctor_set(x_904, 0, x_896);
lean_ctor_set(x_904, 1, x_897);
lean_ctor_set(x_904, 2, x_898);
lean_ctor_set(x_904, 3, x_899);
lean_ctor_set_uint8(x_904, sizeof(void*)*4, x_639);
lean_ctor_set(x_1, 3, x_904);
lean_ctor_set(x_1, 2, x_870);
lean_ctor_set(x_1, 1, x_869);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_862);
return x_1;
}
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; 
x_905 = lean_ctor_get(x_4, 1);
x_906 = lean_ctor_get(x_4, 2);
lean_inc(x_906);
lean_inc(x_905);
lean_dec(x_4);
x_907 = lean_ctor_get(x_679, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_679, 1);
lean_inc(x_908);
x_909 = lean_ctor_get(x_679, 2);
lean_inc(x_909);
x_910 = lean_ctor_get(x_679, 3);
lean_inc(x_910);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 lean_ctor_release(x_679, 2);
 lean_ctor_release(x_679, 3);
 x_911 = x_679;
} else {
 lean_dec_ref(x_679);
 x_911 = lean_box(0);
}
x_912 = lean_ctor_get(x_807, 0);
lean_inc(x_912);
x_913 = lean_ctor_get(x_807, 1);
lean_inc(x_913);
x_914 = lean_ctor_get(x_807, 2);
lean_inc(x_914);
x_915 = lean_ctor_get(x_807, 3);
lean_inc(x_915);
if (lean_is_exclusive(x_807)) {
 lean_ctor_release(x_807, 0);
 lean_ctor_release(x_807, 1);
 lean_ctor_release(x_807, 2);
 lean_ctor_release(x_807, 3);
 x_916 = x_807;
} else {
 lean_dec_ref(x_807);
 x_916 = lean_box(0);
}
lean_inc(x_235);
if (lean_is_scalar(x_916)) {
 x_917 = lean_alloc_ctor(1, 4, 1);
} else {
 x_917 = x_916;
}
lean_ctor_set(x_917, 0, x_234);
lean_ctor_set(x_917, 1, x_864);
lean_ctor_set(x_917, 2, x_865);
lean_ctor_set(x_917, 3, x_235);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_918 = x_235;
} else {
 lean_dec_ref(x_235);
 x_918 = lean_box(0);
}
lean_ctor_set_uint8(x_917, sizeof(void*)*4, x_862);
if (lean_is_scalar(x_911)) {
 x_919 = lean_alloc_ctor(1, 4, 1);
} else {
 x_919 = x_911;
}
lean_ctor_set(x_919, 0, x_907);
lean_ctor_set(x_919, 1, x_908);
lean_ctor_set(x_919, 2, x_909);
lean_ctor_set(x_919, 3, x_910);
lean_ctor_set_uint8(x_919, sizeof(void*)*4, x_862);
x_920 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_920, 0, x_917);
lean_ctor_set(x_920, 1, x_2);
lean_ctor_set(x_920, 2, x_3);
lean_ctor_set(x_920, 3, x_919);
lean_ctor_set_uint8(x_920, sizeof(void*)*4, x_639);
if (lean_is_scalar(x_918)) {
 x_921 = lean_alloc_ctor(1, 4, 1);
} else {
 x_921 = x_918;
}
lean_ctor_set(x_921, 0, x_912);
lean_ctor_set(x_921, 1, x_913);
lean_ctor_set(x_921, 2, x_914);
lean_ctor_set(x_921, 3, x_915);
lean_ctor_set_uint8(x_921, sizeof(void*)*4, x_639);
lean_ctor_set(x_1, 3, x_921);
lean_ctor_set(x_1, 2, x_906);
lean_ctor_set(x_1, 1, x_905);
lean_ctor_set(x_1, 0, x_920);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_862);
return x_1;
}
}
else
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
x_922 = lean_ctor_get(x_1, 1);
x_923 = lean_ctor_get(x_1, 2);
lean_inc(x_923);
lean_inc(x_922);
lean_dec(x_1);
x_924 = lean_ctor_get(x_4, 1);
lean_inc(x_924);
x_925 = lean_ctor_get(x_4, 2);
lean_inc(x_925);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_926 = x_4;
} else {
 lean_dec_ref(x_4);
 x_926 = lean_box(0);
}
x_927 = lean_ctor_get(x_679, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_679, 1);
lean_inc(x_928);
x_929 = lean_ctor_get(x_679, 2);
lean_inc(x_929);
x_930 = lean_ctor_get(x_679, 3);
lean_inc(x_930);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 lean_ctor_release(x_679, 2);
 lean_ctor_release(x_679, 3);
 x_931 = x_679;
} else {
 lean_dec_ref(x_679);
 x_931 = lean_box(0);
}
x_932 = lean_ctor_get(x_807, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_807, 1);
lean_inc(x_933);
x_934 = lean_ctor_get(x_807, 2);
lean_inc(x_934);
x_935 = lean_ctor_get(x_807, 3);
lean_inc(x_935);
if (lean_is_exclusive(x_807)) {
 lean_ctor_release(x_807, 0);
 lean_ctor_release(x_807, 1);
 lean_ctor_release(x_807, 2);
 lean_ctor_release(x_807, 3);
 x_936 = x_807;
} else {
 lean_dec_ref(x_807);
 x_936 = lean_box(0);
}
lean_inc(x_235);
if (lean_is_scalar(x_936)) {
 x_937 = lean_alloc_ctor(1, 4, 1);
} else {
 x_937 = x_936;
}
lean_ctor_set(x_937, 0, x_234);
lean_ctor_set(x_937, 1, x_922);
lean_ctor_set(x_937, 2, x_923);
lean_ctor_set(x_937, 3, x_235);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_938 = x_235;
} else {
 lean_dec_ref(x_235);
 x_938 = lean_box(0);
}
lean_ctor_set_uint8(x_937, sizeof(void*)*4, x_862);
if (lean_is_scalar(x_931)) {
 x_939 = lean_alloc_ctor(1, 4, 1);
} else {
 x_939 = x_931;
}
lean_ctor_set(x_939, 0, x_927);
lean_ctor_set(x_939, 1, x_928);
lean_ctor_set(x_939, 2, x_929);
lean_ctor_set(x_939, 3, x_930);
lean_ctor_set_uint8(x_939, sizeof(void*)*4, x_862);
if (lean_is_scalar(x_926)) {
 x_940 = lean_alloc_ctor(1, 4, 1);
} else {
 x_940 = x_926;
}
lean_ctor_set(x_940, 0, x_937);
lean_ctor_set(x_940, 1, x_2);
lean_ctor_set(x_940, 2, x_3);
lean_ctor_set(x_940, 3, x_939);
lean_ctor_set_uint8(x_940, sizeof(void*)*4, x_639);
if (lean_is_scalar(x_938)) {
 x_941 = lean_alloc_ctor(1, 4, 1);
} else {
 x_941 = x_938;
}
lean_ctor_set(x_941, 0, x_932);
lean_ctor_set(x_941, 1, x_933);
lean_ctor_set(x_941, 2, x_934);
lean_ctor_set(x_941, 3, x_935);
lean_ctor_set_uint8(x_941, sizeof(void*)*4, x_639);
x_942 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_942, 0, x_940);
lean_ctor_set(x_942, 1, x_924);
lean_ctor_set(x_942, 2, x_925);
lean_ctor_set(x_942, 3, x_941);
lean_ctor_set_uint8(x_942, sizeof(void*)*4, x_862);
return x_942;
}
}
else
{
uint8_t x_943; 
x_943 = !lean_is_exclusive(x_1);
if (x_943 == 0)
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; uint8_t x_948; 
x_944 = lean_ctor_get(x_1, 1);
x_945 = lean_ctor_get(x_1, 2);
x_946 = lean_ctor_get(x_1, 3);
lean_dec(x_946);
x_947 = lean_ctor_get(x_1, 0);
lean_dec(x_947);
x_948 = !lean_is_exclusive(x_235);
if (x_948 == 0)
{
uint8_t x_949; 
x_949 = !lean_is_exclusive(x_4);
if (x_949 == 0)
{
lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; uint8_t x_958; 
x_950 = lean_ctor_get(x_235, 0);
x_951 = lean_ctor_get(x_235, 1);
x_952 = lean_ctor_get(x_235, 2);
x_953 = lean_ctor_get(x_235, 3);
x_954 = lean_ctor_get(x_4, 1);
x_955 = lean_ctor_get(x_4, 2);
x_956 = lean_ctor_get(x_4, 3);
lean_dec(x_956);
x_957 = lean_ctor_get(x_4, 0);
lean_dec(x_957);
x_958 = !lean_is_exclusive(x_679);
if (x_958 == 0)
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; 
x_959 = lean_ctor_get(x_679, 0);
x_960 = lean_ctor_get(x_679, 1);
x_961 = lean_ctor_get(x_679, 2);
x_962 = lean_ctor_get(x_679, 3);
lean_ctor_set(x_679, 3, x_953);
lean_ctor_set(x_679, 2, x_952);
lean_ctor_set(x_679, 1, x_951);
lean_ctor_set(x_679, 0, x_950);
lean_ctor_set_uint8(x_679, sizeof(void*)*4, x_862);
lean_ctor_set(x_4, 3, x_679);
lean_ctor_set(x_4, 2, x_945);
lean_ctor_set(x_4, 1, x_944);
lean_ctor_set(x_4, 0, x_234);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_806);
lean_ctor_set(x_235, 3, x_959);
lean_ctor_set(x_235, 2, x_3);
lean_ctor_set(x_235, 1, x_2);
lean_ctor_set(x_235, 0, x_4);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_862);
lean_ctor_set(x_1, 3, x_807);
lean_ctor_set(x_1, 2, x_955);
lean_ctor_set(x_1, 1, x_954);
lean_ctor_set(x_1, 0, x_962);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_862);
x_963 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_963, 0, x_235);
lean_ctor_set(x_963, 1, x_960);
lean_ctor_set(x_963, 2, x_961);
lean_ctor_set(x_963, 3, x_1);
lean_ctor_set_uint8(x_963, sizeof(void*)*4, x_806);
return x_963;
}
else
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
x_964 = lean_ctor_get(x_679, 0);
x_965 = lean_ctor_get(x_679, 1);
x_966 = lean_ctor_get(x_679, 2);
x_967 = lean_ctor_get(x_679, 3);
lean_inc(x_967);
lean_inc(x_966);
lean_inc(x_965);
lean_inc(x_964);
lean_dec(x_679);
x_968 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_968, 0, x_950);
lean_ctor_set(x_968, 1, x_951);
lean_ctor_set(x_968, 2, x_952);
lean_ctor_set(x_968, 3, x_953);
lean_ctor_set_uint8(x_968, sizeof(void*)*4, x_862);
lean_ctor_set(x_4, 3, x_968);
lean_ctor_set(x_4, 2, x_945);
lean_ctor_set(x_4, 1, x_944);
lean_ctor_set(x_4, 0, x_234);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_806);
lean_ctor_set(x_235, 3, x_964);
lean_ctor_set(x_235, 2, x_3);
lean_ctor_set(x_235, 1, x_2);
lean_ctor_set(x_235, 0, x_4);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_862);
lean_ctor_set(x_1, 3, x_807);
lean_ctor_set(x_1, 2, x_955);
lean_ctor_set(x_1, 1, x_954);
lean_ctor_set(x_1, 0, x_967);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_862);
x_969 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_969, 0, x_235);
lean_ctor_set(x_969, 1, x_965);
lean_ctor_set(x_969, 2, x_966);
lean_ctor_set(x_969, 3, x_1);
lean_ctor_set_uint8(x_969, sizeof(void*)*4, x_806);
return x_969;
}
}
else
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_970 = lean_ctor_get(x_235, 0);
x_971 = lean_ctor_get(x_235, 1);
x_972 = lean_ctor_get(x_235, 2);
x_973 = lean_ctor_get(x_235, 3);
x_974 = lean_ctor_get(x_4, 1);
x_975 = lean_ctor_get(x_4, 2);
lean_inc(x_975);
lean_inc(x_974);
lean_dec(x_4);
x_976 = lean_ctor_get(x_679, 0);
lean_inc(x_976);
x_977 = lean_ctor_get(x_679, 1);
lean_inc(x_977);
x_978 = lean_ctor_get(x_679, 2);
lean_inc(x_978);
x_979 = lean_ctor_get(x_679, 3);
lean_inc(x_979);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 lean_ctor_release(x_679, 2);
 lean_ctor_release(x_679, 3);
 x_980 = x_679;
} else {
 lean_dec_ref(x_679);
 x_980 = lean_box(0);
}
if (lean_is_scalar(x_980)) {
 x_981 = lean_alloc_ctor(1, 4, 1);
} else {
 x_981 = x_980;
}
lean_ctor_set(x_981, 0, x_970);
lean_ctor_set(x_981, 1, x_971);
lean_ctor_set(x_981, 2, x_972);
lean_ctor_set(x_981, 3, x_973);
lean_ctor_set_uint8(x_981, sizeof(void*)*4, x_862);
x_982 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_982, 0, x_234);
lean_ctor_set(x_982, 1, x_944);
lean_ctor_set(x_982, 2, x_945);
lean_ctor_set(x_982, 3, x_981);
lean_ctor_set_uint8(x_982, sizeof(void*)*4, x_806);
lean_ctor_set(x_235, 3, x_976);
lean_ctor_set(x_235, 2, x_3);
lean_ctor_set(x_235, 1, x_2);
lean_ctor_set(x_235, 0, x_982);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_862);
lean_ctor_set(x_1, 3, x_807);
lean_ctor_set(x_1, 2, x_975);
lean_ctor_set(x_1, 1, x_974);
lean_ctor_set(x_1, 0, x_979);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_862);
x_983 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_983, 0, x_235);
lean_ctor_set(x_983, 1, x_977);
lean_ctor_set(x_983, 2, x_978);
lean_ctor_set(x_983, 3, x_1);
lean_ctor_set_uint8(x_983, sizeof(void*)*4, x_806);
return x_983;
}
}
else
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; 
x_984 = lean_ctor_get(x_235, 0);
x_985 = lean_ctor_get(x_235, 1);
x_986 = lean_ctor_get(x_235, 2);
x_987 = lean_ctor_get(x_235, 3);
lean_inc(x_987);
lean_inc(x_986);
lean_inc(x_985);
lean_inc(x_984);
lean_dec(x_235);
x_988 = lean_ctor_get(x_4, 1);
lean_inc(x_988);
x_989 = lean_ctor_get(x_4, 2);
lean_inc(x_989);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_990 = x_4;
} else {
 lean_dec_ref(x_4);
 x_990 = lean_box(0);
}
x_991 = lean_ctor_get(x_679, 0);
lean_inc(x_991);
x_992 = lean_ctor_get(x_679, 1);
lean_inc(x_992);
x_993 = lean_ctor_get(x_679, 2);
lean_inc(x_993);
x_994 = lean_ctor_get(x_679, 3);
lean_inc(x_994);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 lean_ctor_release(x_679, 2);
 lean_ctor_release(x_679, 3);
 x_995 = x_679;
} else {
 lean_dec_ref(x_679);
 x_995 = lean_box(0);
}
if (lean_is_scalar(x_995)) {
 x_996 = lean_alloc_ctor(1, 4, 1);
} else {
 x_996 = x_995;
}
lean_ctor_set(x_996, 0, x_984);
lean_ctor_set(x_996, 1, x_985);
lean_ctor_set(x_996, 2, x_986);
lean_ctor_set(x_996, 3, x_987);
lean_ctor_set_uint8(x_996, sizeof(void*)*4, x_862);
if (lean_is_scalar(x_990)) {
 x_997 = lean_alloc_ctor(1, 4, 1);
} else {
 x_997 = x_990;
}
lean_ctor_set(x_997, 0, x_234);
lean_ctor_set(x_997, 1, x_944);
lean_ctor_set(x_997, 2, x_945);
lean_ctor_set(x_997, 3, x_996);
lean_ctor_set_uint8(x_997, sizeof(void*)*4, x_806);
x_998 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_998, 0, x_997);
lean_ctor_set(x_998, 1, x_2);
lean_ctor_set(x_998, 2, x_3);
lean_ctor_set(x_998, 3, x_991);
lean_ctor_set_uint8(x_998, sizeof(void*)*4, x_862);
lean_ctor_set(x_1, 3, x_807);
lean_ctor_set(x_1, 2, x_989);
lean_ctor_set(x_1, 1, x_988);
lean_ctor_set(x_1, 0, x_994);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_862);
x_999 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_999, 0, x_998);
lean_ctor_set(x_999, 1, x_992);
lean_ctor_set(x_999, 2, x_993);
lean_ctor_set(x_999, 3, x_1);
lean_ctor_set_uint8(x_999, sizeof(void*)*4, x_806);
return x_999;
}
}
else
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1000 = lean_ctor_get(x_1, 1);
x_1001 = lean_ctor_get(x_1, 2);
lean_inc(x_1001);
lean_inc(x_1000);
lean_dec(x_1);
x_1002 = lean_ctor_get(x_235, 0);
lean_inc(x_1002);
x_1003 = lean_ctor_get(x_235, 1);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_235, 2);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_235, 3);
lean_inc(x_1005);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_1006 = x_235;
} else {
 lean_dec_ref(x_235);
 x_1006 = lean_box(0);
}
x_1007 = lean_ctor_get(x_4, 1);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_4, 2);
lean_inc(x_1008);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1009 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1009 = lean_box(0);
}
x_1010 = lean_ctor_get(x_679, 0);
lean_inc(x_1010);
x_1011 = lean_ctor_get(x_679, 1);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_679, 2);
lean_inc(x_1012);
x_1013 = lean_ctor_get(x_679, 3);
lean_inc(x_1013);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 lean_ctor_release(x_679, 2);
 lean_ctor_release(x_679, 3);
 x_1014 = x_679;
} else {
 lean_dec_ref(x_679);
 x_1014 = lean_box(0);
}
if (lean_is_scalar(x_1014)) {
 x_1015 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1015 = x_1014;
}
lean_ctor_set(x_1015, 0, x_1002);
lean_ctor_set(x_1015, 1, x_1003);
lean_ctor_set(x_1015, 2, x_1004);
lean_ctor_set(x_1015, 3, x_1005);
lean_ctor_set_uint8(x_1015, sizeof(void*)*4, x_862);
if (lean_is_scalar(x_1009)) {
 x_1016 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1016 = x_1009;
}
lean_ctor_set(x_1016, 0, x_234);
lean_ctor_set(x_1016, 1, x_1000);
lean_ctor_set(x_1016, 2, x_1001);
lean_ctor_set(x_1016, 3, x_1015);
lean_ctor_set_uint8(x_1016, sizeof(void*)*4, x_806);
if (lean_is_scalar(x_1006)) {
 x_1017 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1017 = x_1006;
}
lean_ctor_set(x_1017, 0, x_1016);
lean_ctor_set(x_1017, 1, x_2);
lean_ctor_set(x_1017, 2, x_3);
lean_ctor_set(x_1017, 3, x_1010);
lean_ctor_set_uint8(x_1017, sizeof(void*)*4, x_862);
x_1018 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1018, 0, x_1013);
lean_ctor_set(x_1018, 1, x_1007);
lean_ctor_set(x_1018, 2, x_1008);
lean_ctor_set(x_1018, 3, x_807);
lean_ctor_set_uint8(x_1018, sizeof(void*)*4, x_862);
x_1019 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1019, 0, x_1017);
lean_ctor_set(x_1019, 1, x_1011);
lean_ctor_set(x_1019, 2, x_1012);
lean_ctor_set(x_1019, 3, x_1018);
lean_ctor_set_uint8(x_1019, sizeof(void*)*4, x_806);
return x_1019;
}
}
}
}
else
{
lean_object* x_1020; 
x_1020 = lean_ctor_get(x_4, 3);
lean_inc(x_1020);
if (lean_obj_tag(x_1020) == 0)
{
uint8_t x_1021; 
x_1021 = !lean_is_exclusive(x_679);
if (x_1021 == 0)
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; uint8_t x_1026; 
x_1022 = lean_ctor_get(x_679, 3);
lean_dec(x_1022);
x_1023 = lean_ctor_get(x_679, 2);
lean_dec(x_1023);
x_1024 = lean_ctor_get(x_679, 1);
lean_dec(x_1024);
x_1025 = lean_ctor_get(x_679, 0);
lean_dec(x_1025);
x_1026 = !lean_is_exclusive(x_1);
if (x_1026 == 0)
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; uint8_t x_1031; 
x_1027 = lean_ctor_get(x_1, 1);
x_1028 = lean_ctor_get(x_1, 2);
x_1029 = lean_ctor_get(x_1, 3);
lean_dec(x_1029);
x_1030 = lean_ctor_get(x_1, 0);
lean_dec(x_1030);
x_1031 = !lean_is_exclusive(x_235);
if (x_1031 == 0)
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
x_1032 = lean_ctor_get(x_235, 0);
x_1033 = lean_ctor_get(x_235, 1);
x_1034 = lean_ctor_get(x_235, 2);
x_1035 = lean_ctor_get(x_235, 3);
lean_ctor_set(x_679, 3, x_1035);
lean_ctor_set(x_679, 2, x_1034);
lean_ctor_set(x_679, 1, x_1033);
lean_ctor_set(x_679, 0, x_1032);
lean_ctor_set(x_235, 3, x_679);
lean_ctor_set(x_235, 2, x_1028);
lean_ctor_set(x_235, 1, x_1027);
lean_ctor_set(x_235, 0, x_1020);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_678);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_806);
return x_1;
}
else
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
x_1036 = lean_ctor_get(x_235, 0);
x_1037 = lean_ctor_get(x_235, 1);
x_1038 = lean_ctor_get(x_235, 2);
x_1039 = lean_ctor_get(x_235, 3);
lean_inc(x_1039);
lean_inc(x_1038);
lean_inc(x_1037);
lean_inc(x_1036);
lean_dec(x_235);
lean_ctor_set(x_679, 3, x_1039);
lean_ctor_set(x_679, 2, x_1038);
lean_ctor_set(x_679, 1, x_1037);
lean_ctor_set(x_679, 0, x_1036);
x_1040 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1040, 0, x_1020);
lean_ctor_set(x_1040, 1, x_1027);
lean_ctor_set(x_1040, 2, x_1028);
lean_ctor_set(x_1040, 3, x_679);
lean_ctor_set_uint8(x_1040, sizeof(void*)*4, x_678);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_1040);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_806);
return x_1;
}
}
else
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; 
x_1041 = lean_ctor_get(x_1, 1);
x_1042 = lean_ctor_get(x_1, 2);
lean_inc(x_1042);
lean_inc(x_1041);
lean_dec(x_1);
x_1043 = lean_ctor_get(x_235, 0);
lean_inc(x_1043);
x_1044 = lean_ctor_get(x_235, 1);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_235, 2);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_235, 3);
lean_inc(x_1046);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_1047 = x_235;
} else {
 lean_dec_ref(x_235);
 x_1047 = lean_box(0);
}
lean_ctor_set(x_679, 3, x_1046);
lean_ctor_set(x_679, 2, x_1045);
lean_ctor_set(x_679, 1, x_1044);
lean_ctor_set(x_679, 0, x_1043);
if (lean_is_scalar(x_1047)) {
 x_1048 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1048 = x_1047;
}
lean_ctor_set(x_1048, 0, x_1020);
lean_ctor_set(x_1048, 1, x_1041);
lean_ctor_set(x_1048, 2, x_1042);
lean_ctor_set(x_1048, 3, x_679);
lean_ctor_set_uint8(x_1048, sizeof(void*)*4, x_678);
x_1049 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1049, 0, x_1048);
lean_ctor_set(x_1049, 1, x_2);
lean_ctor_set(x_1049, 2, x_3);
lean_ctor_set(x_1049, 3, x_4);
lean_ctor_set_uint8(x_1049, sizeof(void*)*4, x_806);
return x_1049;
}
}
else
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
lean_dec(x_679);
x_1050 = lean_ctor_get(x_1, 1);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1, 2);
lean_inc(x_1051);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_1052 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1052 = lean_box(0);
}
x_1053 = lean_ctor_get(x_235, 0);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_235, 1);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_235, 2);
lean_inc(x_1055);
x_1056 = lean_ctor_get(x_235, 3);
lean_inc(x_1056);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_1057 = x_235;
} else {
 lean_dec_ref(x_235);
 x_1057 = lean_box(0);
}
x_1058 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1058, 0, x_1053);
lean_ctor_set(x_1058, 1, x_1054);
lean_ctor_set(x_1058, 2, x_1055);
lean_ctor_set(x_1058, 3, x_1056);
lean_ctor_set_uint8(x_1058, sizeof(void*)*4, x_806);
if (lean_is_scalar(x_1057)) {
 x_1059 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1059 = x_1057;
}
lean_ctor_set(x_1059, 0, x_1020);
lean_ctor_set(x_1059, 1, x_1050);
lean_ctor_set(x_1059, 2, x_1051);
lean_ctor_set(x_1059, 3, x_1058);
lean_ctor_set_uint8(x_1059, sizeof(void*)*4, x_678);
if (lean_is_scalar(x_1052)) {
 x_1060 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1060 = x_1052;
}
lean_ctor_set(x_1060, 0, x_1059);
lean_ctor_set(x_1060, 1, x_2);
lean_ctor_set(x_1060, 2, x_3);
lean_ctor_set(x_1060, 3, x_4);
lean_ctor_set_uint8(x_1060, sizeof(void*)*4, x_806);
return x_1060;
}
}
else
{
uint8_t x_1061; 
x_1061 = lean_ctor_get_uint8(x_1020, sizeof(void*)*4);
if (x_1061 == 0)
{
uint8_t x_1062; 
x_1062 = !lean_is_exclusive(x_1);
if (x_1062 == 0)
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; uint8_t x_1067; 
x_1063 = lean_ctor_get(x_1, 1);
x_1064 = lean_ctor_get(x_1, 2);
x_1065 = lean_ctor_get(x_1, 3);
lean_dec(x_1065);
x_1066 = lean_ctor_get(x_1, 0);
lean_dec(x_1066);
x_1067 = !lean_is_exclusive(x_235);
if (x_1067 == 0)
{
uint8_t x_1068; 
x_1068 = !lean_is_exclusive(x_4);
if (x_1068 == 0)
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; uint8_t x_1077; 
x_1069 = lean_ctor_get(x_235, 0);
x_1070 = lean_ctor_get(x_235, 1);
x_1071 = lean_ctor_get(x_235, 2);
x_1072 = lean_ctor_get(x_235, 3);
x_1073 = lean_ctor_get(x_4, 1);
x_1074 = lean_ctor_get(x_4, 2);
x_1075 = lean_ctor_get(x_4, 3);
lean_dec(x_1075);
x_1076 = lean_ctor_get(x_4, 0);
lean_dec(x_1076);
x_1077 = !lean_is_exclusive(x_1020);
if (x_1077 == 0)
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; 
x_1078 = lean_ctor_get(x_1020, 0);
x_1079 = lean_ctor_get(x_1020, 1);
x_1080 = lean_ctor_get(x_1020, 2);
x_1081 = lean_ctor_get(x_1020, 3);
lean_ctor_set(x_1020, 3, x_1072);
lean_ctor_set(x_1020, 2, x_1071);
lean_ctor_set(x_1020, 1, x_1070);
lean_ctor_set(x_1020, 0, x_1069);
lean_ctor_set_uint8(x_1020, sizeof(void*)*4, x_806);
lean_ctor_set(x_4, 2, x_1064);
lean_ctor_set(x_4, 1, x_1063);
lean_ctor_set(x_4, 0, x_234);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1061);
lean_ctor_set(x_235, 3, x_679);
lean_ctor_set(x_235, 2, x_3);
lean_ctor_set(x_235, 1, x_2);
lean_ctor_set(x_235, 0, x_4);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_806);
lean_ctor_set(x_1, 3, x_1081);
lean_ctor_set(x_1, 2, x_1080);
lean_ctor_set(x_1, 1, x_1079);
lean_ctor_set(x_1, 0, x_1078);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_806);
x_1082 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1082, 0, x_235);
lean_ctor_set(x_1082, 1, x_1073);
lean_ctor_set(x_1082, 2, x_1074);
lean_ctor_set(x_1082, 3, x_1);
lean_ctor_set_uint8(x_1082, sizeof(void*)*4, x_1061);
return x_1082;
}
else
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; 
x_1083 = lean_ctor_get(x_1020, 0);
x_1084 = lean_ctor_get(x_1020, 1);
x_1085 = lean_ctor_get(x_1020, 2);
x_1086 = lean_ctor_get(x_1020, 3);
lean_inc(x_1086);
lean_inc(x_1085);
lean_inc(x_1084);
lean_inc(x_1083);
lean_dec(x_1020);
x_1087 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1087, 0, x_1069);
lean_ctor_set(x_1087, 1, x_1070);
lean_ctor_set(x_1087, 2, x_1071);
lean_ctor_set(x_1087, 3, x_1072);
lean_ctor_set_uint8(x_1087, sizeof(void*)*4, x_806);
lean_ctor_set(x_4, 3, x_1087);
lean_ctor_set(x_4, 2, x_1064);
lean_ctor_set(x_4, 1, x_1063);
lean_ctor_set(x_4, 0, x_234);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1061);
lean_ctor_set(x_235, 3, x_679);
lean_ctor_set(x_235, 2, x_3);
lean_ctor_set(x_235, 1, x_2);
lean_ctor_set(x_235, 0, x_4);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_806);
lean_ctor_set(x_1, 3, x_1086);
lean_ctor_set(x_1, 2, x_1085);
lean_ctor_set(x_1, 1, x_1084);
lean_ctor_set(x_1, 0, x_1083);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_806);
x_1088 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1088, 0, x_235);
lean_ctor_set(x_1088, 1, x_1073);
lean_ctor_set(x_1088, 2, x_1074);
lean_ctor_set(x_1088, 3, x_1);
lean_ctor_set_uint8(x_1088, sizeof(void*)*4, x_1061);
return x_1088;
}
}
else
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; 
x_1089 = lean_ctor_get(x_235, 0);
x_1090 = lean_ctor_get(x_235, 1);
x_1091 = lean_ctor_get(x_235, 2);
x_1092 = lean_ctor_get(x_235, 3);
x_1093 = lean_ctor_get(x_4, 1);
x_1094 = lean_ctor_get(x_4, 2);
lean_inc(x_1094);
lean_inc(x_1093);
lean_dec(x_4);
x_1095 = lean_ctor_get(x_1020, 0);
lean_inc(x_1095);
x_1096 = lean_ctor_get(x_1020, 1);
lean_inc(x_1096);
x_1097 = lean_ctor_get(x_1020, 2);
lean_inc(x_1097);
x_1098 = lean_ctor_get(x_1020, 3);
lean_inc(x_1098);
if (lean_is_exclusive(x_1020)) {
 lean_ctor_release(x_1020, 0);
 lean_ctor_release(x_1020, 1);
 lean_ctor_release(x_1020, 2);
 lean_ctor_release(x_1020, 3);
 x_1099 = x_1020;
} else {
 lean_dec_ref(x_1020);
 x_1099 = lean_box(0);
}
if (lean_is_scalar(x_1099)) {
 x_1100 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1100 = x_1099;
}
lean_ctor_set(x_1100, 0, x_1089);
lean_ctor_set(x_1100, 1, x_1090);
lean_ctor_set(x_1100, 2, x_1091);
lean_ctor_set(x_1100, 3, x_1092);
lean_ctor_set_uint8(x_1100, sizeof(void*)*4, x_806);
x_1101 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1101, 0, x_234);
lean_ctor_set(x_1101, 1, x_1063);
lean_ctor_set(x_1101, 2, x_1064);
lean_ctor_set(x_1101, 3, x_1100);
lean_ctor_set_uint8(x_1101, sizeof(void*)*4, x_1061);
lean_ctor_set(x_235, 3, x_679);
lean_ctor_set(x_235, 2, x_3);
lean_ctor_set(x_235, 1, x_2);
lean_ctor_set(x_235, 0, x_1101);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_806);
lean_ctor_set(x_1, 3, x_1098);
lean_ctor_set(x_1, 2, x_1097);
lean_ctor_set(x_1, 1, x_1096);
lean_ctor_set(x_1, 0, x_1095);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_806);
x_1102 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1102, 0, x_235);
lean_ctor_set(x_1102, 1, x_1093);
lean_ctor_set(x_1102, 2, x_1094);
lean_ctor_set(x_1102, 3, x_1);
lean_ctor_set_uint8(x_1102, sizeof(void*)*4, x_1061);
return x_1102;
}
}
else
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1103 = lean_ctor_get(x_235, 0);
x_1104 = lean_ctor_get(x_235, 1);
x_1105 = lean_ctor_get(x_235, 2);
x_1106 = lean_ctor_get(x_235, 3);
lean_inc(x_1106);
lean_inc(x_1105);
lean_inc(x_1104);
lean_inc(x_1103);
lean_dec(x_235);
x_1107 = lean_ctor_get(x_4, 1);
lean_inc(x_1107);
x_1108 = lean_ctor_get(x_4, 2);
lean_inc(x_1108);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1109 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1109 = lean_box(0);
}
x_1110 = lean_ctor_get(x_1020, 0);
lean_inc(x_1110);
x_1111 = lean_ctor_get(x_1020, 1);
lean_inc(x_1111);
x_1112 = lean_ctor_get(x_1020, 2);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1020, 3);
lean_inc(x_1113);
if (lean_is_exclusive(x_1020)) {
 lean_ctor_release(x_1020, 0);
 lean_ctor_release(x_1020, 1);
 lean_ctor_release(x_1020, 2);
 lean_ctor_release(x_1020, 3);
 x_1114 = x_1020;
} else {
 lean_dec_ref(x_1020);
 x_1114 = lean_box(0);
}
if (lean_is_scalar(x_1114)) {
 x_1115 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1115 = x_1114;
}
lean_ctor_set(x_1115, 0, x_1103);
lean_ctor_set(x_1115, 1, x_1104);
lean_ctor_set(x_1115, 2, x_1105);
lean_ctor_set(x_1115, 3, x_1106);
lean_ctor_set_uint8(x_1115, sizeof(void*)*4, x_806);
if (lean_is_scalar(x_1109)) {
 x_1116 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1116 = x_1109;
}
lean_ctor_set(x_1116, 0, x_234);
lean_ctor_set(x_1116, 1, x_1063);
lean_ctor_set(x_1116, 2, x_1064);
lean_ctor_set(x_1116, 3, x_1115);
lean_ctor_set_uint8(x_1116, sizeof(void*)*4, x_1061);
x_1117 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1117, 0, x_1116);
lean_ctor_set(x_1117, 1, x_2);
lean_ctor_set(x_1117, 2, x_3);
lean_ctor_set(x_1117, 3, x_679);
lean_ctor_set_uint8(x_1117, sizeof(void*)*4, x_806);
lean_ctor_set(x_1, 3, x_1113);
lean_ctor_set(x_1, 2, x_1112);
lean_ctor_set(x_1, 1, x_1111);
lean_ctor_set(x_1, 0, x_1110);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_806);
x_1118 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1118, 0, x_1117);
lean_ctor_set(x_1118, 1, x_1107);
lean_ctor_set(x_1118, 2, x_1108);
lean_ctor_set(x_1118, 3, x_1);
lean_ctor_set_uint8(x_1118, sizeof(void*)*4, x_1061);
return x_1118;
}
}
else
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; 
x_1119 = lean_ctor_get(x_1, 1);
x_1120 = lean_ctor_get(x_1, 2);
lean_inc(x_1120);
lean_inc(x_1119);
lean_dec(x_1);
x_1121 = lean_ctor_get(x_235, 0);
lean_inc(x_1121);
x_1122 = lean_ctor_get(x_235, 1);
lean_inc(x_1122);
x_1123 = lean_ctor_get(x_235, 2);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_235, 3);
lean_inc(x_1124);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_1125 = x_235;
} else {
 lean_dec_ref(x_235);
 x_1125 = lean_box(0);
}
x_1126 = lean_ctor_get(x_4, 1);
lean_inc(x_1126);
x_1127 = lean_ctor_get(x_4, 2);
lean_inc(x_1127);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1128 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1128 = lean_box(0);
}
x_1129 = lean_ctor_get(x_1020, 0);
lean_inc(x_1129);
x_1130 = lean_ctor_get(x_1020, 1);
lean_inc(x_1130);
x_1131 = lean_ctor_get(x_1020, 2);
lean_inc(x_1131);
x_1132 = lean_ctor_get(x_1020, 3);
lean_inc(x_1132);
if (lean_is_exclusive(x_1020)) {
 lean_ctor_release(x_1020, 0);
 lean_ctor_release(x_1020, 1);
 lean_ctor_release(x_1020, 2);
 lean_ctor_release(x_1020, 3);
 x_1133 = x_1020;
} else {
 lean_dec_ref(x_1020);
 x_1133 = lean_box(0);
}
if (lean_is_scalar(x_1133)) {
 x_1134 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1134 = x_1133;
}
lean_ctor_set(x_1134, 0, x_1121);
lean_ctor_set(x_1134, 1, x_1122);
lean_ctor_set(x_1134, 2, x_1123);
lean_ctor_set(x_1134, 3, x_1124);
lean_ctor_set_uint8(x_1134, sizeof(void*)*4, x_806);
if (lean_is_scalar(x_1128)) {
 x_1135 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1135 = x_1128;
}
lean_ctor_set(x_1135, 0, x_234);
lean_ctor_set(x_1135, 1, x_1119);
lean_ctor_set(x_1135, 2, x_1120);
lean_ctor_set(x_1135, 3, x_1134);
lean_ctor_set_uint8(x_1135, sizeof(void*)*4, x_1061);
if (lean_is_scalar(x_1125)) {
 x_1136 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1136 = x_1125;
}
lean_ctor_set(x_1136, 0, x_1135);
lean_ctor_set(x_1136, 1, x_2);
lean_ctor_set(x_1136, 2, x_3);
lean_ctor_set(x_1136, 3, x_679);
lean_ctor_set_uint8(x_1136, sizeof(void*)*4, x_806);
x_1137 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1137, 0, x_1129);
lean_ctor_set(x_1137, 1, x_1130);
lean_ctor_set(x_1137, 2, x_1131);
lean_ctor_set(x_1137, 3, x_1132);
lean_ctor_set_uint8(x_1137, sizeof(void*)*4, x_806);
x_1138 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1138, 0, x_1136);
lean_ctor_set(x_1138, 1, x_1126);
lean_ctor_set(x_1138, 2, x_1127);
lean_ctor_set(x_1138, 3, x_1137);
lean_ctor_set_uint8(x_1138, sizeof(void*)*4, x_1061);
return x_1138;
}
}
else
{
uint8_t x_1139; 
x_1139 = !lean_is_exclusive(x_1);
if (x_1139 == 0)
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; uint8_t x_1144; 
x_1140 = lean_ctor_get(x_1, 1);
x_1141 = lean_ctor_get(x_1, 2);
x_1142 = lean_ctor_get(x_1, 3);
lean_dec(x_1142);
x_1143 = lean_ctor_get(x_1, 0);
lean_dec(x_1143);
x_1144 = !lean_is_exclusive(x_235);
if (x_1144 == 0)
{
uint8_t x_1145; 
x_1145 = !lean_is_exclusive(x_4);
if (x_1145 == 0)
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; uint8_t x_1154; 
x_1146 = lean_ctor_get(x_235, 0);
x_1147 = lean_ctor_get(x_235, 1);
x_1148 = lean_ctor_get(x_235, 2);
x_1149 = lean_ctor_get(x_235, 3);
x_1150 = lean_ctor_get(x_4, 1);
x_1151 = lean_ctor_get(x_4, 2);
x_1152 = lean_ctor_get(x_4, 3);
lean_dec(x_1152);
x_1153 = lean_ctor_get(x_4, 0);
lean_dec(x_1153);
x_1154 = !lean_is_exclusive(x_679);
if (x_1154 == 0)
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
x_1155 = lean_ctor_get(x_679, 0);
x_1156 = lean_ctor_get(x_679, 1);
x_1157 = lean_ctor_get(x_679, 2);
x_1158 = lean_ctor_get(x_679, 3);
lean_ctor_set(x_679, 3, x_1149);
lean_ctor_set(x_679, 2, x_1148);
lean_ctor_set(x_679, 1, x_1147);
lean_ctor_set(x_679, 0, x_1146);
lean_ctor_set_uint8(x_679, sizeof(void*)*4, x_1061);
lean_ctor_set(x_4, 3, x_679);
lean_ctor_set(x_4, 2, x_1141);
lean_ctor_set(x_4, 1, x_1140);
lean_ctor_set(x_4, 0, x_234);
lean_ctor_set(x_235, 3, x_1158);
lean_ctor_set(x_235, 2, x_1157);
lean_ctor_set(x_235, 1, x_1156);
lean_ctor_set(x_235, 0, x_1155);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_1061);
lean_ctor_set(x_1, 3, x_1020);
lean_ctor_set(x_1, 2, x_1151);
lean_ctor_set(x_1, 1, x_1150);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_678);
x_1159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1159, 0, x_4);
lean_ctor_set(x_1159, 1, x_2);
lean_ctor_set(x_1159, 2, x_3);
lean_ctor_set(x_1159, 3, x_1);
lean_ctor_set_uint8(x_1159, sizeof(void*)*4, x_1061);
return x_1159;
}
else
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; 
x_1160 = lean_ctor_get(x_679, 0);
x_1161 = lean_ctor_get(x_679, 1);
x_1162 = lean_ctor_get(x_679, 2);
x_1163 = lean_ctor_get(x_679, 3);
lean_inc(x_1163);
lean_inc(x_1162);
lean_inc(x_1161);
lean_inc(x_1160);
lean_dec(x_679);
x_1164 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1164, 0, x_1146);
lean_ctor_set(x_1164, 1, x_1147);
lean_ctor_set(x_1164, 2, x_1148);
lean_ctor_set(x_1164, 3, x_1149);
lean_ctor_set_uint8(x_1164, sizeof(void*)*4, x_1061);
lean_ctor_set(x_4, 3, x_1164);
lean_ctor_set(x_4, 2, x_1141);
lean_ctor_set(x_4, 1, x_1140);
lean_ctor_set(x_4, 0, x_234);
lean_ctor_set(x_235, 3, x_1163);
lean_ctor_set(x_235, 2, x_1162);
lean_ctor_set(x_235, 1, x_1161);
lean_ctor_set(x_235, 0, x_1160);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_1061);
lean_ctor_set(x_1, 3, x_1020);
lean_ctor_set(x_1, 2, x_1151);
lean_ctor_set(x_1, 1, x_1150);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_678);
x_1165 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1165, 0, x_4);
lean_ctor_set(x_1165, 1, x_2);
lean_ctor_set(x_1165, 2, x_3);
lean_ctor_set(x_1165, 3, x_1);
lean_ctor_set_uint8(x_1165, sizeof(void*)*4, x_1061);
return x_1165;
}
}
else
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; 
x_1166 = lean_ctor_get(x_235, 0);
x_1167 = lean_ctor_get(x_235, 1);
x_1168 = lean_ctor_get(x_235, 2);
x_1169 = lean_ctor_get(x_235, 3);
x_1170 = lean_ctor_get(x_4, 1);
x_1171 = lean_ctor_get(x_4, 2);
lean_inc(x_1171);
lean_inc(x_1170);
lean_dec(x_4);
x_1172 = lean_ctor_get(x_679, 0);
lean_inc(x_1172);
x_1173 = lean_ctor_get(x_679, 1);
lean_inc(x_1173);
x_1174 = lean_ctor_get(x_679, 2);
lean_inc(x_1174);
x_1175 = lean_ctor_get(x_679, 3);
lean_inc(x_1175);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 lean_ctor_release(x_679, 2);
 lean_ctor_release(x_679, 3);
 x_1176 = x_679;
} else {
 lean_dec_ref(x_679);
 x_1176 = lean_box(0);
}
if (lean_is_scalar(x_1176)) {
 x_1177 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1177 = x_1176;
}
lean_ctor_set(x_1177, 0, x_1166);
lean_ctor_set(x_1177, 1, x_1167);
lean_ctor_set(x_1177, 2, x_1168);
lean_ctor_set(x_1177, 3, x_1169);
lean_ctor_set_uint8(x_1177, sizeof(void*)*4, x_1061);
x_1178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1178, 0, x_234);
lean_ctor_set(x_1178, 1, x_1140);
lean_ctor_set(x_1178, 2, x_1141);
lean_ctor_set(x_1178, 3, x_1177);
lean_ctor_set_uint8(x_1178, sizeof(void*)*4, x_678);
lean_ctor_set(x_235, 3, x_1175);
lean_ctor_set(x_235, 2, x_1174);
lean_ctor_set(x_235, 1, x_1173);
lean_ctor_set(x_235, 0, x_1172);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_1061);
lean_ctor_set(x_1, 3, x_1020);
lean_ctor_set(x_1, 2, x_1171);
lean_ctor_set(x_1, 1, x_1170);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_678);
x_1179 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1179, 0, x_1178);
lean_ctor_set(x_1179, 1, x_2);
lean_ctor_set(x_1179, 2, x_3);
lean_ctor_set(x_1179, 3, x_1);
lean_ctor_set_uint8(x_1179, sizeof(void*)*4, x_1061);
return x_1179;
}
}
else
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
x_1180 = lean_ctor_get(x_235, 0);
x_1181 = lean_ctor_get(x_235, 1);
x_1182 = lean_ctor_get(x_235, 2);
x_1183 = lean_ctor_get(x_235, 3);
lean_inc(x_1183);
lean_inc(x_1182);
lean_inc(x_1181);
lean_inc(x_1180);
lean_dec(x_235);
x_1184 = lean_ctor_get(x_4, 1);
lean_inc(x_1184);
x_1185 = lean_ctor_get(x_4, 2);
lean_inc(x_1185);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1186 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1186 = lean_box(0);
}
x_1187 = lean_ctor_get(x_679, 0);
lean_inc(x_1187);
x_1188 = lean_ctor_get(x_679, 1);
lean_inc(x_1188);
x_1189 = lean_ctor_get(x_679, 2);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_679, 3);
lean_inc(x_1190);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 lean_ctor_release(x_679, 2);
 lean_ctor_release(x_679, 3);
 x_1191 = x_679;
} else {
 lean_dec_ref(x_679);
 x_1191 = lean_box(0);
}
if (lean_is_scalar(x_1191)) {
 x_1192 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1192 = x_1191;
}
lean_ctor_set(x_1192, 0, x_1180);
lean_ctor_set(x_1192, 1, x_1181);
lean_ctor_set(x_1192, 2, x_1182);
lean_ctor_set(x_1192, 3, x_1183);
lean_ctor_set_uint8(x_1192, sizeof(void*)*4, x_1061);
if (lean_is_scalar(x_1186)) {
 x_1193 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1193 = x_1186;
}
lean_ctor_set(x_1193, 0, x_234);
lean_ctor_set(x_1193, 1, x_1140);
lean_ctor_set(x_1193, 2, x_1141);
lean_ctor_set(x_1193, 3, x_1192);
lean_ctor_set_uint8(x_1193, sizeof(void*)*4, x_678);
x_1194 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1194, 0, x_1187);
lean_ctor_set(x_1194, 1, x_1188);
lean_ctor_set(x_1194, 2, x_1189);
lean_ctor_set(x_1194, 3, x_1190);
lean_ctor_set_uint8(x_1194, sizeof(void*)*4, x_1061);
lean_ctor_set(x_1, 3, x_1020);
lean_ctor_set(x_1, 2, x_1185);
lean_ctor_set(x_1, 1, x_1184);
lean_ctor_set(x_1, 0, x_1194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_678);
x_1195 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1195, 0, x_1193);
lean_ctor_set(x_1195, 1, x_2);
lean_ctor_set(x_1195, 2, x_3);
lean_ctor_set(x_1195, 3, x_1);
lean_ctor_set_uint8(x_1195, sizeof(void*)*4, x_1061);
return x_1195;
}
}
else
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; 
x_1196 = lean_ctor_get(x_1, 1);
x_1197 = lean_ctor_get(x_1, 2);
lean_inc(x_1197);
lean_inc(x_1196);
lean_dec(x_1);
x_1198 = lean_ctor_get(x_235, 0);
lean_inc(x_1198);
x_1199 = lean_ctor_get(x_235, 1);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_235, 2);
lean_inc(x_1200);
x_1201 = lean_ctor_get(x_235, 3);
lean_inc(x_1201);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_1202 = x_235;
} else {
 lean_dec_ref(x_235);
 x_1202 = lean_box(0);
}
x_1203 = lean_ctor_get(x_4, 1);
lean_inc(x_1203);
x_1204 = lean_ctor_get(x_4, 2);
lean_inc(x_1204);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1205 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1205 = lean_box(0);
}
x_1206 = lean_ctor_get(x_679, 0);
lean_inc(x_1206);
x_1207 = lean_ctor_get(x_679, 1);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_679, 2);
lean_inc(x_1208);
x_1209 = lean_ctor_get(x_679, 3);
lean_inc(x_1209);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 lean_ctor_release(x_679, 2);
 lean_ctor_release(x_679, 3);
 x_1210 = x_679;
} else {
 lean_dec_ref(x_679);
 x_1210 = lean_box(0);
}
if (lean_is_scalar(x_1210)) {
 x_1211 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1211 = x_1210;
}
lean_ctor_set(x_1211, 0, x_1198);
lean_ctor_set(x_1211, 1, x_1199);
lean_ctor_set(x_1211, 2, x_1200);
lean_ctor_set(x_1211, 3, x_1201);
lean_ctor_set_uint8(x_1211, sizeof(void*)*4, x_1061);
if (lean_is_scalar(x_1205)) {
 x_1212 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1212 = x_1205;
}
lean_ctor_set(x_1212, 0, x_234);
lean_ctor_set(x_1212, 1, x_1196);
lean_ctor_set(x_1212, 2, x_1197);
lean_ctor_set(x_1212, 3, x_1211);
lean_ctor_set_uint8(x_1212, sizeof(void*)*4, x_678);
if (lean_is_scalar(x_1202)) {
 x_1213 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1213 = x_1202;
}
lean_ctor_set(x_1213, 0, x_1206);
lean_ctor_set(x_1213, 1, x_1207);
lean_ctor_set(x_1213, 2, x_1208);
lean_ctor_set(x_1213, 3, x_1209);
lean_ctor_set_uint8(x_1213, sizeof(void*)*4, x_1061);
x_1214 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1214, 0, x_1213);
lean_ctor_set(x_1214, 1, x_1203);
lean_ctor_set(x_1214, 2, x_1204);
lean_ctor_set(x_1214, 3, x_1020);
lean_ctor_set_uint8(x_1214, sizeof(void*)*4, x_678);
x_1215 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1215, 0, x_1212);
lean_ctor_set(x_1215, 1, x_2);
lean_ctor_set(x_1215, 2, x_3);
lean_ctor_set(x_1215, 3, x_1214);
lean_ctor_set_uint8(x_1215, sizeof(void*)*4, x_1061);
return x_1215;
}
}
}
}
}
}
else
{
uint8_t x_1216; 
x_1216 = !lean_is_exclusive(x_1);
if (x_1216 == 0)
{
lean_object* x_1217; lean_object* x_1218; uint8_t x_1219; 
x_1217 = lean_ctor_get(x_1, 3);
lean_dec(x_1217);
x_1218 = lean_ctor_get(x_1, 0);
lean_dec(x_1218);
x_1219 = !lean_is_exclusive(x_235);
if (x_1219 == 0)
{
lean_object* x_1220; 
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_678);
x_1220 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1220, 0, x_1);
lean_ctor_set(x_1220, 1, x_2);
lean_ctor_set(x_1220, 2, x_3);
lean_ctor_set(x_1220, 3, x_4);
lean_ctor_set_uint8(x_1220, sizeof(void*)*4, x_678);
return x_1220;
}
else
{
lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; 
x_1221 = lean_ctor_get(x_235, 0);
x_1222 = lean_ctor_get(x_235, 1);
x_1223 = lean_ctor_get(x_235, 2);
x_1224 = lean_ctor_get(x_235, 3);
lean_inc(x_1224);
lean_inc(x_1223);
lean_inc(x_1222);
lean_inc(x_1221);
lean_dec(x_235);
x_1225 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1225, 0, x_1221);
lean_ctor_set(x_1225, 1, x_1222);
lean_ctor_set(x_1225, 2, x_1223);
lean_ctor_set(x_1225, 3, x_1224);
lean_ctor_set_uint8(x_1225, sizeof(void*)*4, x_678);
lean_ctor_set(x_1, 3, x_1225);
x_1226 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1226, 0, x_1);
lean_ctor_set(x_1226, 1, x_2);
lean_ctor_set(x_1226, 2, x_3);
lean_ctor_set(x_1226, 3, x_4);
lean_ctor_set_uint8(x_1226, sizeof(void*)*4, x_678);
return x_1226;
}
}
else
{
lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; 
x_1227 = lean_ctor_get(x_1, 1);
x_1228 = lean_ctor_get(x_1, 2);
lean_inc(x_1228);
lean_inc(x_1227);
lean_dec(x_1);
x_1229 = lean_ctor_get(x_235, 0);
lean_inc(x_1229);
x_1230 = lean_ctor_get(x_235, 1);
lean_inc(x_1230);
x_1231 = lean_ctor_get(x_235, 2);
lean_inc(x_1231);
x_1232 = lean_ctor_get(x_235, 3);
lean_inc(x_1232);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 x_1233 = x_235;
} else {
 lean_dec_ref(x_235);
 x_1233 = lean_box(0);
}
if (lean_is_scalar(x_1233)) {
 x_1234 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1234 = x_1233;
}
lean_ctor_set(x_1234, 0, x_1229);
lean_ctor_set(x_1234, 1, x_1230);
lean_ctor_set(x_1234, 2, x_1231);
lean_ctor_set(x_1234, 3, x_1232);
lean_ctor_set_uint8(x_1234, sizeof(void*)*4, x_678);
x_1235 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1235, 0, x_234);
lean_ctor_set(x_1235, 1, x_1227);
lean_ctor_set(x_1235, 2, x_1228);
lean_ctor_set(x_1235, 3, x_1234);
lean_ctor_set_uint8(x_1235, sizeof(void*)*4, x_233);
x_1236 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1236, 0, x_1235);
lean_ctor_set(x_1236, 1, x_2);
lean_ctor_set(x_1236, 2, x_3);
lean_ctor_set(x_1236, 3, x_4);
lean_ctor_set_uint8(x_1236, sizeof(void*)*4, x_678);
return x_1236;
}
}
}
}
}
}
else
{
uint8_t x_1237; 
x_1237 = lean_ctor_get_uint8(x_234, sizeof(void*)*4);
if (x_1237 == 0)
{
uint8_t x_1238; 
x_1238 = !lean_is_exclusive(x_1);
if (x_1238 == 0)
{
lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; uint8_t x_1243; 
x_1239 = lean_ctor_get(x_1, 1);
x_1240 = lean_ctor_get(x_1, 2);
x_1241 = lean_ctor_get(x_1, 3);
x_1242 = lean_ctor_get(x_1, 0);
lean_dec(x_1242);
x_1243 = !lean_is_exclusive(x_234);
if (x_1243 == 0)
{
uint8_t x_1244; lean_object* x_1245; 
x_1244 = 1;
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1244);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_1241);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1244);
x_1245 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1245, 0, x_234);
lean_ctor_set(x_1245, 1, x_1239);
lean_ctor_set(x_1245, 2, x_1240);
lean_ctor_set(x_1245, 3, x_1);
lean_ctor_set_uint8(x_1245, sizeof(void*)*4, x_1237);
return x_1245;
}
else
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; uint8_t x_1250; lean_object* x_1251; lean_object* x_1252; 
x_1246 = lean_ctor_get(x_234, 0);
x_1247 = lean_ctor_get(x_234, 1);
x_1248 = lean_ctor_get(x_234, 2);
x_1249 = lean_ctor_get(x_234, 3);
lean_inc(x_1249);
lean_inc(x_1248);
lean_inc(x_1247);
lean_inc(x_1246);
lean_dec(x_234);
x_1250 = 1;
x_1251 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1251, 0, x_1246);
lean_ctor_set(x_1251, 1, x_1247);
lean_ctor_set(x_1251, 2, x_1248);
lean_ctor_set(x_1251, 3, x_1249);
lean_ctor_set_uint8(x_1251, sizeof(void*)*4, x_1250);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_1241);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1250);
x_1252 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1252, 0, x_1251);
lean_ctor_set(x_1252, 1, x_1239);
lean_ctor_set(x_1252, 2, x_1240);
lean_ctor_set(x_1252, 3, x_1);
lean_ctor_set_uint8(x_1252, sizeof(void*)*4, x_1237);
return x_1252;
}
}
else
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; uint8_t x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; 
x_1253 = lean_ctor_get(x_1, 1);
x_1254 = lean_ctor_get(x_1, 2);
x_1255 = lean_ctor_get(x_1, 3);
lean_inc(x_1255);
lean_inc(x_1254);
lean_inc(x_1253);
lean_dec(x_1);
x_1256 = lean_ctor_get(x_234, 0);
lean_inc(x_1256);
x_1257 = lean_ctor_get(x_234, 1);
lean_inc(x_1257);
x_1258 = lean_ctor_get(x_234, 2);
lean_inc(x_1258);
x_1259 = lean_ctor_get(x_234, 3);
lean_inc(x_1259);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1260 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1260 = lean_box(0);
}
x_1261 = 1;
if (lean_is_scalar(x_1260)) {
 x_1262 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1262 = x_1260;
}
lean_ctor_set(x_1262, 0, x_1256);
lean_ctor_set(x_1262, 1, x_1257);
lean_ctor_set(x_1262, 2, x_1258);
lean_ctor_set(x_1262, 3, x_1259);
lean_ctor_set_uint8(x_1262, sizeof(void*)*4, x_1261);
x_1263 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1263, 0, x_1255);
lean_ctor_set(x_1263, 1, x_2);
lean_ctor_set(x_1263, 2, x_3);
lean_ctor_set(x_1263, 3, x_4);
lean_ctor_set_uint8(x_1263, sizeof(void*)*4, x_1261);
x_1264 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1264, 0, x_1262);
lean_ctor_set(x_1264, 1, x_1253);
lean_ctor_set(x_1264, 2, x_1254);
lean_ctor_set(x_1264, 3, x_1263);
lean_ctor_set_uint8(x_1264, sizeof(void*)*4, x_1237);
return x_1264;
}
}
else
{
lean_object* x_1265; 
x_1265 = lean_ctor_get(x_1, 3);
lean_inc(x_1265);
if (lean_obj_tag(x_1265) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_1266; 
x_1266 = !lean_is_exclusive(x_1);
if (x_1266 == 0)
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
x_1267 = lean_ctor_get(x_1, 3);
lean_dec(x_1267);
x_1268 = lean_ctor_get(x_1, 0);
lean_dec(x_1268);
lean_ctor_set(x_1, 3, x_4);
x_1269 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1269, 0, x_1);
lean_ctor_set(x_1269, 1, x_2);
lean_ctor_set(x_1269, 2, x_3);
lean_ctor_set(x_1269, 3, x_4);
lean_ctor_set_uint8(x_1269, sizeof(void*)*4, x_1237);
return x_1269;
}
else
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; 
x_1270 = lean_ctor_get(x_1, 1);
x_1271 = lean_ctor_get(x_1, 2);
lean_inc(x_1271);
lean_inc(x_1270);
lean_dec(x_1);
x_1272 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1272, 0, x_234);
lean_ctor_set(x_1272, 1, x_1270);
lean_ctor_set(x_1272, 2, x_1271);
lean_ctor_set(x_1272, 3, x_4);
lean_ctor_set_uint8(x_1272, sizeof(void*)*4, x_233);
x_1273 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1273, 0, x_1272);
lean_ctor_set(x_1273, 1, x_2);
lean_ctor_set(x_1273, 2, x_3);
lean_ctor_set(x_1273, 3, x_4);
lean_ctor_set_uint8(x_1273, sizeof(void*)*4, x_1237);
return x_1273;
}
}
else
{
uint8_t x_1274; 
x_1274 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_1274 == 0)
{
lean_object* x_1275; 
x_1275 = lean_ctor_get(x_4, 0);
lean_inc(x_1275);
if (lean_obj_tag(x_1275) == 0)
{
lean_object* x_1276; 
x_1276 = lean_ctor_get(x_4, 3);
lean_inc(x_1276);
if (lean_obj_tag(x_1276) == 0)
{
uint8_t x_1277; 
x_1277 = !lean_is_exclusive(x_1);
if (x_1277 == 0)
{
lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; uint8_t x_1282; 
x_1278 = lean_ctor_get(x_1, 1);
x_1279 = lean_ctor_get(x_1, 2);
x_1280 = lean_ctor_get(x_1, 3);
lean_dec(x_1280);
x_1281 = lean_ctor_get(x_1, 0);
lean_dec(x_1281);
x_1282 = !lean_is_exclusive(x_4);
if (x_1282 == 0)
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; uint8_t x_1287; 
x_1283 = lean_ctor_get(x_4, 1);
x_1284 = lean_ctor_get(x_4, 2);
x_1285 = lean_ctor_get(x_4, 3);
lean_dec(x_1285);
x_1286 = lean_ctor_get(x_4, 0);
lean_dec(x_1286);
lean_inc(x_234);
lean_ctor_set(x_4, 2, x_1279);
lean_ctor_set(x_4, 1, x_1278);
lean_ctor_set(x_4, 0, x_234);
x_1287 = !lean_is_exclusive(x_234);
if (x_1287 == 0)
{
lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; 
x_1288 = lean_ctor_get(x_234, 3);
lean_dec(x_1288);
x_1289 = lean_ctor_get(x_234, 2);
lean_dec(x_1289);
x_1290 = lean_ctor_get(x_234, 1);
lean_dec(x_1290);
x_1291 = lean_ctor_get(x_234, 0);
lean_dec(x_1291);
lean_ctor_set(x_234, 3, x_1276);
lean_ctor_set(x_234, 2, x_1284);
lean_ctor_set(x_234, 1, x_1283);
lean_ctor_set(x_234, 0, x_1276);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1274);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1237);
return x_1;
}
else
{
lean_object* x_1292; 
lean_dec(x_234);
x_1292 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1292, 0, x_1276);
lean_ctor_set(x_1292, 1, x_1283);
lean_ctor_set(x_1292, 2, x_1284);
lean_ctor_set(x_1292, 3, x_1276);
lean_ctor_set_uint8(x_1292, sizeof(void*)*4, x_1274);
lean_ctor_set(x_1, 3, x_1292);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1237);
return x_1;
}
}
else
{
lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; 
x_1293 = lean_ctor_get(x_4, 1);
x_1294 = lean_ctor_get(x_4, 2);
lean_inc(x_1294);
lean_inc(x_1293);
lean_dec(x_4);
lean_inc(x_234);
x_1295 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1295, 0, x_234);
lean_ctor_set(x_1295, 1, x_1278);
lean_ctor_set(x_1295, 2, x_1279);
lean_ctor_set(x_1295, 3, x_1276);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1296 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1296 = lean_box(0);
}
lean_ctor_set_uint8(x_1295, sizeof(void*)*4, x_1274);
if (lean_is_scalar(x_1296)) {
 x_1297 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1297 = x_1296;
}
lean_ctor_set(x_1297, 0, x_1276);
lean_ctor_set(x_1297, 1, x_1293);
lean_ctor_set(x_1297, 2, x_1294);
lean_ctor_set(x_1297, 3, x_1276);
lean_ctor_set_uint8(x_1297, sizeof(void*)*4, x_1274);
lean_ctor_set(x_1, 3, x_1297);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_1295);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1237);
return x_1;
}
}
else
{
lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
x_1298 = lean_ctor_get(x_1, 1);
x_1299 = lean_ctor_get(x_1, 2);
lean_inc(x_1299);
lean_inc(x_1298);
lean_dec(x_1);
x_1300 = lean_ctor_get(x_4, 1);
lean_inc(x_1300);
x_1301 = lean_ctor_get(x_4, 2);
lean_inc(x_1301);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1302 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1302 = lean_box(0);
}
lean_inc(x_234);
if (lean_is_scalar(x_1302)) {
 x_1303 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1303 = x_1302;
}
lean_ctor_set(x_1303, 0, x_234);
lean_ctor_set(x_1303, 1, x_1298);
lean_ctor_set(x_1303, 2, x_1299);
lean_ctor_set(x_1303, 3, x_1276);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1304 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1304 = lean_box(0);
}
lean_ctor_set_uint8(x_1303, sizeof(void*)*4, x_1274);
if (lean_is_scalar(x_1304)) {
 x_1305 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1305 = x_1304;
}
lean_ctor_set(x_1305, 0, x_1276);
lean_ctor_set(x_1305, 1, x_1300);
lean_ctor_set(x_1305, 2, x_1301);
lean_ctor_set(x_1305, 3, x_1276);
lean_ctor_set_uint8(x_1305, sizeof(void*)*4, x_1274);
x_1306 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1306, 0, x_1303);
lean_ctor_set(x_1306, 1, x_2);
lean_ctor_set(x_1306, 2, x_3);
lean_ctor_set(x_1306, 3, x_1305);
lean_ctor_set_uint8(x_1306, sizeof(void*)*4, x_1237);
return x_1306;
}
}
else
{
uint8_t x_1307; 
x_1307 = lean_ctor_get_uint8(x_1276, sizeof(void*)*4);
if (x_1307 == 0)
{
uint8_t x_1308; 
x_1308 = !lean_is_exclusive(x_1);
if (x_1308 == 0)
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; uint8_t x_1313; 
x_1309 = lean_ctor_get(x_1, 1);
x_1310 = lean_ctor_get(x_1, 2);
x_1311 = lean_ctor_get(x_1, 3);
lean_dec(x_1311);
x_1312 = lean_ctor_get(x_1, 0);
lean_dec(x_1312);
x_1313 = !lean_is_exclusive(x_4);
if (x_1313 == 0)
{
lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; uint8_t x_1318; 
x_1314 = lean_ctor_get(x_4, 1);
x_1315 = lean_ctor_get(x_4, 2);
x_1316 = lean_ctor_get(x_4, 3);
lean_dec(x_1316);
x_1317 = lean_ctor_get(x_4, 0);
lean_dec(x_1317);
x_1318 = !lean_is_exclusive(x_1276);
if (x_1318 == 0)
{
lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; uint8_t x_1323; 
x_1319 = lean_ctor_get(x_1276, 0);
x_1320 = lean_ctor_get(x_1276, 1);
x_1321 = lean_ctor_get(x_1276, 2);
x_1322 = lean_ctor_get(x_1276, 3);
lean_inc(x_234);
lean_ctor_set(x_1276, 3, x_1275);
lean_ctor_set(x_1276, 2, x_1310);
lean_ctor_set(x_1276, 1, x_1309);
lean_ctor_set(x_1276, 0, x_234);
x_1323 = !lean_is_exclusive(x_234);
if (x_1323 == 0)
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; 
x_1324 = lean_ctor_get(x_234, 3);
lean_dec(x_1324);
x_1325 = lean_ctor_get(x_234, 2);
lean_dec(x_1325);
x_1326 = lean_ctor_get(x_234, 1);
lean_dec(x_1326);
x_1327 = lean_ctor_get(x_234, 0);
lean_dec(x_1327);
lean_ctor_set(x_4, 3, x_1275);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_1276);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1237);
lean_ctor_set(x_234, 3, x_1322);
lean_ctor_set(x_234, 2, x_1321);
lean_ctor_set(x_234, 1, x_1320);
lean_ctor_set(x_234, 0, x_1319);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_1315);
lean_ctor_set(x_1, 1, x_1314);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1307);
return x_1;
}
else
{
lean_object* x_1328; 
lean_dec(x_234);
lean_ctor_set(x_4, 3, x_1275);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_1276);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1237);
x_1328 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1328, 0, x_1319);
lean_ctor_set(x_1328, 1, x_1320);
lean_ctor_set(x_1328, 2, x_1321);
lean_ctor_set(x_1328, 3, x_1322);
lean_ctor_set_uint8(x_1328, sizeof(void*)*4, x_1237);
lean_ctor_set(x_1, 3, x_1328);
lean_ctor_set(x_1, 2, x_1315);
lean_ctor_set(x_1, 1, x_1314);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1307);
return x_1;
}
}
else
{
lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
x_1329 = lean_ctor_get(x_1276, 0);
x_1330 = lean_ctor_get(x_1276, 1);
x_1331 = lean_ctor_get(x_1276, 2);
x_1332 = lean_ctor_get(x_1276, 3);
lean_inc(x_1332);
lean_inc(x_1331);
lean_inc(x_1330);
lean_inc(x_1329);
lean_dec(x_1276);
lean_inc(x_234);
x_1333 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1333, 0, x_234);
lean_ctor_set(x_1333, 1, x_1309);
lean_ctor_set(x_1333, 2, x_1310);
lean_ctor_set(x_1333, 3, x_1275);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1334 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1334 = lean_box(0);
}
lean_ctor_set_uint8(x_1333, sizeof(void*)*4, x_1307);
lean_ctor_set(x_4, 3, x_1275);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_1333);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1237);
if (lean_is_scalar(x_1334)) {
 x_1335 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1335 = x_1334;
}
lean_ctor_set(x_1335, 0, x_1329);
lean_ctor_set(x_1335, 1, x_1330);
lean_ctor_set(x_1335, 2, x_1331);
lean_ctor_set(x_1335, 3, x_1332);
lean_ctor_set_uint8(x_1335, sizeof(void*)*4, x_1237);
lean_ctor_set(x_1, 3, x_1335);
lean_ctor_set(x_1, 2, x_1315);
lean_ctor_set(x_1, 1, x_1314);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1307);
return x_1;
}
}
else
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; 
x_1336 = lean_ctor_get(x_4, 1);
x_1337 = lean_ctor_get(x_4, 2);
lean_inc(x_1337);
lean_inc(x_1336);
lean_dec(x_4);
x_1338 = lean_ctor_get(x_1276, 0);
lean_inc(x_1338);
x_1339 = lean_ctor_get(x_1276, 1);
lean_inc(x_1339);
x_1340 = lean_ctor_get(x_1276, 2);
lean_inc(x_1340);
x_1341 = lean_ctor_get(x_1276, 3);
lean_inc(x_1341);
if (lean_is_exclusive(x_1276)) {
 lean_ctor_release(x_1276, 0);
 lean_ctor_release(x_1276, 1);
 lean_ctor_release(x_1276, 2);
 lean_ctor_release(x_1276, 3);
 x_1342 = x_1276;
} else {
 lean_dec_ref(x_1276);
 x_1342 = lean_box(0);
}
lean_inc(x_234);
if (lean_is_scalar(x_1342)) {
 x_1343 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1343 = x_1342;
}
lean_ctor_set(x_1343, 0, x_234);
lean_ctor_set(x_1343, 1, x_1309);
lean_ctor_set(x_1343, 2, x_1310);
lean_ctor_set(x_1343, 3, x_1275);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1344 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1344 = lean_box(0);
}
lean_ctor_set_uint8(x_1343, sizeof(void*)*4, x_1307);
x_1345 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1345, 0, x_1343);
lean_ctor_set(x_1345, 1, x_2);
lean_ctor_set(x_1345, 2, x_3);
lean_ctor_set(x_1345, 3, x_1275);
lean_ctor_set_uint8(x_1345, sizeof(void*)*4, x_1237);
if (lean_is_scalar(x_1344)) {
 x_1346 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1346 = x_1344;
}
lean_ctor_set(x_1346, 0, x_1338);
lean_ctor_set(x_1346, 1, x_1339);
lean_ctor_set(x_1346, 2, x_1340);
lean_ctor_set(x_1346, 3, x_1341);
lean_ctor_set_uint8(x_1346, sizeof(void*)*4, x_1237);
lean_ctor_set(x_1, 3, x_1346);
lean_ctor_set(x_1, 2, x_1337);
lean_ctor_set(x_1, 1, x_1336);
lean_ctor_set(x_1, 0, x_1345);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1307);
return x_1;
}
}
else
{
lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; 
x_1347 = lean_ctor_get(x_1, 1);
x_1348 = lean_ctor_get(x_1, 2);
lean_inc(x_1348);
lean_inc(x_1347);
lean_dec(x_1);
x_1349 = lean_ctor_get(x_4, 1);
lean_inc(x_1349);
x_1350 = lean_ctor_get(x_4, 2);
lean_inc(x_1350);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1351 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1351 = lean_box(0);
}
x_1352 = lean_ctor_get(x_1276, 0);
lean_inc(x_1352);
x_1353 = lean_ctor_get(x_1276, 1);
lean_inc(x_1353);
x_1354 = lean_ctor_get(x_1276, 2);
lean_inc(x_1354);
x_1355 = lean_ctor_get(x_1276, 3);
lean_inc(x_1355);
if (lean_is_exclusive(x_1276)) {
 lean_ctor_release(x_1276, 0);
 lean_ctor_release(x_1276, 1);
 lean_ctor_release(x_1276, 2);
 lean_ctor_release(x_1276, 3);
 x_1356 = x_1276;
} else {
 lean_dec_ref(x_1276);
 x_1356 = lean_box(0);
}
lean_inc(x_234);
if (lean_is_scalar(x_1356)) {
 x_1357 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1357 = x_1356;
}
lean_ctor_set(x_1357, 0, x_234);
lean_ctor_set(x_1357, 1, x_1347);
lean_ctor_set(x_1357, 2, x_1348);
lean_ctor_set(x_1357, 3, x_1275);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1358 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1358 = lean_box(0);
}
lean_ctor_set_uint8(x_1357, sizeof(void*)*4, x_1307);
if (lean_is_scalar(x_1351)) {
 x_1359 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1359 = x_1351;
}
lean_ctor_set(x_1359, 0, x_1357);
lean_ctor_set(x_1359, 1, x_2);
lean_ctor_set(x_1359, 2, x_3);
lean_ctor_set(x_1359, 3, x_1275);
lean_ctor_set_uint8(x_1359, sizeof(void*)*4, x_1237);
if (lean_is_scalar(x_1358)) {
 x_1360 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1360 = x_1358;
}
lean_ctor_set(x_1360, 0, x_1352);
lean_ctor_set(x_1360, 1, x_1353);
lean_ctor_set(x_1360, 2, x_1354);
lean_ctor_set(x_1360, 3, x_1355);
lean_ctor_set_uint8(x_1360, sizeof(void*)*4, x_1237);
x_1361 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1361, 0, x_1359);
lean_ctor_set(x_1361, 1, x_1349);
lean_ctor_set(x_1361, 2, x_1350);
lean_ctor_set(x_1361, 3, x_1360);
lean_ctor_set_uint8(x_1361, sizeof(void*)*4, x_1307);
return x_1361;
}
}
else
{
uint8_t x_1362; 
x_1362 = !lean_is_exclusive(x_1276);
if (x_1362 == 0)
{
lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; uint8_t x_1367; 
x_1363 = lean_ctor_get(x_1276, 3);
lean_dec(x_1363);
x_1364 = lean_ctor_get(x_1276, 2);
lean_dec(x_1364);
x_1365 = lean_ctor_get(x_1276, 1);
lean_dec(x_1365);
x_1366 = lean_ctor_get(x_1276, 0);
lean_dec(x_1366);
x_1367 = !lean_is_exclusive(x_1);
if (x_1367 == 0)
{
lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; uint8_t x_1372; 
x_1368 = lean_ctor_get(x_1, 1);
x_1369 = lean_ctor_get(x_1, 2);
x_1370 = lean_ctor_get(x_1, 3);
lean_dec(x_1370);
x_1371 = lean_ctor_get(x_1, 0);
lean_dec(x_1371);
x_1372 = !lean_is_exclusive(x_234);
if (x_1372 == 0)
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; 
x_1373 = lean_ctor_get(x_234, 0);
x_1374 = lean_ctor_get(x_234, 1);
x_1375 = lean_ctor_get(x_234, 2);
x_1376 = lean_ctor_get(x_234, 3);
lean_ctor_set(x_1276, 3, x_1376);
lean_ctor_set(x_1276, 2, x_1375);
lean_ctor_set(x_1276, 1, x_1374);
lean_ctor_set(x_1276, 0, x_1373);
lean_ctor_set(x_234, 3, x_1275);
lean_ctor_set(x_234, 2, x_1369);
lean_ctor_set(x_234, 1, x_1368);
lean_ctor_set(x_234, 0, x_1276);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1274);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1307);
return x_1;
}
else
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
x_1377 = lean_ctor_get(x_234, 0);
x_1378 = lean_ctor_get(x_234, 1);
x_1379 = lean_ctor_get(x_234, 2);
x_1380 = lean_ctor_get(x_234, 3);
lean_inc(x_1380);
lean_inc(x_1379);
lean_inc(x_1378);
lean_inc(x_1377);
lean_dec(x_234);
lean_ctor_set(x_1276, 3, x_1380);
lean_ctor_set(x_1276, 2, x_1379);
lean_ctor_set(x_1276, 1, x_1378);
lean_ctor_set(x_1276, 0, x_1377);
x_1381 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1381, 0, x_1276);
lean_ctor_set(x_1381, 1, x_1368);
lean_ctor_set(x_1381, 2, x_1369);
lean_ctor_set(x_1381, 3, x_1275);
lean_ctor_set_uint8(x_1381, sizeof(void*)*4, x_1274);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_1381);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1307);
return x_1;
}
}
else
{
lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; 
x_1382 = lean_ctor_get(x_1, 1);
x_1383 = lean_ctor_get(x_1, 2);
lean_inc(x_1383);
lean_inc(x_1382);
lean_dec(x_1);
x_1384 = lean_ctor_get(x_234, 0);
lean_inc(x_1384);
x_1385 = lean_ctor_get(x_234, 1);
lean_inc(x_1385);
x_1386 = lean_ctor_get(x_234, 2);
lean_inc(x_1386);
x_1387 = lean_ctor_get(x_234, 3);
lean_inc(x_1387);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1388 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1388 = lean_box(0);
}
lean_ctor_set(x_1276, 3, x_1387);
lean_ctor_set(x_1276, 2, x_1386);
lean_ctor_set(x_1276, 1, x_1385);
lean_ctor_set(x_1276, 0, x_1384);
if (lean_is_scalar(x_1388)) {
 x_1389 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1389 = x_1388;
}
lean_ctor_set(x_1389, 0, x_1276);
lean_ctor_set(x_1389, 1, x_1382);
lean_ctor_set(x_1389, 2, x_1383);
lean_ctor_set(x_1389, 3, x_1275);
lean_ctor_set_uint8(x_1389, sizeof(void*)*4, x_1274);
x_1390 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1390, 0, x_1389);
lean_ctor_set(x_1390, 1, x_2);
lean_ctor_set(x_1390, 2, x_3);
lean_ctor_set(x_1390, 3, x_4);
lean_ctor_set_uint8(x_1390, sizeof(void*)*4, x_1307);
return x_1390;
}
}
else
{
lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; 
lean_dec(x_1276);
x_1391 = lean_ctor_get(x_1, 1);
lean_inc(x_1391);
x_1392 = lean_ctor_get(x_1, 2);
lean_inc(x_1392);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_1393 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1393 = lean_box(0);
}
x_1394 = lean_ctor_get(x_234, 0);
lean_inc(x_1394);
x_1395 = lean_ctor_get(x_234, 1);
lean_inc(x_1395);
x_1396 = lean_ctor_get(x_234, 2);
lean_inc(x_1396);
x_1397 = lean_ctor_get(x_234, 3);
lean_inc(x_1397);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1398 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1398 = lean_box(0);
}
x_1399 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1399, 0, x_1394);
lean_ctor_set(x_1399, 1, x_1395);
lean_ctor_set(x_1399, 2, x_1396);
lean_ctor_set(x_1399, 3, x_1397);
lean_ctor_set_uint8(x_1399, sizeof(void*)*4, x_1307);
if (lean_is_scalar(x_1398)) {
 x_1400 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1400 = x_1398;
}
lean_ctor_set(x_1400, 0, x_1399);
lean_ctor_set(x_1400, 1, x_1391);
lean_ctor_set(x_1400, 2, x_1392);
lean_ctor_set(x_1400, 3, x_1275);
lean_ctor_set_uint8(x_1400, sizeof(void*)*4, x_1274);
if (lean_is_scalar(x_1393)) {
 x_1401 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1401 = x_1393;
}
lean_ctor_set(x_1401, 0, x_1400);
lean_ctor_set(x_1401, 1, x_2);
lean_ctor_set(x_1401, 2, x_3);
lean_ctor_set(x_1401, 3, x_4);
lean_ctor_set_uint8(x_1401, sizeof(void*)*4, x_1307);
return x_1401;
}
}
}
}
else
{
uint8_t x_1402; 
x_1402 = lean_ctor_get_uint8(x_1275, sizeof(void*)*4);
if (x_1402 == 0)
{
lean_object* x_1403; 
x_1403 = lean_ctor_get(x_4, 3);
lean_inc(x_1403);
if (lean_obj_tag(x_1403) == 0)
{
uint8_t x_1404; 
x_1404 = !lean_is_exclusive(x_1);
if (x_1404 == 0)
{
lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; uint8_t x_1409; 
x_1405 = lean_ctor_get(x_1, 1);
x_1406 = lean_ctor_get(x_1, 2);
x_1407 = lean_ctor_get(x_1, 3);
lean_dec(x_1407);
x_1408 = lean_ctor_get(x_1, 0);
lean_dec(x_1408);
x_1409 = !lean_is_exclusive(x_4);
if (x_1409 == 0)
{
lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; uint8_t x_1414; 
x_1410 = lean_ctor_get(x_4, 1);
x_1411 = lean_ctor_get(x_4, 2);
x_1412 = lean_ctor_get(x_4, 3);
lean_dec(x_1412);
x_1413 = lean_ctor_get(x_4, 0);
lean_dec(x_1413);
x_1414 = !lean_is_exclusive(x_1275);
if (x_1414 == 0)
{
lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; uint8_t x_1419; 
x_1415 = lean_ctor_get(x_1275, 0);
x_1416 = lean_ctor_get(x_1275, 1);
x_1417 = lean_ctor_get(x_1275, 2);
x_1418 = lean_ctor_get(x_1275, 3);
lean_inc(x_234);
lean_ctor_set(x_1275, 3, x_1403);
lean_ctor_set(x_1275, 2, x_1406);
lean_ctor_set(x_1275, 1, x_1405);
lean_ctor_set(x_1275, 0, x_234);
x_1419 = !lean_is_exclusive(x_234);
if (x_1419 == 0)
{
lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; 
x_1420 = lean_ctor_get(x_234, 3);
lean_dec(x_1420);
x_1421 = lean_ctor_get(x_234, 2);
lean_dec(x_1421);
x_1422 = lean_ctor_get(x_234, 1);
lean_dec(x_1422);
x_1423 = lean_ctor_get(x_234, 0);
lean_dec(x_1423);
lean_ctor_set(x_4, 3, x_1415);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1237);
lean_ctor_set(x_234, 3, x_1403);
lean_ctor_set(x_234, 2, x_1411);
lean_ctor_set(x_234, 1, x_1410);
lean_ctor_set(x_234, 0, x_1418);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_1417);
lean_ctor_set(x_1, 1, x_1416);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1402);
return x_1;
}
else
{
lean_object* x_1424; 
lean_dec(x_234);
lean_ctor_set(x_4, 3, x_1415);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1237);
x_1424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1424, 0, x_1418);
lean_ctor_set(x_1424, 1, x_1410);
lean_ctor_set(x_1424, 2, x_1411);
lean_ctor_set(x_1424, 3, x_1403);
lean_ctor_set_uint8(x_1424, sizeof(void*)*4, x_1237);
lean_ctor_set(x_1, 3, x_1424);
lean_ctor_set(x_1, 2, x_1417);
lean_ctor_set(x_1, 1, x_1416);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1402);
return x_1;
}
}
else
{
lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; 
x_1425 = lean_ctor_get(x_1275, 0);
x_1426 = lean_ctor_get(x_1275, 1);
x_1427 = lean_ctor_get(x_1275, 2);
x_1428 = lean_ctor_get(x_1275, 3);
lean_inc(x_1428);
lean_inc(x_1427);
lean_inc(x_1426);
lean_inc(x_1425);
lean_dec(x_1275);
lean_inc(x_234);
x_1429 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1429, 0, x_234);
lean_ctor_set(x_1429, 1, x_1405);
lean_ctor_set(x_1429, 2, x_1406);
lean_ctor_set(x_1429, 3, x_1403);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1430 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1430 = lean_box(0);
}
lean_ctor_set_uint8(x_1429, sizeof(void*)*4, x_1402);
lean_ctor_set(x_4, 3, x_1425);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_1429);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1237);
if (lean_is_scalar(x_1430)) {
 x_1431 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1431 = x_1430;
}
lean_ctor_set(x_1431, 0, x_1428);
lean_ctor_set(x_1431, 1, x_1410);
lean_ctor_set(x_1431, 2, x_1411);
lean_ctor_set(x_1431, 3, x_1403);
lean_ctor_set_uint8(x_1431, sizeof(void*)*4, x_1237);
lean_ctor_set(x_1, 3, x_1431);
lean_ctor_set(x_1, 2, x_1427);
lean_ctor_set(x_1, 1, x_1426);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1402);
return x_1;
}
}
else
{
lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; 
x_1432 = lean_ctor_get(x_4, 1);
x_1433 = lean_ctor_get(x_4, 2);
lean_inc(x_1433);
lean_inc(x_1432);
lean_dec(x_4);
x_1434 = lean_ctor_get(x_1275, 0);
lean_inc(x_1434);
x_1435 = lean_ctor_get(x_1275, 1);
lean_inc(x_1435);
x_1436 = lean_ctor_get(x_1275, 2);
lean_inc(x_1436);
x_1437 = lean_ctor_get(x_1275, 3);
lean_inc(x_1437);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 lean_ctor_release(x_1275, 1);
 lean_ctor_release(x_1275, 2);
 lean_ctor_release(x_1275, 3);
 x_1438 = x_1275;
} else {
 lean_dec_ref(x_1275);
 x_1438 = lean_box(0);
}
lean_inc(x_234);
if (lean_is_scalar(x_1438)) {
 x_1439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1439 = x_1438;
}
lean_ctor_set(x_1439, 0, x_234);
lean_ctor_set(x_1439, 1, x_1405);
lean_ctor_set(x_1439, 2, x_1406);
lean_ctor_set(x_1439, 3, x_1403);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1440 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1440 = lean_box(0);
}
lean_ctor_set_uint8(x_1439, sizeof(void*)*4, x_1402);
x_1441 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1441, 0, x_1439);
lean_ctor_set(x_1441, 1, x_2);
lean_ctor_set(x_1441, 2, x_3);
lean_ctor_set(x_1441, 3, x_1434);
lean_ctor_set_uint8(x_1441, sizeof(void*)*4, x_1237);
if (lean_is_scalar(x_1440)) {
 x_1442 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1442 = x_1440;
}
lean_ctor_set(x_1442, 0, x_1437);
lean_ctor_set(x_1442, 1, x_1432);
lean_ctor_set(x_1442, 2, x_1433);
lean_ctor_set(x_1442, 3, x_1403);
lean_ctor_set_uint8(x_1442, sizeof(void*)*4, x_1237);
lean_ctor_set(x_1, 3, x_1442);
lean_ctor_set(x_1, 2, x_1436);
lean_ctor_set(x_1, 1, x_1435);
lean_ctor_set(x_1, 0, x_1441);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1402);
return x_1;
}
}
else
{
lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; 
x_1443 = lean_ctor_get(x_1, 1);
x_1444 = lean_ctor_get(x_1, 2);
lean_inc(x_1444);
lean_inc(x_1443);
lean_dec(x_1);
x_1445 = lean_ctor_get(x_4, 1);
lean_inc(x_1445);
x_1446 = lean_ctor_get(x_4, 2);
lean_inc(x_1446);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1447 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1447 = lean_box(0);
}
x_1448 = lean_ctor_get(x_1275, 0);
lean_inc(x_1448);
x_1449 = lean_ctor_get(x_1275, 1);
lean_inc(x_1449);
x_1450 = lean_ctor_get(x_1275, 2);
lean_inc(x_1450);
x_1451 = lean_ctor_get(x_1275, 3);
lean_inc(x_1451);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 lean_ctor_release(x_1275, 1);
 lean_ctor_release(x_1275, 2);
 lean_ctor_release(x_1275, 3);
 x_1452 = x_1275;
} else {
 lean_dec_ref(x_1275);
 x_1452 = lean_box(0);
}
lean_inc(x_234);
if (lean_is_scalar(x_1452)) {
 x_1453 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1453 = x_1452;
}
lean_ctor_set(x_1453, 0, x_234);
lean_ctor_set(x_1453, 1, x_1443);
lean_ctor_set(x_1453, 2, x_1444);
lean_ctor_set(x_1453, 3, x_1403);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1454 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1454 = lean_box(0);
}
lean_ctor_set_uint8(x_1453, sizeof(void*)*4, x_1402);
if (lean_is_scalar(x_1447)) {
 x_1455 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1455 = x_1447;
}
lean_ctor_set(x_1455, 0, x_1453);
lean_ctor_set(x_1455, 1, x_2);
lean_ctor_set(x_1455, 2, x_3);
lean_ctor_set(x_1455, 3, x_1448);
lean_ctor_set_uint8(x_1455, sizeof(void*)*4, x_1237);
if (lean_is_scalar(x_1454)) {
 x_1456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1456 = x_1454;
}
lean_ctor_set(x_1456, 0, x_1451);
lean_ctor_set(x_1456, 1, x_1445);
lean_ctor_set(x_1456, 2, x_1446);
lean_ctor_set(x_1456, 3, x_1403);
lean_ctor_set_uint8(x_1456, sizeof(void*)*4, x_1237);
x_1457 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1457, 0, x_1455);
lean_ctor_set(x_1457, 1, x_1449);
lean_ctor_set(x_1457, 2, x_1450);
lean_ctor_set(x_1457, 3, x_1456);
lean_ctor_set_uint8(x_1457, sizeof(void*)*4, x_1402);
return x_1457;
}
}
else
{
uint8_t x_1458; 
x_1458 = lean_ctor_get_uint8(x_1403, sizeof(void*)*4);
if (x_1458 == 0)
{
uint8_t x_1459; 
x_1459 = !lean_is_exclusive(x_1);
if (x_1459 == 0)
{
lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; uint8_t x_1464; 
x_1460 = lean_ctor_get(x_1, 1);
x_1461 = lean_ctor_get(x_1, 2);
x_1462 = lean_ctor_get(x_1, 3);
lean_dec(x_1462);
x_1463 = lean_ctor_get(x_1, 0);
lean_dec(x_1463);
x_1464 = !lean_is_exclusive(x_4);
if (x_1464 == 0)
{
lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; uint8_t x_1469; 
x_1465 = lean_ctor_get(x_4, 1);
x_1466 = lean_ctor_get(x_4, 2);
x_1467 = lean_ctor_get(x_4, 3);
lean_dec(x_1467);
x_1468 = lean_ctor_get(x_4, 0);
lean_dec(x_1468);
x_1469 = !lean_is_exclusive(x_1275);
if (x_1469 == 0)
{
uint8_t x_1470; 
x_1470 = !lean_is_exclusive(x_1403);
if (x_1470 == 0)
{
lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; uint8_t x_1475; 
x_1471 = lean_ctor_get(x_1403, 0);
x_1472 = lean_ctor_get(x_1403, 1);
x_1473 = lean_ctor_get(x_1403, 2);
x_1474 = lean_ctor_get(x_1403, 3);
lean_inc(x_234);
lean_ctor_set(x_1403, 3, x_1265);
lean_ctor_set(x_1403, 2, x_1461);
lean_ctor_set(x_1403, 1, x_1460);
lean_ctor_set(x_1403, 0, x_234);
x_1475 = !lean_is_exclusive(x_234);
if (x_1475 == 0)
{
lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; 
x_1476 = lean_ctor_get(x_234, 3);
lean_dec(x_1476);
x_1477 = lean_ctor_get(x_234, 2);
lean_dec(x_1477);
x_1478 = lean_ctor_get(x_234, 1);
lean_dec(x_1478);
x_1479 = lean_ctor_get(x_234, 0);
lean_dec(x_1479);
lean_ctor_set_uint8(x_1275, sizeof(void*)*4, x_1458);
lean_ctor_set(x_4, 3, x_1275);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_1403);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1237);
lean_ctor_set(x_234, 3, x_1474);
lean_ctor_set(x_234, 2, x_1473);
lean_ctor_set(x_234, 1, x_1472);
lean_ctor_set(x_234, 0, x_1471);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_1466);
lean_ctor_set(x_1, 1, x_1465);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1458);
return x_1;
}
else
{
lean_object* x_1480; 
lean_dec(x_234);
lean_ctor_set_uint8(x_1275, sizeof(void*)*4, x_1458);
lean_ctor_set(x_4, 3, x_1275);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_1403);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1237);
x_1480 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1480, 0, x_1471);
lean_ctor_set(x_1480, 1, x_1472);
lean_ctor_set(x_1480, 2, x_1473);
lean_ctor_set(x_1480, 3, x_1474);
lean_ctor_set_uint8(x_1480, sizeof(void*)*4, x_1237);
lean_ctor_set(x_1, 3, x_1480);
lean_ctor_set(x_1, 2, x_1466);
lean_ctor_set(x_1, 1, x_1465);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1458);
return x_1;
}
}
else
{
lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; 
x_1481 = lean_ctor_get(x_1403, 0);
x_1482 = lean_ctor_get(x_1403, 1);
x_1483 = lean_ctor_get(x_1403, 2);
x_1484 = lean_ctor_get(x_1403, 3);
lean_inc(x_1484);
lean_inc(x_1483);
lean_inc(x_1482);
lean_inc(x_1481);
lean_dec(x_1403);
lean_inc(x_234);
x_1485 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1485, 0, x_234);
lean_ctor_set(x_1485, 1, x_1460);
lean_ctor_set(x_1485, 2, x_1461);
lean_ctor_set(x_1485, 3, x_1265);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1486 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1486 = lean_box(0);
}
lean_ctor_set_uint8(x_1485, sizeof(void*)*4, x_1458);
lean_ctor_set_uint8(x_1275, sizeof(void*)*4, x_1458);
lean_ctor_set(x_4, 3, x_1275);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_1485);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1237);
if (lean_is_scalar(x_1486)) {
 x_1487 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1487 = x_1486;
}
lean_ctor_set(x_1487, 0, x_1481);
lean_ctor_set(x_1487, 1, x_1482);
lean_ctor_set(x_1487, 2, x_1483);
lean_ctor_set(x_1487, 3, x_1484);
lean_ctor_set_uint8(x_1487, sizeof(void*)*4, x_1237);
lean_ctor_set(x_1, 3, x_1487);
lean_ctor_set(x_1, 2, x_1466);
lean_ctor_set(x_1, 1, x_1465);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1458);
return x_1;
}
}
else
{
lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; 
x_1488 = lean_ctor_get(x_1275, 0);
x_1489 = lean_ctor_get(x_1275, 1);
x_1490 = lean_ctor_get(x_1275, 2);
x_1491 = lean_ctor_get(x_1275, 3);
lean_inc(x_1491);
lean_inc(x_1490);
lean_inc(x_1489);
lean_inc(x_1488);
lean_dec(x_1275);
x_1492 = lean_ctor_get(x_1403, 0);
lean_inc(x_1492);
x_1493 = lean_ctor_get(x_1403, 1);
lean_inc(x_1493);
x_1494 = lean_ctor_get(x_1403, 2);
lean_inc(x_1494);
x_1495 = lean_ctor_get(x_1403, 3);
lean_inc(x_1495);
if (lean_is_exclusive(x_1403)) {
 lean_ctor_release(x_1403, 0);
 lean_ctor_release(x_1403, 1);
 lean_ctor_release(x_1403, 2);
 lean_ctor_release(x_1403, 3);
 x_1496 = x_1403;
} else {
 lean_dec_ref(x_1403);
 x_1496 = lean_box(0);
}
lean_inc(x_234);
if (lean_is_scalar(x_1496)) {
 x_1497 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1497 = x_1496;
}
lean_ctor_set(x_1497, 0, x_234);
lean_ctor_set(x_1497, 1, x_1460);
lean_ctor_set(x_1497, 2, x_1461);
lean_ctor_set(x_1497, 3, x_1265);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1498 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1498 = lean_box(0);
}
lean_ctor_set_uint8(x_1497, sizeof(void*)*4, x_1458);
x_1499 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1499, 0, x_1488);
lean_ctor_set(x_1499, 1, x_1489);
lean_ctor_set(x_1499, 2, x_1490);
lean_ctor_set(x_1499, 3, x_1491);
lean_ctor_set_uint8(x_1499, sizeof(void*)*4, x_1458);
lean_ctor_set(x_4, 3, x_1499);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_1497);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1237);
if (lean_is_scalar(x_1498)) {
 x_1500 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1500 = x_1498;
}
lean_ctor_set(x_1500, 0, x_1492);
lean_ctor_set(x_1500, 1, x_1493);
lean_ctor_set(x_1500, 2, x_1494);
lean_ctor_set(x_1500, 3, x_1495);
lean_ctor_set_uint8(x_1500, sizeof(void*)*4, x_1237);
lean_ctor_set(x_1, 3, x_1500);
lean_ctor_set(x_1, 2, x_1466);
lean_ctor_set(x_1, 1, x_1465);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1458);
return x_1;
}
}
else
{
lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; 
x_1501 = lean_ctor_get(x_4, 1);
x_1502 = lean_ctor_get(x_4, 2);
lean_inc(x_1502);
lean_inc(x_1501);
lean_dec(x_4);
x_1503 = lean_ctor_get(x_1275, 0);
lean_inc(x_1503);
x_1504 = lean_ctor_get(x_1275, 1);
lean_inc(x_1504);
x_1505 = lean_ctor_get(x_1275, 2);
lean_inc(x_1505);
x_1506 = lean_ctor_get(x_1275, 3);
lean_inc(x_1506);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 lean_ctor_release(x_1275, 1);
 lean_ctor_release(x_1275, 2);
 lean_ctor_release(x_1275, 3);
 x_1507 = x_1275;
} else {
 lean_dec_ref(x_1275);
 x_1507 = lean_box(0);
}
x_1508 = lean_ctor_get(x_1403, 0);
lean_inc(x_1508);
x_1509 = lean_ctor_get(x_1403, 1);
lean_inc(x_1509);
x_1510 = lean_ctor_get(x_1403, 2);
lean_inc(x_1510);
x_1511 = lean_ctor_get(x_1403, 3);
lean_inc(x_1511);
if (lean_is_exclusive(x_1403)) {
 lean_ctor_release(x_1403, 0);
 lean_ctor_release(x_1403, 1);
 lean_ctor_release(x_1403, 2);
 lean_ctor_release(x_1403, 3);
 x_1512 = x_1403;
} else {
 lean_dec_ref(x_1403);
 x_1512 = lean_box(0);
}
lean_inc(x_234);
if (lean_is_scalar(x_1512)) {
 x_1513 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1513 = x_1512;
}
lean_ctor_set(x_1513, 0, x_234);
lean_ctor_set(x_1513, 1, x_1460);
lean_ctor_set(x_1513, 2, x_1461);
lean_ctor_set(x_1513, 3, x_1265);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1514 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1514 = lean_box(0);
}
lean_ctor_set_uint8(x_1513, sizeof(void*)*4, x_1458);
if (lean_is_scalar(x_1507)) {
 x_1515 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1515 = x_1507;
}
lean_ctor_set(x_1515, 0, x_1503);
lean_ctor_set(x_1515, 1, x_1504);
lean_ctor_set(x_1515, 2, x_1505);
lean_ctor_set(x_1515, 3, x_1506);
lean_ctor_set_uint8(x_1515, sizeof(void*)*4, x_1458);
x_1516 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1516, 0, x_1513);
lean_ctor_set(x_1516, 1, x_2);
lean_ctor_set(x_1516, 2, x_3);
lean_ctor_set(x_1516, 3, x_1515);
lean_ctor_set_uint8(x_1516, sizeof(void*)*4, x_1237);
if (lean_is_scalar(x_1514)) {
 x_1517 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1517 = x_1514;
}
lean_ctor_set(x_1517, 0, x_1508);
lean_ctor_set(x_1517, 1, x_1509);
lean_ctor_set(x_1517, 2, x_1510);
lean_ctor_set(x_1517, 3, x_1511);
lean_ctor_set_uint8(x_1517, sizeof(void*)*4, x_1237);
lean_ctor_set(x_1, 3, x_1517);
lean_ctor_set(x_1, 2, x_1502);
lean_ctor_set(x_1, 1, x_1501);
lean_ctor_set(x_1, 0, x_1516);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1458);
return x_1;
}
}
else
{
lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; 
x_1518 = lean_ctor_get(x_1, 1);
x_1519 = lean_ctor_get(x_1, 2);
lean_inc(x_1519);
lean_inc(x_1518);
lean_dec(x_1);
x_1520 = lean_ctor_get(x_4, 1);
lean_inc(x_1520);
x_1521 = lean_ctor_get(x_4, 2);
lean_inc(x_1521);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1522 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1522 = lean_box(0);
}
x_1523 = lean_ctor_get(x_1275, 0);
lean_inc(x_1523);
x_1524 = lean_ctor_get(x_1275, 1);
lean_inc(x_1524);
x_1525 = lean_ctor_get(x_1275, 2);
lean_inc(x_1525);
x_1526 = lean_ctor_get(x_1275, 3);
lean_inc(x_1526);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 lean_ctor_release(x_1275, 1);
 lean_ctor_release(x_1275, 2);
 lean_ctor_release(x_1275, 3);
 x_1527 = x_1275;
} else {
 lean_dec_ref(x_1275);
 x_1527 = lean_box(0);
}
x_1528 = lean_ctor_get(x_1403, 0);
lean_inc(x_1528);
x_1529 = lean_ctor_get(x_1403, 1);
lean_inc(x_1529);
x_1530 = lean_ctor_get(x_1403, 2);
lean_inc(x_1530);
x_1531 = lean_ctor_get(x_1403, 3);
lean_inc(x_1531);
if (lean_is_exclusive(x_1403)) {
 lean_ctor_release(x_1403, 0);
 lean_ctor_release(x_1403, 1);
 lean_ctor_release(x_1403, 2);
 lean_ctor_release(x_1403, 3);
 x_1532 = x_1403;
} else {
 lean_dec_ref(x_1403);
 x_1532 = lean_box(0);
}
lean_inc(x_234);
if (lean_is_scalar(x_1532)) {
 x_1533 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1533 = x_1532;
}
lean_ctor_set(x_1533, 0, x_234);
lean_ctor_set(x_1533, 1, x_1518);
lean_ctor_set(x_1533, 2, x_1519);
lean_ctor_set(x_1533, 3, x_1265);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1534 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1534 = lean_box(0);
}
lean_ctor_set_uint8(x_1533, sizeof(void*)*4, x_1458);
if (lean_is_scalar(x_1527)) {
 x_1535 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1535 = x_1527;
}
lean_ctor_set(x_1535, 0, x_1523);
lean_ctor_set(x_1535, 1, x_1524);
lean_ctor_set(x_1535, 2, x_1525);
lean_ctor_set(x_1535, 3, x_1526);
lean_ctor_set_uint8(x_1535, sizeof(void*)*4, x_1458);
if (lean_is_scalar(x_1522)) {
 x_1536 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1536 = x_1522;
}
lean_ctor_set(x_1536, 0, x_1533);
lean_ctor_set(x_1536, 1, x_2);
lean_ctor_set(x_1536, 2, x_3);
lean_ctor_set(x_1536, 3, x_1535);
lean_ctor_set_uint8(x_1536, sizeof(void*)*4, x_1237);
if (lean_is_scalar(x_1534)) {
 x_1537 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1537 = x_1534;
}
lean_ctor_set(x_1537, 0, x_1528);
lean_ctor_set(x_1537, 1, x_1529);
lean_ctor_set(x_1537, 2, x_1530);
lean_ctor_set(x_1537, 3, x_1531);
lean_ctor_set_uint8(x_1537, sizeof(void*)*4, x_1237);
x_1538 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1538, 0, x_1536);
lean_ctor_set(x_1538, 1, x_1520);
lean_ctor_set(x_1538, 2, x_1521);
lean_ctor_set(x_1538, 3, x_1537);
lean_ctor_set_uint8(x_1538, sizeof(void*)*4, x_1458);
return x_1538;
}
}
else
{
uint8_t x_1539; 
x_1539 = !lean_is_exclusive(x_1);
if (x_1539 == 0)
{
lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; uint8_t x_1544; 
x_1540 = lean_ctor_get(x_1, 1);
x_1541 = lean_ctor_get(x_1, 2);
x_1542 = lean_ctor_get(x_1, 3);
lean_dec(x_1542);
x_1543 = lean_ctor_get(x_1, 0);
lean_dec(x_1543);
x_1544 = !lean_is_exclusive(x_234);
if (x_1544 == 0)
{
uint8_t x_1545; 
x_1545 = !lean_is_exclusive(x_4);
if (x_1545 == 0)
{
lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; uint8_t x_1554; 
x_1546 = lean_ctor_get(x_234, 0);
x_1547 = lean_ctor_get(x_234, 1);
x_1548 = lean_ctor_get(x_234, 2);
x_1549 = lean_ctor_get(x_234, 3);
x_1550 = lean_ctor_get(x_4, 1);
x_1551 = lean_ctor_get(x_4, 2);
x_1552 = lean_ctor_get(x_4, 3);
lean_dec(x_1552);
x_1553 = lean_ctor_get(x_4, 0);
lean_dec(x_1553);
x_1554 = !lean_is_exclusive(x_1275);
if (x_1554 == 0)
{
lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; 
x_1555 = lean_ctor_get(x_1275, 0);
x_1556 = lean_ctor_get(x_1275, 1);
x_1557 = lean_ctor_get(x_1275, 2);
x_1558 = lean_ctor_get(x_1275, 3);
lean_ctor_set(x_1275, 3, x_1549);
lean_ctor_set(x_1275, 2, x_1548);
lean_ctor_set(x_1275, 1, x_1547);
lean_ctor_set(x_1275, 0, x_1546);
lean_ctor_set_uint8(x_1275, sizeof(void*)*4, x_1458);
lean_ctor_set(x_4, 3, x_1265);
lean_ctor_set(x_4, 2, x_1541);
lean_ctor_set(x_4, 1, x_1540);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1402);
lean_ctor_set(x_234, 3, x_1555);
lean_ctor_set(x_234, 2, x_3);
lean_ctor_set(x_234, 1, x_2);
lean_ctor_set(x_234, 0, x_4);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1458);
lean_ctor_set(x_1, 3, x_1403);
lean_ctor_set(x_1, 2, x_1551);
lean_ctor_set(x_1, 1, x_1550);
lean_ctor_set(x_1, 0, x_1558);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1458);
x_1559 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1559, 0, x_234);
lean_ctor_set(x_1559, 1, x_1556);
lean_ctor_set(x_1559, 2, x_1557);
lean_ctor_set(x_1559, 3, x_1);
lean_ctor_set_uint8(x_1559, sizeof(void*)*4, x_1402);
return x_1559;
}
else
{
lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; 
x_1560 = lean_ctor_get(x_1275, 0);
x_1561 = lean_ctor_get(x_1275, 1);
x_1562 = lean_ctor_get(x_1275, 2);
x_1563 = lean_ctor_get(x_1275, 3);
lean_inc(x_1563);
lean_inc(x_1562);
lean_inc(x_1561);
lean_inc(x_1560);
lean_dec(x_1275);
x_1564 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1564, 0, x_1546);
lean_ctor_set(x_1564, 1, x_1547);
lean_ctor_set(x_1564, 2, x_1548);
lean_ctor_set(x_1564, 3, x_1549);
lean_ctor_set_uint8(x_1564, sizeof(void*)*4, x_1458);
lean_ctor_set(x_4, 3, x_1265);
lean_ctor_set(x_4, 2, x_1541);
lean_ctor_set(x_4, 1, x_1540);
lean_ctor_set(x_4, 0, x_1564);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1402);
lean_ctor_set(x_234, 3, x_1560);
lean_ctor_set(x_234, 2, x_3);
lean_ctor_set(x_234, 1, x_2);
lean_ctor_set(x_234, 0, x_4);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1458);
lean_ctor_set(x_1, 3, x_1403);
lean_ctor_set(x_1, 2, x_1551);
lean_ctor_set(x_1, 1, x_1550);
lean_ctor_set(x_1, 0, x_1563);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1458);
x_1565 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1565, 0, x_234);
lean_ctor_set(x_1565, 1, x_1561);
lean_ctor_set(x_1565, 2, x_1562);
lean_ctor_set(x_1565, 3, x_1);
lean_ctor_set_uint8(x_1565, sizeof(void*)*4, x_1402);
return x_1565;
}
}
else
{
lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; 
x_1566 = lean_ctor_get(x_234, 0);
x_1567 = lean_ctor_get(x_234, 1);
x_1568 = lean_ctor_get(x_234, 2);
x_1569 = lean_ctor_get(x_234, 3);
x_1570 = lean_ctor_get(x_4, 1);
x_1571 = lean_ctor_get(x_4, 2);
lean_inc(x_1571);
lean_inc(x_1570);
lean_dec(x_4);
x_1572 = lean_ctor_get(x_1275, 0);
lean_inc(x_1572);
x_1573 = lean_ctor_get(x_1275, 1);
lean_inc(x_1573);
x_1574 = lean_ctor_get(x_1275, 2);
lean_inc(x_1574);
x_1575 = lean_ctor_get(x_1275, 3);
lean_inc(x_1575);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 lean_ctor_release(x_1275, 1);
 lean_ctor_release(x_1275, 2);
 lean_ctor_release(x_1275, 3);
 x_1576 = x_1275;
} else {
 lean_dec_ref(x_1275);
 x_1576 = lean_box(0);
}
if (lean_is_scalar(x_1576)) {
 x_1577 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1577 = x_1576;
}
lean_ctor_set(x_1577, 0, x_1566);
lean_ctor_set(x_1577, 1, x_1567);
lean_ctor_set(x_1577, 2, x_1568);
lean_ctor_set(x_1577, 3, x_1569);
lean_ctor_set_uint8(x_1577, sizeof(void*)*4, x_1458);
x_1578 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1578, 0, x_1577);
lean_ctor_set(x_1578, 1, x_1540);
lean_ctor_set(x_1578, 2, x_1541);
lean_ctor_set(x_1578, 3, x_1265);
lean_ctor_set_uint8(x_1578, sizeof(void*)*4, x_1402);
lean_ctor_set(x_234, 3, x_1572);
lean_ctor_set(x_234, 2, x_3);
lean_ctor_set(x_234, 1, x_2);
lean_ctor_set(x_234, 0, x_1578);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1458);
lean_ctor_set(x_1, 3, x_1403);
lean_ctor_set(x_1, 2, x_1571);
lean_ctor_set(x_1, 1, x_1570);
lean_ctor_set(x_1, 0, x_1575);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1458);
x_1579 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1579, 0, x_234);
lean_ctor_set(x_1579, 1, x_1573);
lean_ctor_set(x_1579, 2, x_1574);
lean_ctor_set(x_1579, 3, x_1);
lean_ctor_set_uint8(x_1579, sizeof(void*)*4, x_1402);
return x_1579;
}
}
else
{
lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; 
x_1580 = lean_ctor_get(x_234, 0);
x_1581 = lean_ctor_get(x_234, 1);
x_1582 = lean_ctor_get(x_234, 2);
x_1583 = lean_ctor_get(x_234, 3);
lean_inc(x_1583);
lean_inc(x_1582);
lean_inc(x_1581);
lean_inc(x_1580);
lean_dec(x_234);
x_1584 = lean_ctor_get(x_4, 1);
lean_inc(x_1584);
x_1585 = lean_ctor_get(x_4, 2);
lean_inc(x_1585);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1586 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1586 = lean_box(0);
}
x_1587 = lean_ctor_get(x_1275, 0);
lean_inc(x_1587);
x_1588 = lean_ctor_get(x_1275, 1);
lean_inc(x_1588);
x_1589 = lean_ctor_get(x_1275, 2);
lean_inc(x_1589);
x_1590 = lean_ctor_get(x_1275, 3);
lean_inc(x_1590);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 lean_ctor_release(x_1275, 1);
 lean_ctor_release(x_1275, 2);
 lean_ctor_release(x_1275, 3);
 x_1591 = x_1275;
} else {
 lean_dec_ref(x_1275);
 x_1591 = lean_box(0);
}
if (lean_is_scalar(x_1591)) {
 x_1592 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1592 = x_1591;
}
lean_ctor_set(x_1592, 0, x_1580);
lean_ctor_set(x_1592, 1, x_1581);
lean_ctor_set(x_1592, 2, x_1582);
lean_ctor_set(x_1592, 3, x_1583);
lean_ctor_set_uint8(x_1592, sizeof(void*)*4, x_1458);
if (lean_is_scalar(x_1586)) {
 x_1593 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1593 = x_1586;
}
lean_ctor_set(x_1593, 0, x_1592);
lean_ctor_set(x_1593, 1, x_1540);
lean_ctor_set(x_1593, 2, x_1541);
lean_ctor_set(x_1593, 3, x_1265);
lean_ctor_set_uint8(x_1593, sizeof(void*)*4, x_1402);
x_1594 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1594, 0, x_1593);
lean_ctor_set(x_1594, 1, x_2);
lean_ctor_set(x_1594, 2, x_3);
lean_ctor_set(x_1594, 3, x_1587);
lean_ctor_set_uint8(x_1594, sizeof(void*)*4, x_1458);
lean_ctor_set(x_1, 3, x_1403);
lean_ctor_set(x_1, 2, x_1585);
lean_ctor_set(x_1, 1, x_1584);
lean_ctor_set(x_1, 0, x_1590);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1458);
x_1595 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1595, 0, x_1594);
lean_ctor_set(x_1595, 1, x_1588);
lean_ctor_set(x_1595, 2, x_1589);
lean_ctor_set(x_1595, 3, x_1);
lean_ctor_set_uint8(x_1595, sizeof(void*)*4, x_1402);
return x_1595;
}
}
else
{
lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; 
x_1596 = lean_ctor_get(x_1, 1);
x_1597 = lean_ctor_get(x_1, 2);
lean_inc(x_1597);
lean_inc(x_1596);
lean_dec(x_1);
x_1598 = lean_ctor_get(x_234, 0);
lean_inc(x_1598);
x_1599 = lean_ctor_get(x_234, 1);
lean_inc(x_1599);
x_1600 = lean_ctor_get(x_234, 2);
lean_inc(x_1600);
x_1601 = lean_ctor_get(x_234, 3);
lean_inc(x_1601);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1602 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1602 = lean_box(0);
}
x_1603 = lean_ctor_get(x_4, 1);
lean_inc(x_1603);
x_1604 = lean_ctor_get(x_4, 2);
lean_inc(x_1604);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1605 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1605 = lean_box(0);
}
x_1606 = lean_ctor_get(x_1275, 0);
lean_inc(x_1606);
x_1607 = lean_ctor_get(x_1275, 1);
lean_inc(x_1607);
x_1608 = lean_ctor_get(x_1275, 2);
lean_inc(x_1608);
x_1609 = lean_ctor_get(x_1275, 3);
lean_inc(x_1609);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 lean_ctor_release(x_1275, 1);
 lean_ctor_release(x_1275, 2);
 lean_ctor_release(x_1275, 3);
 x_1610 = x_1275;
} else {
 lean_dec_ref(x_1275);
 x_1610 = lean_box(0);
}
if (lean_is_scalar(x_1610)) {
 x_1611 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1611 = x_1610;
}
lean_ctor_set(x_1611, 0, x_1598);
lean_ctor_set(x_1611, 1, x_1599);
lean_ctor_set(x_1611, 2, x_1600);
lean_ctor_set(x_1611, 3, x_1601);
lean_ctor_set_uint8(x_1611, sizeof(void*)*4, x_1458);
if (lean_is_scalar(x_1605)) {
 x_1612 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1612 = x_1605;
}
lean_ctor_set(x_1612, 0, x_1611);
lean_ctor_set(x_1612, 1, x_1596);
lean_ctor_set(x_1612, 2, x_1597);
lean_ctor_set(x_1612, 3, x_1265);
lean_ctor_set_uint8(x_1612, sizeof(void*)*4, x_1402);
if (lean_is_scalar(x_1602)) {
 x_1613 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1613 = x_1602;
}
lean_ctor_set(x_1613, 0, x_1612);
lean_ctor_set(x_1613, 1, x_2);
lean_ctor_set(x_1613, 2, x_3);
lean_ctor_set(x_1613, 3, x_1606);
lean_ctor_set_uint8(x_1613, sizeof(void*)*4, x_1458);
x_1614 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1614, 0, x_1609);
lean_ctor_set(x_1614, 1, x_1603);
lean_ctor_set(x_1614, 2, x_1604);
lean_ctor_set(x_1614, 3, x_1403);
lean_ctor_set_uint8(x_1614, sizeof(void*)*4, x_1458);
x_1615 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1615, 0, x_1613);
lean_ctor_set(x_1615, 1, x_1607);
lean_ctor_set(x_1615, 2, x_1608);
lean_ctor_set(x_1615, 3, x_1614);
lean_ctor_set_uint8(x_1615, sizeof(void*)*4, x_1402);
return x_1615;
}
}
}
}
else
{
lean_object* x_1616; 
x_1616 = lean_ctor_get(x_4, 3);
lean_inc(x_1616);
if (lean_obj_tag(x_1616) == 0)
{
uint8_t x_1617; 
x_1617 = !lean_is_exclusive(x_1275);
if (x_1617 == 0)
{
lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; uint8_t x_1622; 
x_1618 = lean_ctor_get(x_1275, 3);
lean_dec(x_1618);
x_1619 = lean_ctor_get(x_1275, 2);
lean_dec(x_1619);
x_1620 = lean_ctor_get(x_1275, 1);
lean_dec(x_1620);
x_1621 = lean_ctor_get(x_1275, 0);
lean_dec(x_1621);
x_1622 = !lean_is_exclusive(x_1);
if (x_1622 == 0)
{
lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; uint8_t x_1627; 
x_1623 = lean_ctor_get(x_1, 1);
x_1624 = lean_ctor_get(x_1, 2);
x_1625 = lean_ctor_get(x_1, 3);
lean_dec(x_1625);
x_1626 = lean_ctor_get(x_1, 0);
lean_dec(x_1626);
x_1627 = !lean_is_exclusive(x_234);
if (x_1627 == 0)
{
lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; 
x_1628 = lean_ctor_get(x_234, 0);
x_1629 = lean_ctor_get(x_234, 1);
x_1630 = lean_ctor_get(x_234, 2);
x_1631 = lean_ctor_get(x_234, 3);
lean_ctor_set(x_1275, 3, x_1631);
lean_ctor_set(x_1275, 2, x_1630);
lean_ctor_set(x_1275, 1, x_1629);
lean_ctor_set(x_1275, 0, x_1628);
lean_ctor_set(x_234, 3, x_1616);
lean_ctor_set(x_234, 2, x_1624);
lean_ctor_set(x_234, 1, x_1623);
lean_ctor_set(x_234, 0, x_1275);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1274);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1402);
return x_1;
}
else
{
lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; 
x_1632 = lean_ctor_get(x_234, 0);
x_1633 = lean_ctor_get(x_234, 1);
x_1634 = lean_ctor_get(x_234, 2);
x_1635 = lean_ctor_get(x_234, 3);
lean_inc(x_1635);
lean_inc(x_1634);
lean_inc(x_1633);
lean_inc(x_1632);
lean_dec(x_234);
lean_ctor_set(x_1275, 3, x_1635);
lean_ctor_set(x_1275, 2, x_1634);
lean_ctor_set(x_1275, 1, x_1633);
lean_ctor_set(x_1275, 0, x_1632);
x_1636 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1636, 0, x_1275);
lean_ctor_set(x_1636, 1, x_1623);
lean_ctor_set(x_1636, 2, x_1624);
lean_ctor_set(x_1636, 3, x_1616);
lean_ctor_set_uint8(x_1636, sizeof(void*)*4, x_1274);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_1636);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1402);
return x_1;
}
}
else
{
lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; 
x_1637 = lean_ctor_get(x_1, 1);
x_1638 = lean_ctor_get(x_1, 2);
lean_inc(x_1638);
lean_inc(x_1637);
lean_dec(x_1);
x_1639 = lean_ctor_get(x_234, 0);
lean_inc(x_1639);
x_1640 = lean_ctor_get(x_234, 1);
lean_inc(x_1640);
x_1641 = lean_ctor_get(x_234, 2);
lean_inc(x_1641);
x_1642 = lean_ctor_get(x_234, 3);
lean_inc(x_1642);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1643 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1643 = lean_box(0);
}
lean_ctor_set(x_1275, 3, x_1642);
lean_ctor_set(x_1275, 2, x_1641);
lean_ctor_set(x_1275, 1, x_1640);
lean_ctor_set(x_1275, 0, x_1639);
if (lean_is_scalar(x_1643)) {
 x_1644 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1644 = x_1643;
}
lean_ctor_set(x_1644, 0, x_1275);
lean_ctor_set(x_1644, 1, x_1637);
lean_ctor_set(x_1644, 2, x_1638);
lean_ctor_set(x_1644, 3, x_1616);
lean_ctor_set_uint8(x_1644, sizeof(void*)*4, x_1274);
x_1645 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1645, 0, x_1644);
lean_ctor_set(x_1645, 1, x_2);
lean_ctor_set(x_1645, 2, x_3);
lean_ctor_set(x_1645, 3, x_4);
lean_ctor_set_uint8(x_1645, sizeof(void*)*4, x_1402);
return x_1645;
}
}
else
{
lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; 
lean_dec(x_1275);
x_1646 = lean_ctor_get(x_1, 1);
lean_inc(x_1646);
x_1647 = lean_ctor_get(x_1, 2);
lean_inc(x_1647);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_1648 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1648 = lean_box(0);
}
x_1649 = lean_ctor_get(x_234, 0);
lean_inc(x_1649);
x_1650 = lean_ctor_get(x_234, 1);
lean_inc(x_1650);
x_1651 = lean_ctor_get(x_234, 2);
lean_inc(x_1651);
x_1652 = lean_ctor_get(x_234, 3);
lean_inc(x_1652);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1653 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1653 = lean_box(0);
}
x_1654 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1654, 0, x_1649);
lean_ctor_set(x_1654, 1, x_1650);
lean_ctor_set(x_1654, 2, x_1651);
lean_ctor_set(x_1654, 3, x_1652);
lean_ctor_set_uint8(x_1654, sizeof(void*)*4, x_1402);
if (lean_is_scalar(x_1653)) {
 x_1655 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1655 = x_1653;
}
lean_ctor_set(x_1655, 0, x_1654);
lean_ctor_set(x_1655, 1, x_1646);
lean_ctor_set(x_1655, 2, x_1647);
lean_ctor_set(x_1655, 3, x_1616);
lean_ctor_set_uint8(x_1655, sizeof(void*)*4, x_1274);
if (lean_is_scalar(x_1648)) {
 x_1656 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1656 = x_1648;
}
lean_ctor_set(x_1656, 0, x_1655);
lean_ctor_set(x_1656, 1, x_2);
lean_ctor_set(x_1656, 2, x_3);
lean_ctor_set(x_1656, 3, x_4);
lean_ctor_set_uint8(x_1656, sizeof(void*)*4, x_1402);
return x_1656;
}
}
else
{
uint8_t x_1657; 
x_1657 = lean_ctor_get_uint8(x_1616, sizeof(void*)*4);
if (x_1657 == 0)
{
uint8_t x_1658; 
x_1658 = !lean_is_exclusive(x_1);
if (x_1658 == 0)
{
lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; uint8_t x_1663; 
x_1659 = lean_ctor_get(x_1, 1);
x_1660 = lean_ctor_get(x_1, 2);
x_1661 = lean_ctor_get(x_1, 3);
lean_dec(x_1661);
x_1662 = lean_ctor_get(x_1, 0);
lean_dec(x_1662);
x_1663 = !lean_is_exclusive(x_234);
if (x_1663 == 0)
{
uint8_t x_1664; 
x_1664 = !lean_is_exclusive(x_4);
if (x_1664 == 0)
{
lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; uint8_t x_1673; 
x_1665 = lean_ctor_get(x_234, 0);
x_1666 = lean_ctor_get(x_234, 1);
x_1667 = lean_ctor_get(x_234, 2);
x_1668 = lean_ctor_get(x_234, 3);
x_1669 = lean_ctor_get(x_4, 1);
x_1670 = lean_ctor_get(x_4, 2);
x_1671 = lean_ctor_get(x_4, 3);
lean_dec(x_1671);
x_1672 = lean_ctor_get(x_4, 0);
lean_dec(x_1672);
x_1673 = !lean_is_exclusive(x_1616);
if (x_1673 == 0)
{
lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; 
x_1674 = lean_ctor_get(x_1616, 0);
x_1675 = lean_ctor_get(x_1616, 1);
x_1676 = lean_ctor_get(x_1616, 2);
x_1677 = lean_ctor_get(x_1616, 3);
lean_ctor_set(x_1616, 3, x_1668);
lean_ctor_set(x_1616, 2, x_1667);
lean_ctor_set(x_1616, 1, x_1666);
lean_ctor_set(x_1616, 0, x_1665);
lean_ctor_set_uint8(x_1616, sizeof(void*)*4, x_1402);
lean_ctor_set(x_4, 3, x_1265);
lean_ctor_set(x_4, 2, x_1660);
lean_ctor_set(x_4, 1, x_1659);
lean_ctor_set(x_4, 0, x_1616);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1657);
lean_ctor_set(x_234, 3, x_1275);
lean_ctor_set(x_234, 2, x_3);
lean_ctor_set(x_234, 1, x_2);
lean_ctor_set(x_234, 0, x_4);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1402);
lean_ctor_set(x_1, 3, x_1677);
lean_ctor_set(x_1, 2, x_1676);
lean_ctor_set(x_1, 1, x_1675);
lean_ctor_set(x_1, 0, x_1674);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1402);
x_1678 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1678, 0, x_234);
lean_ctor_set(x_1678, 1, x_1669);
lean_ctor_set(x_1678, 2, x_1670);
lean_ctor_set(x_1678, 3, x_1);
lean_ctor_set_uint8(x_1678, sizeof(void*)*4, x_1657);
return x_1678;
}
else
{
lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; 
x_1679 = lean_ctor_get(x_1616, 0);
x_1680 = lean_ctor_get(x_1616, 1);
x_1681 = lean_ctor_get(x_1616, 2);
x_1682 = lean_ctor_get(x_1616, 3);
lean_inc(x_1682);
lean_inc(x_1681);
lean_inc(x_1680);
lean_inc(x_1679);
lean_dec(x_1616);
x_1683 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1683, 0, x_1665);
lean_ctor_set(x_1683, 1, x_1666);
lean_ctor_set(x_1683, 2, x_1667);
lean_ctor_set(x_1683, 3, x_1668);
lean_ctor_set_uint8(x_1683, sizeof(void*)*4, x_1402);
lean_ctor_set(x_4, 3, x_1265);
lean_ctor_set(x_4, 2, x_1660);
lean_ctor_set(x_4, 1, x_1659);
lean_ctor_set(x_4, 0, x_1683);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1657);
lean_ctor_set(x_234, 3, x_1275);
lean_ctor_set(x_234, 2, x_3);
lean_ctor_set(x_234, 1, x_2);
lean_ctor_set(x_234, 0, x_4);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1402);
lean_ctor_set(x_1, 3, x_1682);
lean_ctor_set(x_1, 2, x_1681);
lean_ctor_set(x_1, 1, x_1680);
lean_ctor_set(x_1, 0, x_1679);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1402);
x_1684 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1684, 0, x_234);
lean_ctor_set(x_1684, 1, x_1669);
lean_ctor_set(x_1684, 2, x_1670);
lean_ctor_set(x_1684, 3, x_1);
lean_ctor_set_uint8(x_1684, sizeof(void*)*4, x_1657);
return x_1684;
}
}
else
{
lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; 
x_1685 = lean_ctor_get(x_234, 0);
x_1686 = lean_ctor_get(x_234, 1);
x_1687 = lean_ctor_get(x_234, 2);
x_1688 = lean_ctor_get(x_234, 3);
x_1689 = lean_ctor_get(x_4, 1);
x_1690 = lean_ctor_get(x_4, 2);
lean_inc(x_1690);
lean_inc(x_1689);
lean_dec(x_4);
x_1691 = lean_ctor_get(x_1616, 0);
lean_inc(x_1691);
x_1692 = lean_ctor_get(x_1616, 1);
lean_inc(x_1692);
x_1693 = lean_ctor_get(x_1616, 2);
lean_inc(x_1693);
x_1694 = lean_ctor_get(x_1616, 3);
lean_inc(x_1694);
if (lean_is_exclusive(x_1616)) {
 lean_ctor_release(x_1616, 0);
 lean_ctor_release(x_1616, 1);
 lean_ctor_release(x_1616, 2);
 lean_ctor_release(x_1616, 3);
 x_1695 = x_1616;
} else {
 lean_dec_ref(x_1616);
 x_1695 = lean_box(0);
}
if (lean_is_scalar(x_1695)) {
 x_1696 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1696 = x_1695;
}
lean_ctor_set(x_1696, 0, x_1685);
lean_ctor_set(x_1696, 1, x_1686);
lean_ctor_set(x_1696, 2, x_1687);
lean_ctor_set(x_1696, 3, x_1688);
lean_ctor_set_uint8(x_1696, sizeof(void*)*4, x_1402);
x_1697 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1697, 0, x_1696);
lean_ctor_set(x_1697, 1, x_1659);
lean_ctor_set(x_1697, 2, x_1660);
lean_ctor_set(x_1697, 3, x_1265);
lean_ctor_set_uint8(x_1697, sizeof(void*)*4, x_1657);
lean_ctor_set(x_234, 3, x_1275);
lean_ctor_set(x_234, 2, x_3);
lean_ctor_set(x_234, 1, x_2);
lean_ctor_set(x_234, 0, x_1697);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1402);
lean_ctor_set(x_1, 3, x_1694);
lean_ctor_set(x_1, 2, x_1693);
lean_ctor_set(x_1, 1, x_1692);
lean_ctor_set(x_1, 0, x_1691);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1402);
x_1698 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1698, 0, x_234);
lean_ctor_set(x_1698, 1, x_1689);
lean_ctor_set(x_1698, 2, x_1690);
lean_ctor_set(x_1698, 3, x_1);
lean_ctor_set_uint8(x_1698, sizeof(void*)*4, x_1657);
return x_1698;
}
}
else
{
lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; 
x_1699 = lean_ctor_get(x_234, 0);
x_1700 = lean_ctor_get(x_234, 1);
x_1701 = lean_ctor_get(x_234, 2);
x_1702 = lean_ctor_get(x_234, 3);
lean_inc(x_1702);
lean_inc(x_1701);
lean_inc(x_1700);
lean_inc(x_1699);
lean_dec(x_234);
x_1703 = lean_ctor_get(x_4, 1);
lean_inc(x_1703);
x_1704 = lean_ctor_get(x_4, 2);
lean_inc(x_1704);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1705 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1705 = lean_box(0);
}
x_1706 = lean_ctor_get(x_1616, 0);
lean_inc(x_1706);
x_1707 = lean_ctor_get(x_1616, 1);
lean_inc(x_1707);
x_1708 = lean_ctor_get(x_1616, 2);
lean_inc(x_1708);
x_1709 = lean_ctor_get(x_1616, 3);
lean_inc(x_1709);
if (lean_is_exclusive(x_1616)) {
 lean_ctor_release(x_1616, 0);
 lean_ctor_release(x_1616, 1);
 lean_ctor_release(x_1616, 2);
 lean_ctor_release(x_1616, 3);
 x_1710 = x_1616;
} else {
 lean_dec_ref(x_1616);
 x_1710 = lean_box(0);
}
if (lean_is_scalar(x_1710)) {
 x_1711 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1711 = x_1710;
}
lean_ctor_set(x_1711, 0, x_1699);
lean_ctor_set(x_1711, 1, x_1700);
lean_ctor_set(x_1711, 2, x_1701);
lean_ctor_set(x_1711, 3, x_1702);
lean_ctor_set_uint8(x_1711, sizeof(void*)*4, x_1402);
if (lean_is_scalar(x_1705)) {
 x_1712 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1712 = x_1705;
}
lean_ctor_set(x_1712, 0, x_1711);
lean_ctor_set(x_1712, 1, x_1659);
lean_ctor_set(x_1712, 2, x_1660);
lean_ctor_set(x_1712, 3, x_1265);
lean_ctor_set_uint8(x_1712, sizeof(void*)*4, x_1657);
x_1713 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1713, 0, x_1712);
lean_ctor_set(x_1713, 1, x_2);
lean_ctor_set(x_1713, 2, x_3);
lean_ctor_set(x_1713, 3, x_1275);
lean_ctor_set_uint8(x_1713, sizeof(void*)*4, x_1402);
lean_ctor_set(x_1, 3, x_1709);
lean_ctor_set(x_1, 2, x_1708);
lean_ctor_set(x_1, 1, x_1707);
lean_ctor_set(x_1, 0, x_1706);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1402);
x_1714 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1714, 0, x_1713);
lean_ctor_set(x_1714, 1, x_1703);
lean_ctor_set(x_1714, 2, x_1704);
lean_ctor_set(x_1714, 3, x_1);
lean_ctor_set_uint8(x_1714, sizeof(void*)*4, x_1657);
return x_1714;
}
}
else
{
lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; 
x_1715 = lean_ctor_get(x_1, 1);
x_1716 = lean_ctor_get(x_1, 2);
lean_inc(x_1716);
lean_inc(x_1715);
lean_dec(x_1);
x_1717 = lean_ctor_get(x_234, 0);
lean_inc(x_1717);
x_1718 = lean_ctor_get(x_234, 1);
lean_inc(x_1718);
x_1719 = lean_ctor_get(x_234, 2);
lean_inc(x_1719);
x_1720 = lean_ctor_get(x_234, 3);
lean_inc(x_1720);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1721 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1721 = lean_box(0);
}
x_1722 = lean_ctor_get(x_4, 1);
lean_inc(x_1722);
x_1723 = lean_ctor_get(x_4, 2);
lean_inc(x_1723);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1724 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1724 = lean_box(0);
}
x_1725 = lean_ctor_get(x_1616, 0);
lean_inc(x_1725);
x_1726 = lean_ctor_get(x_1616, 1);
lean_inc(x_1726);
x_1727 = lean_ctor_get(x_1616, 2);
lean_inc(x_1727);
x_1728 = lean_ctor_get(x_1616, 3);
lean_inc(x_1728);
if (lean_is_exclusive(x_1616)) {
 lean_ctor_release(x_1616, 0);
 lean_ctor_release(x_1616, 1);
 lean_ctor_release(x_1616, 2);
 lean_ctor_release(x_1616, 3);
 x_1729 = x_1616;
} else {
 lean_dec_ref(x_1616);
 x_1729 = lean_box(0);
}
if (lean_is_scalar(x_1729)) {
 x_1730 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1730 = x_1729;
}
lean_ctor_set(x_1730, 0, x_1717);
lean_ctor_set(x_1730, 1, x_1718);
lean_ctor_set(x_1730, 2, x_1719);
lean_ctor_set(x_1730, 3, x_1720);
lean_ctor_set_uint8(x_1730, sizeof(void*)*4, x_1402);
if (lean_is_scalar(x_1724)) {
 x_1731 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1731 = x_1724;
}
lean_ctor_set(x_1731, 0, x_1730);
lean_ctor_set(x_1731, 1, x_1715);
lean_ctor_set(x_1731, 2, x_1716);
lean_ctor_set(x_1731, 3, x_1265);
lean_ctor_set_uint8(x_1731, sizeof(void*)*4, x_1657);
if (lean_is_scalar(x_1721)) {
 x_1732 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1732 = x_1721;
}
lean_ctor_set(x_1732, 0, x_1731);
lean_ctor_set(x_1732, 1, x_2);
lean_ctor_set(x_1732, 2, x_3);
lean_ctor_set(x_1732, 3, x_1275);
lean_ctor_set_uint8(x_1732, sizeof(void*)*4, x_1402);
x_1733 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1733, 0, x_1725);
lean_ctor_set(x_1733, 1, x_1726);
lean_ctor_set(x_1733, 2, x_1727);
lean_ctor_set(x_1733, 3, x_1728);
lean_ctor_set_uint8(x_1733, sizeof(void*)*4, x_1402);
x_1734 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1734, 0, x_1732);
lean_ctor_set(x_1734, 1, x_1722);
lean_ctor_set(x_1734, 2, x_1723);
lean_ctor_set(x_1734, 3, x_1733);
lean_ctor_set_uint8(x_1734, sizeof(void*)*4, x_1657);
return x_1734;
}
}
else
{
uint8_t x_1735; 
x_1735 = !lean_is_exclusive(x_1);
if (x_1735 == 0)
{
lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; uint8_t x_1740; 
x_1736 = lean_ctor_get(x_1, 1);
x_1737 = lean_ctor_get(x_1, 2);
x_1738 = lean_ctor_get(x_1, 3);
lean_dec(x_1738);
x_1739 = lean_ctor_get(x_1, 0);
lean_dec(x_1739);
x_1740 = !lean_is_exclusive(x_234);
if (x_1740 == 0)
{
uint8_t x_1741; 
x_1741 = !lean_is_exclusive(x_4);
if (x_1741 == 0)
{
lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; uint8_t x_1750; 
x_1742 = lean_ctor_get(x_234, 0);
x_1743 = lean_ctor_get(x_234, 1);
x_1744 = lean_ctor_get(x_234, 2);
x_1745 = lean_ctor_get(x_234, 3);
x_1746 = lean_ctor_get(x_4, 1);
x_1747 = lean_ctor_get(x_4, 2);
x_1748 = lean_ctor_get(x_4, 3);
lean_dec(x_1748);
x_1749 = lean_ctor_get(x_4, 0);
lean_dec(x_1749);
x_1750 = !lean_is_exclusive(x_1275);
if (x_1750 == 0)
{
lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; 
x_1751 = lean_ctor_get(x_1275, 0);
x_1752 = lean_ctor_get(x_1275, 1);
x_1753 = lean_ctor_get(x_1275, 2);
x_1754 = lean_ctor_get(x_1275, 3);
lean_ctor_set(x_1275, 3, x_1745);
lean_ctor_set(x_1275, 2, x_1744);
lean_ctor_set(x_1275, 1, x_1743);
lean_ctor_set(x_1275, 0, x_1742);
lean_ctor_set_uint8(x_1275, sizeof(void*)*4, x_1657);
lean_ctor_set(x_4, 3, x_1265);
lean_ctor_set(x_4, 2, x_1737);
lean_ctor_set(x_4, 1, x_1736);
lean_ctor_set(x_234, 3, x_1754);
lean_ctor_set(x_234, 2, x_1753);
lean_ctor_set(x_234, 1, x_1752);
lean_ctor_set(x_234, 0, x_1751);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1657);
lean_ctor_set(x_1, 3, x_1616);
lean_ctor_set(x_1, 2, x_1747);
lean_ctor_set(x_1, 1, x_1746);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1274);
x_1755 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1755, 0, x_4);
lean_ctor_set(x_1755, 1, x_2);
lean_ctor_set(x_1755, 2, x_3);
lean_ctor_set(x_1755, 3, x_1);
lean_ctor_set_uint8(x_1755, sizeof(void*)*4, x_1657);
return x_1755;
}
else
{
lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; 
x_1756 = lean_ctor_get(x_1275, 0);
x_1757 = lean_ctor_get(x_1275, 1);
x_1758 = lean_ctor_get(x_1275, 2);
x_1759 = lean_ctor_get(x_1275, 3);
lean_inc(x_1759);
lean_inc(x_1758);
lean_inc(x_1757);
lean_inc(x_1756);
lean_dec(x_1275);
x_1760 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1760, 0, x_1742);
lean_ctor_set(x_1760, 1, x_1743);
lean_ctor_set(x_1760, 2, x_1744);
lean_ctor_set(x_1760, 3, x_1745);
lean_ctor_set_uint8(x_1760, sizeof(void*)*4, x_1657);
lean_ctor_set(x_4, 3, x_1265);
lean_ctor_set(x_4, 2, x_1737);
lean_ctor_set(x_4, 1, x_1736);
lean_ctor_set(x_4, 0, x_1760);
lean_ctor_set(x_234, 3, x_1759);
lean_ctor_set(x_234, 2, x_1758);
lean_ctor_set(x_234, 1, x_1757);
lean_ctor_set(x_234, 0, x_1756);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1657);
lean_ctor_set(x_1, 3, x_1616);
lean_ctor_set(x_1, 2, x_1747);
lean_ctor_set(x_1, 1, x_1746);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1274);
x_1761 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1761, 0, x_4);
lean_ctor_set(x_1761, 1, x_2);
lean_ctor_set(x_1761, 2, x_3);
lean_ctor_set(x_1761, 3, x_1);
lean_ctor_set_uint8(x_1761, sizeof(void*)*4, x_1657);
return x_1761;
}
}
else
{
lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; 
x_1762 = lean_ctor_get(x_234, 0);
x_1763 = lean_ctor_get(x_234, 1);
x_1764 = lean_ctor_get(x_234, 2);
x_1765 = lean_ctor_get(x_234, 3);
x_1766 = lean_ctor_get(x_4, 1);
x_1767 = lean_ctor_get(x_4, 2);
lean_inc(x_1767);
lean_inc(x_1766);
lean_dec(x_4);
x_1768 = lean_ctor_get(x_1275, 0);
lean_inc(x_1768);
x_1769 = lean_ctor_get(x_1275, 1);
lean_inc(x_1769);
x_1770 = lean_ctor_get(x_1275, 2);
lean_inc(x_1770);
x_1771 = lean_ctor_get(x_1275, 3);
lean_inc(x_1771);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 lean_ctor_release(x_1275, 1);
 lean_ctor_release(x_1275, 2);
 lean_ctor_release(x_1275, 3);
 x_1772 = x_1275;
} else {
 lean_dec_ref(x_1275);
 x_1772 = lean_box(0);
}
if (lean_is_scalar(x_1772)) {
 x_1773 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1773 = x_1772;
}
lean_ctor_set(x_1773, 0, x_1762);
lean_ctor_set(x_1773, 1, x_1763);
lean_ctor_set(x_1773, 2, x_1764);
lean_ctor_set(x_1773, 3, x_1765);
lean_ctor_set_uint8(x_1773, sizeof(void*)*4, x_1657);
x_1774 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1774, 0, x_1773);
lean_ctor_set(x_1774, 1, x_1736);
lean_ctor_set(x_1774, 2, x_1737);
lean_ctor_set(x_1774, 3, x_1265);
lean_ctor_set_uint8(x_1774, sizeof(void*)*4, x_1274);
lean_ctor_set(x_234, 3, x_1771);
lean_ctor_set(x_234, 2, x_1770);
lean_ctor_set(x_234, 1, x_1769);
lean_ctor_set(x_234, 0, x_1768);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1657);
lean_ctor_set(x_1, 3, x_1616);
lean_ctor_set(x_1, 2, x_1767);
lean_ctor_set(x_1, 1, x_1766);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1274);
x_1775 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1775, 0, x_1774);
lean_ctor_set(x_1775, 1, x_2);
lean_ctor_set(x_1775, 2, x_3);
lean_ctor_set(x_1775, 3, x_1);
lean_ctor_set_uint8(x_1775, sizeof(void*)*4, x_1657);
return x_1775;
}
}
else
{
lean_object* x_1776; lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; 
x_1776 = lean_ctor_get(x_234, 0);
x_1777 = lean_ctor_get(x_234, 1);
x_1778 = lean_ctor_get(x_234, 2);
x_1779 = lean_ctor_get(x_234, 3);
lean_inc(x_1779);
lean_inc(x_1778);
lean_inc(x_1777);
lean_inc(x_1776);
lean_dec(x_234);
x_1780 = lean_ctor_get(x_4, 1);
lean_inc(x_1780);
x_1781 = lean_ctor_get(x_4, 2);
lean_inc(x_1781);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1782 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1782 = lean_box(0);
}
x_1783 = lean_ctor_get(x_1275, 0);
lean_inc(x_1783);
x_1784 = lean_ctor_get(x_1275, 1);
lean_inc(x_1784);
x_1785 = lean_ctor_get(x_1275, 2);
lean_inc(x_1785);
x_1786 = lean_ctor_get(x_1275, 3);
lean_inc(x_1786);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 lean_ctor_release(x_1275, 1);
 lean_ctor_release(x_1275, 2);
 lean_ctor_release(x_1275, 3);
 x_1787 = x_1275;
} else {
 lean_dec_ref(x_1275);
 x_1787 = lean_box(0);
}
if (lean_is_scalar(x_1787)) {
 x_1788 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1788 = x_1787;
}
lean_ctor_set(x_1788, 0, x_1776);
lean_ctor_set(x_1788, 1, x_1777);
lean_ctor_set(x_1788, 2, x_1778);
lean_ctor_set(x_1788, 3, x_1779);
lean_ctor_set_uint8(x_1788, sizeof(void*)*4, x_1657);
if (lean_is_scalar(x_1782)) {
 x_1789 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1789 = x_1782;
}
lean_ctor_set(x_1789, 0, x_1788);
lean_ctor_set(x_1789, 1, x_1736);
lean_ctor_set(x_1789, 2, x_1737);
lean_ctor_set(x_1789, 3, x_1265);
lean_ctor_set_uint8(x_1789, sizeof(void*)*4, x_1274);
x_1790 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1790, 0, x_1783);
lean_ctor_set(x_1790, 1, x_1784);
lean_ctor_set(x_1790, 2, x_1785);
lean_ctor_set(x_1790, 3, x_1786);
lean_ctor_set_uint8(x_1790, sizeof(void*)*4, x_1657);
lean_ctor_set(x_1, 3, x_1616);
lean_ctor_set(x_1, 2, x_1781);
lean_ctor_set(x_1, 1, x_1780);
lean_ctor_set(x_1, 0, x_1790);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1274);
x_1791 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1791, 0, x_1789);
lean_ctor_set(x_1791, 1, x_2);
lean_ctor_set(x_1791, 2, x_3);
lean_ctor_set(x_1791, 3, x_1);
lean_ctor_set_uint8(x_1791, sizeof(void*)*4, x_1657);
return x_1791;
}
}
else
{
lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; 
x_1792 = lean_ctor_get(x_1, 1);
x_1793 = lean_ctor_get(x_1, 2);
lean_inc(x_1793);
lean_inc(x_1792);
lean_dec(x_1);
x_1794 = lean_ctor_get(x_234, 0);
lean_inc(x_1794);
x_1795 = lean_ctor_get(x_234, 1);
lean_inc(x_1795);
x_1796 = lean_ctor_get(x_234, 2);
lean_inc(x_1796);
x_1797 = lean_ctor_get(x_234, 3);
lean_inc(x_1797);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1798 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1798 = lean_box(0);
}
x_1799 = lean_ctor_get(x_4, 1);
lean_inc(x_1799);
x_1800 = lean_ctor_get(x_4, 2);
lean_inc(x_1800);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1801 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1801 = lean_box(0);
}
x_1802 = lean_ctor_get(x_1275, 0);
lean_inc(x_1802);
x_1803 = lean_ctor_get(x_1275, 1);
lean_inc(x_1803);
x_1804 = lean_ctor_get(x_1275, 2);
lean_inc(x_1804);
x_1805 = lean_ctor_get(x_1275, 3);
lean_inc(x_1805);
if (lean_is_exclusive(x_1275)) {
 lean_ctor_release(x_1275, 0);
 lean_ctor_release(x_1275, 1);
 lean_ctor_release(x_1275, 2);
 lean_ctor_release(x_1275, 3);
 x_1806 = x_1275;
} else {
 lean_dec_ref(x_1275);
 x_1806 = lean_box(0);
}
if (lean_is_scalar(x_1806)) {
 x_1807 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1807 = x_1806;
}
lean_ctor_set(x_1807, 0, x_1794);
lean_ctor_set(x_1807, 1, x_1795);
lean_ctor_set(x_1807, 2, x_1796);
lean_ctor_set(x_1807, 3, x_1797);
lean_ctor_set_uint8(x_1807, sizeof(void*)*4, x_1657);
if (lean_is_scalar(x_1801)) {
 x_1808 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1808 = x_1801;
}
lean_ctor_set(x_1808, 0, x_1807);
lean_ctor_set(x_1808, 1, x_1792);
lean_ctor_set(x_1808, 2, x_1793);
lean_ctor_set(x_1808, 3, x_1265);
lean_ctor_set_uint8(x_1808, sizeof(void*)*4, x_1274);
if (lean_is_scalar(x_1798)) {
 x_1809 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1809 = x_1798;
}
lean_ctor_set(x_1809, 0, x_1802);
lean_ctor_set(x_1809, 1, x_1803);
lean_ctor_set(x_1809, 2, x_1804);
lean_ctor_set(x_1809, 3, x_1805);
lean_ctor_set_uint8(x_1809, sizeof(void*)*4, x_1657);
x_1810 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1810, 0, x_1809);
lean_ctor_set(x_1810, 1, x_1799);
lean_ctor_set(x_1810, 2, x_1800);
lean_ctor_set(x_1810, 3, x_1616);
lean_ctor_set_uint8(x_1810, sizeof(void*)*4, x_1274);
x_1811 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1811, 0, x_1808);
lean_ctor_set(x_1811, 1, x_2);
lean_ctor_set(x_1811, 2, x_3);
lean_ctor_set(x_1811, 3, x_1810);
lean_ctor_set_uint8(x_1811, sizeof(void*)*4, x_1657);
return x_1811;
}
}
}
}
}
}
else
{
uint8_t x_1812; 
x_1812 = !lean_is_exclusive(x_1);
if (x_1812 == 0)
{
lean_object* x_1813; lean_object* x_1814; uint8_t x_1815; 
x_1813 = lean_ctor_get(x_1, 3);
lean_dec(x_1813);
x_1814 = lean_ctor_get(x_1, 0);
lean_dec(x_1814);
x_1815 = !lean_is_exclusive(x_234);
if (x_1815 == 0)
{
lean_object* x_1816; 
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1274);
x_1816 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1816, 0, x_1);
lean_ctor_set(x_1816, 1, x_2);
lean_ctor_set(x_1816, 2, x_3);
lean_ctor_set(x_1816, 3, x_4);
lean_ctor_set_uint8(x_1816, sizeof(void*)*4, x_1274);
return x_1816;
}
else
{
lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; 
x_1817 = lean_ctor_get(x_234, 0);
x_1818 = lean_ctor_get(x_234, 1);
x_1819 = lean_ctor_get(x_234, 2);
x_1820 = lean_ctor_get(x_234, 3);
lean_inc(x_1820);
lean_inc(x_1819);
lean_inc(x_1818);
lean_inc(x_1817);
lean_dec(x_234);
x_1821 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1821, 0, x_1817);
lean_ctor_set(x_1821, 1, x_1818);
lean_ctor_set(x_1821, 2, x_1819);
lean_ctor_set(x_1821, 3, x_1820);
lean_ctor_set_uint8(x_1821, sizeof(void*)*4, x_1274);
lean_ctor_set(x_1, 0, x_1821);
x_1822 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1822, 0, x_1);
lean_ctor_set(x_1822, 1, x_2);
lean_ctor_set(x_1822, 2, x_3);
lean_ctor_set(x_1822, 3, x_4);
lean_ctor_set_uint8(x_1822, sizeof(void*)*4, x_1274);
return x_1822;
}
}
else
{
lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; 
x_1823 = lean_ctor_get(x_1, 1);
x_1824 = lean_ctor_get(x_1, 2);
lean_inc(x_1824);
lean_inc(x_1823);
lean_dec(x_1);
x_1825 = lean_ctor_get(x_234, 0);
lean_inc(x_1825);
x_1826 = lean_ctor_get(x_234, 1);
lean_inc(x_1826);
x_1827 = lean_ctor_get(x_234, 2);
lean_inc(x_1827);
x_1828 = lean_ctor_get(x_234, 3);
lean_inc(x_1828);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1829 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1829 = lean_box(0);
}
if (lean_is_scalar(x_1829)) {
 x_1830 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1830 = x_1829;
}
lean_ctor_set(x_1830, 0, x_1825);
lean_ctor_set(x_1830, 1, x_1826);
lean_ctor_set(x_1830, 2, x_1827);
lean_ctor_set(x_1830, 3, x_1828);
lean_ctor_set_uint8(x_1830, sizeof(void*)*4, x_1274);
x_1831 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1831, 0, x_1830);
lean_ctor_set(x_1831, 1, x_1823);
lean_ctor_set(x_1831, 2, x_1824);
lean_ctor_set(x_1831, 3, x_1265);
lean_ctor_set_uint8(x_1831, sizeof(void*)*4, x_233);
x_1832 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1832, 0, x_1831);
lean_ctor_set(x_1832, 1, x_2);
lean_ctor_set(x_1832, 2, x_3);
lean_ctor_set(x_1832, 3, x_4);
lean_ctor_set_uint8(x_1832, sizeof(void*)*4, x_1274);
return x_1832;
}
}
}
}
else
{
uint8_t x_1833; 
x_1833 = lean_ctor_get_uint8(x_1265, sizeof(void*)*4);
if (x_1833 == 0)
{
uint8_t x_1834; 
x_1834 = !lean_is_exclusive(x_1);
if (x_1834 == 0)
{
lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; uint8_t x_1839; 
x_1835 = lean_ctor_get(x_1, 1);
x_1836 = lean_ctor_get(x_1, 2);
x_1837 = lean_ctor_get(x_1, 3);
lean_dec(x_1837);
x_1838 = lean_ctor_get(x_1, 0);
lean_dec(x_1838);
x_1839 = !lean_is_exclusive(x_1265);
if (x_1839 == 0)
{
lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; uint8_t x_1844; 
x_1840 = lean_ctor_get(x_1265, 0);
x_1841 = lean_ctor_get(x_1265, 1);
x_1842 = lean_ctor_get(x_1265, 2);
x_1843 = lean_ctor_get(x_1265, 3);
lean_inc(x_234);
lean_ctor_set(x_1265, 3, x_1840);
lean_ctor_set(x_1265, 2, x_1836);
lean_ctor_set(x_1265, 1, x_1835);
lean_ctor_set(x_1265, 0, x_234);
x_1844 = !lean_is_exclusive(x_234);
if (x_1844 == 0)
{
lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; 
x_1845 = lean_ctor_get(x_234, 3);
lean_dec(x_1845);
x_1846 = lean_ctor_get(x_234, 2);
lean_dec(x_1846);
x_1847 = lean_ctor_get(x_234, 1);
lean_dec(x_1847);
x_1848 = lean_ctor_get(x_234, 0);
lean_dec(x_1848);
lean_ctor_set_uint8(x_1265, sizeof(void*)*4, x_1237);
lean_ctor_set(x_234, 3, x_4);
lean_ctor_set(x_234, 2, x_3);
lean_ctor_set(x_234, 1, x_2);
lean_ctor_set(x_234, 0, x_1843);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_1842);
lean_ctor_set(x_1, 1, x_1841);
lean_ctor_set(x_1, 0, x_1265);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1833);
return x_1;
}
else
{
lean_object* x_1849; 
lean_dec(x_234);
lean_ctor_set_uint8(x_1265, sizeof(void*)*4, x_1237);
x_1849 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1849, 0, x_1843);
lean_ctor_set(x_1849, 1, x_2);
lean_ctor_set(x_1849, 2, x_3);
lean_ctor_set(x_1849, 3, x_4);
lean_ctor_set_uint8(x_1849, sizeof(void*)*4, x_1237);
lean_ctor_set(x_1, 3, x_1849);
lean_ctor_set(x_1, 2, x_1842);
lean_ctor_set(x_1, 1, x_1841);
lean_ctor_set(x_1, 0, x_1265);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1833);
return x_1;
}
}
else
{
lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; 
x_1850 = lean_ctor_get(x_1265, 0);
x_1851 = lean_ctor_get(x_1265, 1);
x_1852 = lean_ctor_get(x_1265, 2);
x_1853 = lean_ctor_get(x_1265, 3);
lean_inc(x_1853);
lean_inc(x_1852);
lean_inc(x_1851);
lean_inc(x_1850);
lean_dec(x_1265);
lean_inc(x_234);
x_1854 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1854, 0, x_234);
lean_ctor_set(x_1854, 1, x_1835);
lean_ctor_set(x_1854, 2, x_1836);
lean_ctor_set(x_1854, 3, x_1850);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1855 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1855 = lean_box(0);
}
lean_ctor_set_uint8(x_1854, sizeof(void*)*4, x_1237);
if (lean_is_scalar(x_1855)) {
 x_1856 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1856 = x_1855;
}
lean_ctor_set(x_1856, 0, x_1853);
lean_ctor_set(x_1856, 1, x_2);
lean_ctor_set(x_1856, 2, x_3);
lean_ctor_set(x_1856, 3, x_4);
lean_ctor_set_uint8(x_1856, sizeof(void*)*4, x_1237);
lean_ctor_set(x_1, 3, x_1856);
lean_ctor_set(x_1, 2, x_1852);
lean_ctor_set(x_1, 1, x_1851);
lean_ctor_set(x_1, 0, x_1854);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1833);
return x_1;
}
}
else
{
lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; 
x_1857 = lean_ctor_get(x_1, 1);
x_1858 = lean_ctor_get(x_1, 2);
lean_inc(x_1858);
lean_inc(x_1857);
lean_dec(x_1);
x_1859 = lean_ctor_get(x_1265, 0);
lean_inc(x_1859);
x_1860 = lean_ctor_get(x_1265, 1);
lean_inc(x_1860);
x_1861 = lean_ctor_get(x_1265, 2);
lean_inc(x_1861);
x_1862 = lean_ctor_get(x_1265, 3);
lean_inc(x_1862);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_1863 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_1863 = lean_box(0);
}
lean_inc(x_234);
if (lean_is_scalar(x_1863)) {
 x_1864 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1864 = x_1863;
}
lean_ctor_set(x_1864, 0, x_234);
lean_ctor_set(x_1864, 1, x_1857);
lean_ctor_set(x_1864, 2, x_1858);
lean_ctor_set(x_1864, 3, x_1859);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1865 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1865 = lean_box(0);
}
lean_ctor_set_uint8(x_1864, sizeof(void*)*4, x_1237);
if (lean_is_scalar(x_1865)) {
 x_1866 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1866 = x_1865;
}
lean_ctor_set(x_1866, 0, x_1862);
lean_ctor_set(x_1866, 1, x_2);
lean_ctor_set(x_1866, 2, x_3);
lean_ctor_set(x_1866, 3, x_4);
lean_ctor_set_uint8(x_1866, sizeof(void*)*4, x_1237);
x_1867 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1867, 0, x_1864);
lean_ctor_set(x_1867, 1, x_1860);
lean_ctor_set(x_1867, 2, x_1861);
lean_ctor_set(x_1867, 3, x_1866);
lean_ctor_set_uint8(x_1867, sizeof(void*)*4, x_1833);
return x_1867;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_1868; 
x_1868 = !lean_is_exclusive(x_1);
if (x_1868 == 0)
{
lean_object* x_1869; lean_object* x_1870; uint8_t x_1871; 
x_1869 = lean_ctor_get(x_1, 3);
lean_dec(x_1869);
x_1870 = lean_ctor_get(x_1, 0);
lean_dec(x_1870);
x_1871 = !lean_is_exclusive(x_234);
if (x_1871 == 0)
{
lean_object* x_1872; 
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1833);
x_1872 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1872, 0, x_1);
lean_ctor_set(x_1872, 1, x_2);
lean_ctor_set(x_1872, 2, x_3);
lean_ctor_set(x_1872, 3, x_4);
lean_ctor_set_uint8(x_1872, sizeof(void*)*4, x_1833);
return x_1872;
}
else
{
lean_object* x_1873; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; 
x_1873 = lean_ctor_get(x_234, 0);
x_1874 = lean_ctor_get(x_234, 1);
x_1875 = lean_ctor_get(x_234, 2);
x_1876 = lean_ctor_get(x_234, 3);
lean_inc(x_1876);
lean_inc(x_1875);
lean_inc(x_1874);
lean_inc(x_1873);
lean_dec(x_234);
x_1877 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1877, 0, x_1873);
lean_ctor_set(x_1877, 1, x_1874);
lean_ctor_set(x_1877, 2, x_1875);
lean_ctor_set(x_1877, 3, x_1876);
lean_ctor_set_uint8(x_1877, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 0, x_1877);
x_1878 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1878, 0, x_1);
lean_ctor_set(x_1878, 1, x_2);
lean_ctor_set(x_1878, 2, x_3);
lean_ctor_set(x_1878, 3, x_4);
lean_ctor_set_uint8(x_1878, sizeof(void*)*4, x_1833);
return x_1878;
}
}
else
{
lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; 
x_1879 = lean_ctor_get(x_1, 1);
x_1880 = lean_ctor_get(x_1, 2);
lean_inc(x_1880);
lean_inc(x_1879);
lean_dec(x_1);
x_1881 = lean_ctor_get(x_234, 0);
lean_inc(x_1881);
x_1882 = lean_ctor_get(x_234, 1);
lean_inc(x_1882);
x_1883 = lean_ctor_get(x_234, 2);
lean_inc(x_1883);
x_1884 = lean_ctor_get(x_234, 3);
lean_inc(x_1884);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1885 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1885 = lean_box(0);
}
if (lean_is_scalar(x_1885)) {
 x_1886 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1886 = x_1885;
}
lean_ctor_set(x_1886, 0, x_1881);
lean_ctor_set(x_1886, 1, x_1882);
lean_ctor_set(x_1886, 2, x_1883);
lean_ctor_set(x_1886, 3, x_1884);
lean_ctor_set_uint8(x_1886, sizeof(void*)*4, x_1833);
x_1887 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1887, 0, x_1886);
lean_ctor_set(x_1887, 1, x_1879);
lean_ctor_set(x_1887, 2, x_1880);
lean_ctor_set(x_1887, 3, x_1265);
lean_ctor_set_uint8(x_1887, sizeof(void*)*4, x_233);
x_1888 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1888, 0, x_1887);
lean_ctor_set(x_1888, 1, x_2);
lean_ctor_set(x_1888, 2, x_3);
lean_ctor_set(x_1888, 3, x_4);
lean_ctor_set_uint8(x_1888, sizeof(void*)*4, x_1833);
return x_1888;
}
}
else
{
uint8_t x_1889; 
x_1889 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_1889 == 0)
{
lean_object* x_1890; 
x_1890 = lean_ctor_get(x_4, 0);
lean_inc(x_1890);
if (lean_obj_tag(x_1890) == 0)
{
lean_object* x_1891; 
x_1891 = lean_ctor_get(x_4, 3);
lean_inc(x_1891);
if (lean_obj_tag(x_1891) == 0)
{
uint8_t x_1892; 
x_1892 = !lean_is_exclusive(x_1);
if (x_1892 == 0)
{
lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; uint8_t x_1897; 
x_1893 = lean_ctor_get(x_1, 1);
x_1894 = lean_ctor_get(x_1, 2);
x_1895 = lean_ctor_get(x_1, 3);
lean_dec(x_1895);
x_1896 = lean_ctor_get(x_1, 0);
lean_dec(x_1896);
x_1897 = !lean_is_exclusive(x_234);
if (x_1897 == 0)
{
uint8_t x_1898; 
x_1898 = !lean_is_exclusive(x_4);
if (x_1898 == 0)
{
lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; 
x_1899 = lean_ctor_get(x_234, 0);
x_1900 = lean_ctor_get(x_234, 1);
x_1901 = lean_ctor_get(x_234, 2);
x_1902 = lean_ctor_get(x_234, 3);
x_1903 = lean_ctor_get(x_4, 1);
x_1904 = lean_ctor_get(x_4, 2);
x_1905 = lean_ctor_get(x_4, 3);
lean_dec(x_1905);
x_1906 = lean_ctor_get(x_4, 0);
lean_dec(x_1906);
lean_ctor_set(x_4, 3, x_1902);
lean_ctor_set(x_4, 2, x_1901);
lean_ctor_set(x_4, 1, x_1900);
lean_ctor_set(x_4, 0, x_1899);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1833);
lean_ctor_set(x_234, 3, x_1265);
lean_ctor_set(x_234, 2, x_1894);
lean_ctor_set(x_234, 1, x_1893);
lean_ctor_set(x_234, 0, x_4);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean_ctor_set(x_1, 3, x_1891);
lean_ctor_set(x_1, 2, x_1904);
lean_ctor_set(x_1, 1, x_1903);
lean_ctor_set(x_1, 0, x_1891);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_1907 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1907, 0, x_234);
lean_ctor_set(x_1907, 1, x_2);
lean_ctor_set(x_1907, 2, x_3);
lean_ctor_set(x_1907, 3, x_1);
lean_ctor_set_uint8(x_1907, sizeof(void*)*4, x_1833);
return x_1907;
}
else
{
lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; 
x_1908 = lean_ctor_get(x_234, 0);
x_1909 = lean_ctor_get(x_234, 1);
x_1910 = lean_ctor_get(x_234, 2);
x_1911 = lean_ctor_get(x_234, 3);
x_1912 = lean_ctor_get(x_4, 1);
x_1913 = lean_ctor_get(x_4, 2);
lean_inc(x_1913);
lean_inc(x_1912);
lean_dec(x_4);
x_1914 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1914, 0, x_1908);
lean_ctor_set(x_1914, 1, x_1909);
lean_ctor_set(x_1914, 2, x_1910);
lean_ctor_set(x_1914, 3, x_1911);
lean_ctor_set_uint8(x_1914, sizeof(void*)*4, x_1833);
lean_ctor_set(x_234, 3, x_1265);
lean_ctor_set(x_234, 2, x_1894);
lean_ctor_set(x_234, 1, x_1893);
lean_ctor_set(x_234, 0, x_1914);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean_ctor_set(x_1, 3, x_1891);
lean_ctor_set(x_1, 2, x_1913);
lean_ctor_set(x_1, 1, x_1912);
lean_ctor_set(x_1, 0, x_1891);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_1915 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1915, 0, x_234);
lean_ctor_set(x_1915, 1, x_2);
lean_ctor_set(x_1915, 2, x_3);
lean_ctor_set(x_1915, 3, x_1);
lean_ctor_set_uint8(x_1915, sizeof(void*)*4, x_1833);
return x_1915;
}
}
else
{
lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; 
x_1916 = lean_ctor_get(x_234, 0);
x_1917 = lean_ctor_get(x_234, 1);
x_1918 = lean_ctor_get(x_234, 2);
x_1919 = lean_ctor_get(x_234, 3);
lean_inc(x_1919);
lean_inc(x_1918);
lean_inc(x_1917);
lean_inc(x_1916);
lean_dec(x_234);
x_1920 = lean_ctor_get(x_4, 1);
lean_inc(x_1920);
x_1921 = lean_ctor_get(x_4, 2);
lean_inc(x_1921);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1922 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1922 = lean_box(0);
}
if (lean_is_scalar(x_1922)) {
 x_1923 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1923 = x_1922;
}
lean_ctor_set(x_1923, 0, x_1916);
lean_ctor_set(x_1923, 1, x_1917);
lean_ctor_set(x_1923, 2, x_1918);
lean_ctor_set(x_1923, 3, x_1919);
lean_ctor_set_uint8(x_1923, sizeof(void*)*4, x_1833);
x_1924 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1924, 0, x_1923);
lean_ctor_set(x_1924, 1, x_1893);
lean_ctor_set(x_1924, 2, x_1894);
lean_ctor_set(x_1924, 3, x_1265);
lean_ctor_set_uint8(x_1924, sizeof(void*)*4, x_1889);
lean_ctor_set(x_1, 3, x_1891);
lean_ctor_set(x_1, 2, x_1921);
lean_ctor_set(x_1, 1, x_1920);
lean_ctor_set(x_1, 0, x_1891);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_1925 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1925, 0, x_1924);
lean_ctor_set(x_1925, 1, x_2);
lean_ctor_set(x_1925, 2, x_3);
lean_ctor_set(x_1925, 3, x_1);
lean_ctor_set_uint8(x_1925, sizeof(void*)*4, x_1833);
return x_1925;
}
}
else
{
lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; 
x_1926 = lean_ctor_get(x_1, 1);
x_1927 = lean_ctor_get(x_1, 2);
lean_inc(x_1927);
lean_inc(x_1926);
lean_dec(x_1);
x_1928 = lean_ctor_get(x_234, 0);
lean_inc(x_1928);
x_1929 = lean_ctor_get(x_234, 1);
lean_inc(x_1929);
x_1930 = lean_ctor_get(x_234, 2);
lean_inc(x_1930);
x_1931 = lean_ctor_get(x_234, 3);
lean_inc(x_1931);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_1932 = x_234;
} else {
 lean_dec_ref(x_234);
 x_1932 = lean_box(0);
}
x_1933 = lean_ctor_get(x_4, 1);
lean_inc(x_1933);
x_1934 = lean_ctor_get(x_4, 2);
lean_inc(x_1934);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1935 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1935 = lean_box(0);
}
if (lean_is_scalar(x_1935)) {
 x_1936 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1936 = x_1935;
}
lean_ctor_set(x_1936, 0, x_1928);
lean_ctor_set(x_1936, 1, x_1929);
lean_ctor_set(x_1936, 2, x_1930);
lean_ctor_set(x_1936, 3, x_1931);
lean_ctor_set_uint8(x_1936, sizeof(void*)*4, x_1833);
if (lean_is_scalar(x_1932)) {
 x_1937 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1937 = x_1932;
}
lean_ctor_set(x_1937, 0, x_1936);
lean_ctor_set(x_1937, 1, x_1926);
lean_ctor_set(x_1937, 2, x_1927);
lean_ctor_set(x_1937, 3, x_1265);
lean_ctor_set_uint8(x_1937, sizeof(void*)*4, x_1889);
x_1938 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1938, 0, x_1891);
lean_ctor_set(x_1938, 1, x_1933);
lean_ctor_set(x_1938, 2, x_1934);
lean_ctor_set(x_1938, 3, x_1891);
lean_ctor_set_uint8(x_1938, sizeof(void*)*4, x_1889);
x_1939 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1939, 0, x_1937);
lean_ctor_set(x_1939, 1, x_2);
lean_ctor_set(x_1939, 2, x_3);
lean_ctor_set(x_1939, 3, x_1938);
lean_ctor_set_uint8(x_1939, sizeof(void*)*4, x_1833);
return x_1939;
}
}
else
{
uint8_t x_1940; 
x_1940 = lean_ctor_get_uint8(x_1891, sizeof(void*)*4);
if (x_1940 == 0)
{
uint8_t x_1941; 
x_1941 = !lean_is_exclusive(x_1);
if (x_1941 == 0)
{
lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; uint8_t x_1946; 
x_1942 = lean_ctor_get(x_1, 1);
x_1943 = lean_ctor_get(x_1, 2);
x_1944 = lean_ctor_get(x_1, 3);
lean_dec(x_1944);
x_1945 = lean_ctor_get(x_1, 0);
lean_dec(x_1945);
x_1946 = !lean_is_exclusive(x_234);
if (x_1946 == 0)
{
uint8_t x_1947; 
x_1947 = !lean_is_exclusive(x_4);
if (x_1947 == 0)
{
lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; uint8_t x_1956; 
x_1948 = lean_ctor_get(x_234, 0);
x_1949 = lean_ctor_get(x_234, 1);
x_1950 = lean_ctor_get(x_234, 2);
x_1951 = lean_ctor_get(x_234, 3);
x_1952 = lean_ctor_get(x_4, 1);
x_1953 = lean_ctor_get(x_4, 2);
x_1954 = lean_ctor_get(x_4, 3);
lean_dec(x_1954);
x_1955 = lean_ctor_get(x_4, 0);
lean_dec(x_1955);
x_1956 = !lean_is_exclusive(x_1891);
if (x_1956 == 0)
{
lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; uint8_t x_1961; 
x_1957 = lean_ctor_get(x_1891, 0);
x_1958 = lean_ctor_get(x_1891, 1);
x_1959 = lean_ctor_get(x_1891, 2);
x_1960 = lean_ctor_get(x_1891, 3);
lean_ctor_set(x_1891, 3, x_1951);
lean_ctor_set(x_1891, 2, x_1950);
lean_ctor_set(x_1891, 1, x_1949);
lean_ctor_set(x_1891, 0, x_1948);
lean_ctor_set_uint8(x_1891, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
lean_ctor_set(x_4, 3, x_1265);
lean_ctor_set(x_4, 2, x_1943);
lean_ctor_set(x_4, 1, x_1942);
lean_ctor_set(x_4, 0, x_1891);
x_1961 = !lean_is_exclusive(x_1265);
if (x_1961 == 0)
{
lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; 
x_1962 = lean_ctor_get(x_1265, 3);
lean_dec(x_1962);
x_1963 = lean_ctor_get(x_1265, 2);
lean_dec(x_1963);
x_1964 = lean_ctor_get(x_1265, 1);
lean_dec(x_1964);
x_1965 = lean_ctor_get(x_1265, 0);
lean_dec(x_1965);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1940);
lean_ctor_set(x_1265, 3, x_1890);
lean_ctor_set(x_1265, 2, x_3);
lean_ctor_set(x_1265, 1, x_2);
lean_ctor_set(x_1265, 0, x_4);
lean_ctor_set(x_234, 3, x_1960);
lean_ctor_set(x_234, 2, x_1959);
lean_ctor_set(x_234, 1, x_1958);
lean_ctor_set(x_234, 0, x_1957);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_1953);
lean_ctor_set(x_1, 1, x_1952);
lean_ctor_set(x_1, 0, x_1265);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
else
{
lean_object* x_1966; 
lean_dec(x_1265);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1940);
x_1966 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1966, 0, x_4);
lean_ctor_set(x_1966, 1, x_2);
lean_ctor_set(x_1966, 2, x_3);
lean_ctor_set(x_1966, 3, x_1890);
lean_ctor_set_uint8(x_1966, sizeof(void*)*4, x_1833);
lean_ctor_set(x_234, 3, x_1960);
lean_ctor_set(x_234, 2, x_1959);
lean_ctor_set(x_234, 1, x_1958);
lean_ctor_set(x_234, 0, x_1957);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_1953);
lean_ctor_set(x_1, 1, x_1952);
lean_ctor_set(x_1, 0, x_1966);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
}
else
{
lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; 
x_1967 = lean_ctor_get(x_1891, 0);
x_1968 = lean_ctor_get(x_1891, 1);
x_1969 = lean_ctor_get(x_1891, 2);
x_1970 = lean_ctor_get(x_1891, 3);
lean_inc(x_1970);
lean_inc(x_1969);
lean_inc(x_1968);
lean_inc(x_1967);
lean_dec(x_1891);
x_1971 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1971, 0, x_1948);
lean_ctor_set(x_1971, 1, x_1949);
lean_ctor_set(x_1971, 2, x_1950);
lean_ctor_set(x_1971, 3, x_1951);
lean_ctor_set_uint8(x_1971, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
lean_ctor_set(x_4, 3, x_1265);
lean_ctor_set(x_4, 2, x_1943);
lean_ctor_set(x_4, 1, x_1942);
lean_ctor_set(x_4, 0, x_1971);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_1972 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_1972 = lean_box(0);
}
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_1940);
if (lean_is_scalar(x_1972)) {
 x_1973 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1973 = x_1972;
}
lean_ctor_set(x_1973, 0, x_4);
lean_ctor_set(x_1973, 1, x_2);
lean_ctor_set(x_1973, 2, x_3);
lean_ctor_set(x_1973, 3, x_1890);
lean_ctor_set_uint8(x_1973, sizeof(void*)*4, x_1833);
lean_ctor_set(x_234, 3, x_1970);
lean_ctor_set(x_234, 2, x_1969);
lean_ctor_set(x_234, 1, x_1968);
lean_ctor_set(x_234, 0, x_1967);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_1953);
lean_ctor_set(x_1, 1, x_1952);
lean_ctor_set(x_1, 0, x_1973);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
}
else
{
lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; 
x_1974 = lean_ctor_get(x_234, 0);
x_1975 = lean_ctor_get(x_234, 1);
x_1976 = lean_ctor_get(x_234, 2);
x_1977 = lean_ctor_get(x_234, 3);
x_1978 = lean_ctor_get(x_4, 1);
x_1979 = lean_ctor_get(x_4, 2);
lean_inc(x_1979);
lean_inc(x_1978);
lean_dec(x_4);
x_1980 = lean_ctor_get(x_1891, 0);
lean_inc(x_1980);
x_1981 = lean_ctor_get(x_1891, 1);
lean_inc(x_1981);
x_1982 = lean_ctor_get(x_1891, 2);
lean_inc(x_1982);
x_1983 = lean_ctor_get(x_1891, 3);
lean_inc(x_1983);
if (lean_is_exclusive(x_1891)) {
 lean_ctor_release(x_1891, 0);
 lean_ctor_release(x_1891, 1);
 lean_ctor_release(x_1891, 2);
 lean_ctor_release(x_1891, 3);
 x_1984 = x_1891;
} else {
 lean_dec_ref(x_1891);
 x_1984 = lean_box(0);
}
if (lean_is_scalar(x_1984)) {
 x_1985 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1985 = x_1984;
}
lean_ctor_set(x_1985, 0, x_1974);
lean_ctor_set(x_1985, 1, x_1975);
lean_ctor_set(x_1985, 2, x_1976);
lean_ctor_set(x_1985, 3, x_1977);
lean_ctor_set_uint8(x_1985, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
x_1986 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_1986, 0, x_1985);
lean_ctor_set(x_1986, 1, x_1942);
lean_ctor_set(x_1986, 2, x_1943);
lean_ctor_set(x_1986, 3, x_1265);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_1987 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_1987 = lean_box(0);
}
lean_ctor_set_uint8(x_1986, sizeof(void*)*4, x_1940);
if (lean_is_scalar(x_1987)) {
 x_1988 = lean_alloc_ctor(1, 4, 1);
} else {
 x_1988 = x_1987;
}
lean_ctor_set(x_1988, 0, x_1986);
lean_ctor_set(x_1988, 1, x_2);
lean_ctor_set(x_1988, 2, x_3);
lean_ctor_set(x_1988, 3, x_1890);
lean_ctor_set_uint8(x_1988, sizeof(void*)*4, x_1833);
lean_ctor_set(x_234, 3, x_1983);
lean_ctor_set(x_234, 2, x_1982);
lean_ctor_set(x_234, 1, x_1981);
lean_ctor_set(x_234, 0, x_1980);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_1979);
lean_ctor_set(x_1, 1, x_1978);
lean_ctor_set(x_1, 0, x_1988);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
}
else
{
lean_object* x_1989; lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; 
x_1989 = lean_ctor_get(x_234, 0);
x_1990 = lean_ctor_get(x_234, 1);
x_1991 = lean_ctor_get(x_234, 2);
x_1992 = lean_ctor_get(x_234, 3);
lean_inc(x_1992);
lean_inc(x_1991);
lean_inc(x_1990);
lean_inc(x_1989);
lean_dec(x_234);
x_1993 = lean_ctor_get(x_4, 1);
lean_inc(x_1993);
x_1994 = lean_ctor_get(x_4, 2);
lean_inc(x_1994);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_1995 = x_4;
} else {
 lean_dec_ref(x_4);
 x_1995 = lean_box(0);
}
x_1996 = lean_ctor_get(x_1891, 0);
lean_inc(x_1996);
x_1997 = lean_ctor_get(x_1891, 1);
lean_inc(x_1997);
x_1998 = lean_ctor_get(x_1891, 2);
lean_inc(x_1998);
x_1999 = lean_ctor_get(x_1891, 3);
lean_inc(x_1999);
if (lean_is_exclusive(x_1891)) {
 lean_ctor_release(x_1891, 0);
 lean_ctor_release(x_1891, 1);
 lean_ctor_release(x_1891, 2);
 lean_ctor_release(x_1891, 3);
 x_2000 = x_1891;
} else {
 lean_dec_ref(x_1891);
 x_2000 = lean_box(0);
}
if (lean_is_scalar(x_2000)) {
 x_2001 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2001 = x_2000;
}
lean_ctor_set(x_2001, 0, x_1989);
lean_ctor_set(x_2001, 1, x_1990);
lean_ctor_set(x_2001, 2, x_1991);
lean_ctor_set(x_2001, 3, x_1992);
lean_ctor_set_uint8(x_2001, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
if (lean_is_scalar(x_1995)) {
 x_2002 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2002 = x_1995;
}
lean_ctor_set(x_2002, 0, x_2001);
lean_ctor_set(x_2002, 1, x_1942);
lean_ctor_set(x_2002, 2, x_1943);
lean_ctor_set(x_2002, 3, x_1265);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2003 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2003 = lean_box(0);
}
lean_ctor_set_uint8(x_2002, sizeof(void*)*4, x_1940);
if (lean_is_scalar(x_2003)) {
 x_2004 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2004 = x_2003;
}
lean_ctor_set(x_2004, 0, x_2002);
lean_ctor_set(x_2004, 1, x_2);
lean_ctor_set(x_2004, 2, x_3);
lean_ctor_set(x_2004, 3, x_1890);
lean_ctor_set_uint8(x_2004, sizeof(void*)*4, x_1833);
x_2005 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2005, 0, x_1996);
lean_ctor_set(x_2005, 1, x_1997);
lean_ctor_set(x_2005, 2, x_1998);
lean_ctor_set(x_2005, 3, x_1999);
lean_ctor_set_uint8(x_2005, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_2005);
lean_ctor_set(x_1, 2, x_1994);
lean_ctor_set(x_1, 1, x_1993);
lean_ctor_set(x_1, 0, x_2004);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
}
else
{
lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; lean_object* x_2011; lean_object* x_2012; lean_object* x_2013; lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; lean_object* x_2017; lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; 
x_2006 = lean_ctor_get(x_1, 1);
x_2007 = lean_ctor_get(x_1, 2);
lean_inc(x_2007);
lean_inc(x_2006);
lean_dec(x_1);
x_2008 = lean_ctor_get(x_234, 0);
lean_inc(x_2008);
x_2009 = lean_ctor_get(x_234, 1);
lean_inc(x_2009);
x_2010 = lean_ctor_get(x_234, 2);
lean_inc(x_2010);
x_2011 = lean_ctor_get(x_234, 3);
lean_inc(x_2011);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_2012 = x_234;
} else {
 lean_dec_ref(x_234);
 x_2012 = lean_box(0);
}
x_2013 = lean_ctor_get(x_4, 1);
lean_inc(x_2013);
x_2014 = lean_ctor_get(x_4, 2);
lean_inc(x_2014);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_2015 = x_4;
} else {
 lean_dec_ref(x_4);
 x_2015 = lean_box(0);
}
x_2016 = lean_ctor_get(x_1891, 0);
lean_inc(x_2016);
x_2017 = lean_ctor_get(x_1891, 1);
lean_inc(x_2017);
x_2018 = lean_ctor_get(x_1891, 2);
lean_inc(x_2018);
x_2019 = lean_ctor_get(x_1891, 3);
lean_inc(x_2019);
if (lean_is_exclusive(x_1891)) {
 lean_ctor_release(x_1891, 0);
 lean_ctor_release(x_1891, 1);
 lean_ctor_release(x_1891, 2);
 lean_ctor_release(x_1891, 3);
 x_2020 = x_1891;
} else {
 lean_dec_ref(x_1891);
 x_2020 = lean_box(0);
}
if (lean_is_scalar(x_2020)) {
 x_2021 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2021 = x_2020;
}
lean_ctor_set(x_2021, 0, x_2008);
lean_ctor_set(x_2021, 1, x_2009);
lean_ctor_set(x_2021, 2, x_2010);
lean_ctor_set(x_2021, 3, x_2011);
lean_ctor_set_uint8(x_2021, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
if (lean_is_scalar(x_2015)) {
 x_2022 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2022 = x_2015;
}
lean_ctor_set(x_2022, 0, x_2021);
lean_ctor_set(x_2022, 1, x_2006);
lean_ctor_set(x_2022, 2, x_2007);
lean_ctor_set(x_2022, 3, x_1265);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2023 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2023 = lean_box(0);
}
lean_ctor_set_uint8(x_2022, sizeof(void*)*4, x_1940);
if (lean_is_scalar(x_2023)) {
 x_2024 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2024 = x_2023;
}
lean_ctor_set(x_2024, 0, x_2022);
lean_ctor_set(x_2024, 1, x_2);
lean_ctor_set(x_2024, 2, x_3);
lean_ctor_set(x_2024, 3, x_1890);
lean_ctor_set_uint8(x_2024, sizeof(void*)*4, x_1833);
if (lean_is_scalar(x_2012)) {
 x_2025 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2025 = x_2012;
}
lean_ctor_set(x_2025, 0, x_2016);
lean_ctor_set(x_2025, 1, x_2017);
lean_ctor_set(x_2025, 2, x_2018);
lean_ctor_set(x_2025, 3, x_2019);
lean_ctor_set_uint8(x_2025, sizeof(void*)*4, x_1833);
x_2026 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2026, 0, x_2024);
lean_ctor_set(x_2026, 1, x_2013);
lean_ctor_set(x_2026, 2, x_2014);
lean_ctor_set(x_2026, 3, x_2025);
lean_ctor_set_uint8(x_2026, sizeof(void*)*4, x_1940);
return x_2026;
}
}
else
{
uint8_t x_2027; 
x_2027 = !lean_is_exclusive(x_1891);
if (x_2027 == 0)
{
lean_object* x_2028; lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; uint8_t x_2032; 
x_2028 = lean_ctor_get(x_1891, 3);
lean_dec(x_2028);
x_2029 = lean_ctor_get(x_1891, 2);
lean_dec(x_2029);
x_2030 = lean_ctor_get(x_1891, 1);
lean_dec(x_2030);
x_2031 = lean_ctor_get(x_1891, 0);
lean_dec(x_2031);
x_2032 = !lean_is_exclusive(x_1);
if (x_2032 == 0)
{
lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; uint8_t x_2037; 
x_2033 = lean_ctor_get(x_1, 1);
x_2034 = lean_ctor_get(x_1, 2);
x_2035 = lean_ctor_get(x_1, 3);
lean_dec(x_2035);
x_2036 = lean_ctor_get(x_1, 0);
lean_dec(x_2036);
x_2037 = !lean_is_exclusive(x_234);
if (x_2037 == 0)
{
uint8_t x_2038; 
x_2038 = !lean_is_exclusive(x_1265);
if (x_2038 == 0)
{
lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; lean_object* x_2042; 
x_2039 = lean_ctor_get(x_234, 0);
x_2040 = lean_ctor_get(x_234, 1);
x_2041 = lean_ctor_get(x_234, 2);
x_2042 = lean_ctor_get(x_234, 3);
lean_ctor_set(x_1891, 3, x_2042);
lean_ctor_set(x_1891, 2, x_2041);
lean_ctor_set(x_1891, 1, x_2040);
lean_ctor_set(x_1891, 0, x_2039);
lean_ctor_set_uint8(x_1265, sizeof(void*)*4, x_1940);
lean_ctor_set(x_234, 3, x_1265);
lean_ctor_set(x_234, 2, x_2034);
lean_ctor_set(x_234, 1, x_2033);
lean_ctor_set(x_234, 0, x_1891);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
else
{
lean_object* x_2043; lean_object* x_2044; lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; 
x_2043 = lean_ctor_get(x_234, 0);
x_2044 = lean_ctor_get(x_234, 1);
x_2045 = lean_ctor_get(x_234, 2);
x_2046 = lean_ctor_get(x_234, 3);
x_2047 = lean_ctor_get(x_1265, 0);
x_2048 = lean_ctor_get(x_1265, 1);
x_2049 = lean_ctor_get(x_1265, 2);
x_2050 = lean_ctor_get(x_1265, 3);
lean_inc(x_2050);
lean_inc(x_2049);
lean_inc(x_2048);
lean_inc(x_2047);
lean_dec(x_1265);
lean_ctor_set(x_1891, 3, x_2046);
lean_ctor_set(x_1891, 2, x_2045);
lean_ctor_set(x_1891, 1, x_2044);
lean_ctor_set(x_1891, 0, x_2043);
x_2051 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2051, 0, x_2047);
lean_ctor_set(x_2051, 1, x_2048);
lean_ctor_set(x_2051, 2, x_2049);
lean_ctor_set(x_2051, 3, x_2050);
lean_ctor_set_uint8(x_2051, sizeof(void*)*4, x_1940);
lean_ctor_set(x_234, 3, x_2051);
lean_ctor_set(x_234, 2, x_2034);
lean_ctor_set(x_234, 1, x_2033);
lean_ctor_set(x_234, 0, x_1891);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
}
else
{
lean_object* x_2052; lean_object* x_2053; lean_object* x_2054; lean_object* x_2055; lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; 
x_2052 = lean_ctor_get(x_234, 0);
x_2053 = lean_ctor_get(x_234, 1);
x_2054 = lean_ctor_get(x_234, 2);
x_2055 = lean_ctor_get(x_234, 3);
lean_inc(x_2055);
lean_inc(x_2054);
lean_inc(x_2053);
lean_inc(x_2052);
lean_dec(x_234);
x_2056 = lean_ctor_get(x_1265, 0);
lean_inc(x_2056);
x_2057 = lean_ctor_get(x_1265, 1);
lean_inc(x_2057);
x_2058 = lean_ctor_get(x_1265, 2);
lean_inc(x_2058);
x_2059 = lean_ctor_get(x_1265, 3);
lean_inc(x_2059);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2060 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2060 = lean_box(0);
}
lean_ctor_set(x_1891, 3, x_2055);
lean_ctor_set(x_1891, 2, x_2054);
lean_ctor_set(x_1891, 1, x_2053);
lean_ctor_set(x_1891, 0, x_2052);
if (lean_is_scalar(x_2060)) {
 x_2061 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2061 = x_2060;
}
lean_ctor_set(x_2061, 0, x_2056);
lean_ctor_set(x_2061, 1, x_2057);
lean_ctor_set(x_2061, 2, x_2058);
lean_ctor_set(x_2061, 3, x_2059);
lean_ctor_set_uint8(x_2061, sizeof(void*)*4, x_1940);
x_2062 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2062, 0, x_1891);
lean_ctor_set(x_2062, 1, x_2033);
lean_ctor_set(x_2062, 2, x_2034);
lean_ctor_set(x_2062, 3, x_2061);
lean_ctor_set_uint8(x_2062, sizeof(void*)*4, x_1889);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_2062);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1940);
return x_1;
}
}
else
{
lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; 
x_2063 = lean_ctor_get(x_1, 1);
x_2064 = lean_ctor_get(x_1, 2);
lean_inc(x_2064);
lean_inc(x_2063);
lean_dec(x_1);
x_2065 = lean_ctor_get(x_234, 0);
lean_inc(x_2065);
x_2066 = lean_ctor_get(x_234, 1);
lean_inc(x_2066);
x_2067 = lean_ctor_get(x_234, 2);
lean_inc(x_2067);
x_2068 = lean_ctor_get(x_234, 3);
lean_inc(x_2068);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_2069 = x_234;
} else {
 lean_dec_ref(x_234);
 x_2069 = lean_box(0);
}
x_2070 = lean_ctor_get(x_1265, 0);
lean_inc(x_2070);
x_2071 = lean_ctor_get(x_1265, 1);
lean_inc(x_2071);
x_2072 = lean_ctor_get(x_1265, 2);
lean_inc(x_2072);
x_2073 = lean_ctor_get(x_1265, 3);
lean_inc(x_2073);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2074 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2074 = lean_box(0);
}
lean_ctor_set(x_1891, 3, x_2068);
lean_ctor_set(x_1891, 2, x_2067);
lean_ctor_set(x_1891, 1, x_2066);
lean_ctor_set(x_1891, 0, x_2065);
if (lean_is_scalar(x_2074)) {
 x_2075 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2075 = x_2074;
}
lean_ctor_set(x_2075, 0, x_2070);
lean_ctor_set(x_2075, 1, x_2071);
lean_ctor_set(x_2075, 2, x_2072);
lean_ctor_set(x_2075, 3, x_2073);
lean_ctor_set_uint8(x_2075, sizeof(void*)*4, x_1940);
if (lean_is_scalar(x_2069)) {
 x_2076 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2076 = x_2069;
}
lean_ctor_set(x_2076, 0, x_1891);
lean_ctor_set(x_2076, 1, x_2063);
lean_ctor_set(x_2076, 2, x_2064);
lean_ctor_set(x_2076, 3, x_2075);
lean_ctor_set_uint8(x_2076, sizeof(void*)*4, x_1889);
x_2077 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2077, 0, x_2076);
lean_ctor_set(x_2077, 1, x_2);
lean_ctor_set(x_2077, 2, x_3);
lean_ctor_set(x_2077, 3, x_4);
lean_ctor_set_uint8(x_2077, sizeof(void*)*4, x_1940);
return x_2077;
}
}
else
{
lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; 
lean_dec(x_1891);
x_2078 = lean_ctor_get(x_1, 1);
lean_inc(x_2078);
x_2079 = lean_ctor_get(x_1, 2);
lean_inc(x_2079);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_2080 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2080 = lean_box(0);
}
x_2081 = lean_ctor_get(x_234, 0);
lean_inc(x_2081);
x_2082 = lean_ctor_get(x_234, 1);
lean_inc(x_2082);
x_2083 = lean_ctor_get(x_234, 2);
lean_inc(x_2083);
x_2084 = lean_ctor_get(x_234, 3);
lean_inc(x_2084);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_2085 = x_234;
} else {
 lean_dec_ref(x_234);
 x_2085 = lean_box(0);
}
x_2086 = lean_ctor_get(x_1265, 0);
lean_inc(x_2086);
x_2087 = lean_ctor_get(x_1265, 1);
lean_inc(x_2087);
x_2088 = lean_ctor_get(x_1265, 2);
lean_inc(x_2088);
x_2089 = lean_ctor_get(x_1265, 3);
lean_inc(x_2089);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2090 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2090 = lean_box(0);
}
x_2091 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2091, 0, x_2081);
lean_ctor_set(x_2091, 1, x_2082);
lean_ctor_set(x_2091, 2, x_2083);
lean_ctor_set(x_2091, 3, x_2084);
lean_ctor_set_uint8(x_2091, sizeof(void*)*4, x_1940);
if (lean_is_scalar(x_2090)) {
 x_2092 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2092 = x_2090;
}
lean_ctor_set(x_2092, 0, x_2086);
lean_ctor_set(x_2092, 1, x_2087);
lean_ctor_set(x_2092, 2, x_2088);
lean_ctor_set(x_2092, 3, x_2089);
lean_ctor_set_uint8(x_2092, sizeof(void*)*4, x_1940);
if (lean_is_scalar(x_2085)) {
 x_2093 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2093 = x_2085;
}
lean_ctor_set(x_2093, 0, x_2091);
lean_ctor_set(x_2093, 1, x_2078);
lean_ctor_set(x_2093, 2, x_2079);
lean_ctor_set(x_2093, 3, x_2092);
lean_ctor_set_uint8(x_2093, sizeof(void*)*4, x_1889);
if (lean_is_scalar(x_2080)) {
 x_2094 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2094 = x_2080;
}
lean_ctor_set(x_2094, 0, x_2093);
lean_ctor_set(x_2094, 1, x_2);
lean_ctor_set(x_2094, 2, x_3);
lean_ctor_set(x_2094, 3, x_4);
lean_ctor_set_uint8(x_2094, sizeof(void*)*4, x_1940);
return x_2094;
}
}
}
}
else
{
uint8_t x_2095; 
x_2095 = lean_ctor_get_uint8(x_1890, sizeof(void*)*4);
if (x_2095 == 0)
{
lean_object* x_2096; 
x_2096 = lean_ctor_get(x_4, 3);
lean_inc(x_2096);
if (lean_obj_tag(x_2096) == 0)
{
uint8_t x_2097; 
x_2097 = !lean_is_exclusive(x_1);
if (x_2097 == 0)
{
lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; uint8_t x_2102; 
x_2098 = lean_ctor_get(x_1, 1);
x_2099 = lean_ctor_get(x_1, 2);
x_2100 = lean_ctor_get(x_1, 3);
lean_dec(x_2100);
x_2101 = lean_ctor_get(x_1, 0);
lean_dec(x_2101);
x_2102 = !lean_is_exclusive(x_234);
if (x_2102 == 0)
{
uint8_t x_2103; 
x_2103 = !lean_is_exclusive(x_4);
if (x_2103 == 0)
{
lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; uint8_t x_2112; 
x_2104 = lean_ctor_get(x_234, 0);
x_2105 = lean_ctor_get(x_234, 1);
x_2106 = lean_ctor_get(x_234, 2);
x_2107 = lean_ctor_get(x_234, 3);
x_2108 = lean_ctor_get(x_4, 1);
x_2109 = lean_ctor_get(x_4, 2);
x_2110 = lean_ctor_get(x_4, 3);
lean_dec(x_2110);
x_2111 = lean_ctor_get(x_4, 0);
lean_dec(x_2111);
x_2112 = !lean_is_exclusive(x_1890);
if (x_2112 == 0)
{
lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; lean_object* x_2116; uint8_t x_2117; 
x_2113 = lean_ctor_get(x_1890, 0);
x_2114 = lean_ctor_get(x_1890, 1);
x_2115 = lean_ctor_get(x_1890, 2);
x_2116 = lean_ctor_get(x_1890, 3);
lean_ctor_set(x_1890, 3, x_2107);
lean_ctor_set(x_1890, 2, x_2106);
lean_ctor_set(x_1890, 1, x_2105);
lean_ctor_set(x_1890, 0, x_2104);
lean_ctor_set_uint8(x_1890, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
lean_ctor_set(x_4, 3, x_1265);
lean_ctor_set(x_4, 2, x_2099);
lean_ctor_set(x_4, 1, x_2098);
x_2117 = !lean_is_exclusive(x_1265);
if (x_2117 == 0)
{
lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; 
x_2118 = lean_ctor_get(x_1265, 3);
lean_dec(x_2118);
x_2119 = lean_ctor_get(x_1265, 2);
lean_dec(x_2119);
x_2120 = lean_ctor_get(x_1265, 1);
lean_dec(x_2120);
x_2121 = lean_ctor_get(x_1265, 0);
lean_dec(x_2121);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2095);
lean_ctor_set(x_1265, 3, x_2113);
lean_ctor_set(x_1265, 2, x_3);
lean_ctor_set(x_1265, 1, x_2);
lean_ctor_set(x_1265, 0, x_4);
lean_ctor_set(x_234, 3, x_2096);
lean_ctor_set(x_234, 2, x_2109);
lean_ctor_set(x_234, 1, x_2108);
lean_ctor_set(x_234, 0, x_2116);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_2115);
lean_ctor_set(x_1, 1, x_2114);
lean_ctor_set(x_1, 0, x_1265);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
else
{
lean_object* x_2122; 
lean_dec(x_1265);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2095);
x_2122 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2122, 0, x_4);
lean_ctor_set(x_2122, 1, x_2);
lean_ctor_set(x_2122, 2, x_3);
lean_ctor_set(x_2122, 3, x_2113);
lean_ctor_set_uint8(x_2122, sizeof(void*)*4, x_1833);
lean_ctor_set(x_234, 3, x_2096);
lean_ctor_set(x_234, 2, x_2109);
lean_ctor_set(x_234, 1, x_2108);
lean_ctor_set(x_234, 0, x_2116);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_2115);
lean_ctor_set(x_1, 1, x_2114);
lean_ctor_set(x_1, 0, x_2122);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
}
else
{
lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; 
x_2123 = lean_ctor_get(x_1890, 0);
x_2124 = lean_ctor_get(x_1890, 1);
x_2125 = lean_ctor_get(x_1890, 2);
x_2126 = lean_ctor_get(x_1890, 3);
lean_inc(x_2126);
lean_inc(x_2125);
lean_inc(x_2124);
lean_inc(x_2123);
lean_dec(x_1890);
x_2127 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2127, 0, x_2104);
lean_ctor_set(x_2127, 1, x_2105);
lean_ctor_set(x_2127, 2, x_2106);
lean_ctor_set(x_2127, 3, x_2107);
lean_ctor_set_uint8(x_2127, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
lean_ctor_set(x_4, 3, x_1265);
lean_ctor_set(x_4, 2, x_2099);
lean_ctor_set(x_4, 1, x_2098);
lean_ctor_set(x_4, 0, x_2127);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2128 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2128 = lean_box(0);
}
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2095);
if (lean_is_scalar(x_2128)) {
 x_2129 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2129 = x_2128;
}
lean_ctor_set(x_2129, 0, x_4);
lean_ctor_set(x_2129, 1, x_2);
lean_ctor_set(x_2129, 2, x_3);
lean_ctor_set(x_2129, 3, x_2123);
lean_ctor_set_uint8(x_2129, sizeof(void*)*4, x_1833);
lean_ctor_set(x_234, 3, x_2096);
lean_ctor_set(x_234, 2, x_2109);
lean_ctor_set(x_234, 1, x_2108);
lean_ctor_set(x_234, 0, x_2126);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_2125);
lean_ctor_set(x_1, 1, x_2124);
lean_ctor_set(x_1, 0, x_2129);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
}
else
{
lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; lean_object* x_2133; lean_object* x_2134; lean_object* x_2135; lean_object* x_2136; lean_object* x_2137; lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; 
x_2130 = lean_ctor_get(x_234, 0);
x_2131 = lean_ctor_get(x_234, 1);
x_2132 = lean_ctor_get(x_234, 2);
x_2133 = lean_ctor_get(x_234, 3);
x_2134 = lean_ctor_get(x_4, 1);
x_2135 = lean_ctor_get(x_4, 2);
lean_inc(x_2135);
lean_inc(x_2134);
lean_dec(x_4);
x_2136 = lean_ctor_get(x_1890, 0);
lean_inc(x_2136);
x_2137 = lean_ctor_get(x_1890, 1);
lean_inc(x_2137);
x_2138 = lean_ctor_get(x_1890, 2);
lean_inc(x_2138);
x_2139 = lean_ctor_get(x_1890, 3);
lean_inc(x_2139);
if (lean_is_exclusive(x_1890)) {
 lean_ctor_release(x_1890, 0);
 lean_ctor_release(x_1890, 1);
 lean_ctor_release(x_1890, 2);
 lean_ctor_release(x_1890, 3);
 x_2140 = x_1890;
} else {
 lean_dec_ref(x_1890);
 x_2140 = lean_box(0);
}
if (lean_is_scalar(x_2140)) {
 x_2141 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2141 = x_2140;
}
lean_ctor_set(x_2141, 0, x_2130);
lean_ctor_set(x_2141, 1, x_2131);
lean_ctor_set(x_2141, 2, x_2132);
lean_ctor_set(x_2141, 3, x_2133);
lean_ctor_set_uint8(x_2141, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
x_2142 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2142, 0, x_2141);
lean_ctor_set(x_2142, 1, x_2098);
lean_ctor_set(x_2142, 2, x_2099);
lean_ctor_set(x_2142, 3, x_1265);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2143 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2143 = lean_box(0);
}
lean_ctor_set_uint8(x_2142, sizeof(void*)*4, x_2095);
if (lean_is_scalar(x_2143)) {
 x_2144 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2144 = x_2143;
}
lean_ctor_set(x_2144, 0, x_2142);
lean_ctor_set(x_2144, 1, x_2);
lean_ctor_set(x_2144, 2, x_3);
lean_ctor_set(x_2144, 3, x_2136);
lean_ctor_set_uint8(x_2144, sizeof(void*)*4, x_1833);
lean_ctor_set(x_234, 3, x_2096);
lean_ctor_set(x_234, 2, x_2135);
lean_ctor_set(x_234, 1, x_2134);
lean_ctor_set(x_234, 0, x_2139);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_2138);
lean_ctor_set(x_1, 1, x_2137);
lean_ctor_set(x_1, 0, x_2144);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
}
else
{
lean_object* x_2145; lean_object* x_2146; lean_object* x_2147; lean_object* x_2148; lean_object* x_2149; lean_object* x_2150; lean_object* x_2151; lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; 
x_2145 = lean_ctor_get(x_234, 0);
x_2146 = lean_ctor_get(x_234, 1);
x_2147 = lean_ctor_get(x_234, 2);
x_2148 = lean_ctor_get(x_234, 3);
lean_inc(x_2148);
lean_inc(x_2147);
lean_inc(x_2146);
lean_inc(x_2145);
lean_dec(x_234);
x_2149 = lean_ctor_get(x_4, 1);
lean_inc(x_2149);
x_2150 = lean_ctor_get(x_4, 2);
lean_inc(x_2150);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_2151 = x_4;
} else {
 lean_dec_ref(x_4);
 x_2151 = lean_box(0);
}
x_2152 = lean_ctor_get(x_1890, 0);
lean_inc(x_2152);
x_2153 = lean_ctor_get(x_1890, 1);
lean_inc(x_2153);
x_2154 = lean_ctor_get(x_1890, 2);
lean_inc(x_2154);
x_2155 = lean_ctor_get(x_1890, 3);
lean_inc(x_2155);
if (lean_is_exclusive(x_1890)) {
 lean_ctor_release(x_1890, 0);
 lean_ctor_release(x_1890, 1);
 lean_ctor_release(x_1890, 2);
 lean_ctor_release(x_1890, 3);
 x_2156 = x_1890;
} else {
 lean_dec_ref(x_1890);
 x_2156 = lean_box(0);
}
if (lean_is_scalar(x_2156)) {
 x_2157 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2157 = x_2156;
}
lean_ctor_set(x_2157, 0, x_2145);
lean_ctor_set(x_2157, 1, x_2146);
lean_ctor_set(x_2157, 2, x_2147);
lean_ctor_set(x_2157, 3, x_2148);
lean_ctor_set_uint8(x_2157, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
if (lean_is_scalar(x_2151)) {
 x_2158 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2158 = x_2151;
}
lean_ctor_set(x_2158, 0, x_2157);
lean_ctor_set(x_2158, 1, x_2098);
lean_ctor_set(x_2158, 2, x_2099);
lean_ctor_set(x_2158, 3, x_1265);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2159 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2159 = lean_box(0);
}
lean_ctor_set_uint8(x_2158, sizeof(void*)*4, x_2095);
if (lean_is_scalar(x_2159)) {
 x_2160 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2160 = x_2159;
}
lean_ctor_set(x_2160, 0, x_2158);
lean_ctor_set(x_2160, 1, x_2);
lean_ctor_set(x_2160, 2, x_3);
lean_ctor_set(x_2160, 3, x_2152);
lean_ctor_set_uint8(x_2160, sizeof(void*)*4, x_1833);
x_2161 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2161, 0, x_2155);
lean_ctor_set(x_2161, 1, x_2149);
lean_ctor_set(x_2161, 2, x_2150);
lean_ctor_set(x_2161, 3, x_2096);
lean_ctor_set_uint8(x_2161, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_2161);
lean_ctor_set(x_1, 2, x_2154);
lean_ctor_set(x_1, 1, x_2153);
lean_ctor_set(x_1, 0, x_2160);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
}
else
{
lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; lean_object* x_2178; lean_object* x_2179; lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; 
x_2162 = lean_ctor_get(x_1, 1);
x_2163 = lean_ctor_get(x_1, 2);
lean_inc(x_2163);
lean_inc(x_2162);
lean_dec(x_1);
x_2164 = lean_ctor_get(x_234, 0);
lean_inc(x_2164);
x_2165 = lean_ctor_get(x_234, 1);
lean_inc(x_2165);
x_2166 = lean_ctor_get(x_234, 2);
lean_inc(x_2166);
x_2167 = lean_ctor_get(x_234, 3);
lean_inc(x_2167);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_2168 = x_234;
} else {
 lean_dec_ref(x_234);
 x_2168 = lean_box(0);
}
x_2169 = lean_ctor_get(x_4, 1);
lean_inc(x_2169);
x_2170 = lean_ctor_get(x_4, 2);
lean_inc(x_2170);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_2171 = x_4;
} else {
 lean_dec_ref(x_4);
 x_2171 = lean_box(0);
}
x_2172 = lean_ctor_get(x_1890, 0);
lean_inc(x_2172);
x_2173 = lean_ctor_get(x_1890, 1);
lean_inc(x_2173);
x_2174 = lean_ctor_get(x_1890, 2);
lean_inc(x_2174);
x_2175 = lean_ctor_get(x_1890, 3);
lean_inc(x_2175);
if (lean_is_exclusive(x_1890)) {
 lean_ctor_release(x_1890, 0);
 lean_ctor_release(x_1890, 1);
 lean_ctor_release(x_1890, 2);
 lean_ctor_release(x_1890, 3);
 x_2176 = x_1890;
} else {
 lean_dec_ref(x_1890);
 x_2176 = lean_box(0);
}
if (lean_is_scalar(x_2176)) {
 x_2177 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2177 = x_2176;
}
lean_ctor_set(x_2177, 0, x_2164);
lean_ctor_set(x_2177, 1, x_2165);
lean_ctor_set(x_2177, 2, x_2166);
lean_ctor_set(x_2177, 3, x_2167);
lean_ctor_set_uint8(x_2177, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
if (lean_is_scalar(x_2171)) {
 x_2178 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2178 = x_2171;
}
lean_ctor_set(x_2178, 0, x_2177);
lean_ctor_set(x_2178, 1, x_2162);
lean_ctor_set(x_2178, 2, x_2163);
lean_ctor_set(x_2178, 3, x_1265);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2179 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2179 = lean_box(0);
}
lean_ctor_set_uint8(x_2178, sizeof(void*)*4, x_2095);
if (lean_is_scalar(x_2179)) {
 x_2180 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2180 = x_2179;
}
lean_ctor_set(x_2180, 0, x_2178);
lean_ctor_set(x_2180, 1, x_2);
lean_ctor_set(x_2180, 2, x_3);
lean_ctor_set(x_2180, 3, x_2172);
lean_ctor_set_uint8(x_2180, sizeof(void*)*4, x_1833);
if (lean_is_scalar(x_2168)) {
 x_2181 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2181 = x_2168;
}
lean_ctor_set(x_2181, 0, x_2175);
lean_ctor_set(x_2181, 1, x_2169);
lean_ctor_set(x_2181, 2, x_2170);
lean_ctor_set(x_2181, 3, x_2096);
lean_ctor_set_uint8(x_2181, sizeof(void*)*4, x_1833);
x_2182 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2182, 0, x_2180);
lean_ctor_set(x_2182, 1, x_2173);
lean_ctor_set(x_2182, 2, x_2174);
lean_ctor_set(x_2182, 3, x_2181);
lean_ctor_set_uint8(x_2182, sizeof(void*)*4, x_2095);
return x_2182;
}
}
else
{
uint8_t x_2183; 
x_2183 = lean_ctor_get_uint8(x_2096, sizeof(void*)*4);
if (x_2183 == 0)
{
uint8_t x_2184; 
x_2184 = !lean_is_exclusive(x_1);
if (x_2184 == 0)
{
lean_object* x_2185; lean_object* x_2186; lean_object* x_2187; lean_object* x_2188; uint8_t x_2189; 
x_2185 = lean_ctor_get(x_1, 1);
x_2186 = lean_ctor_get(x_1, 2);
x_2187 = lean_ctor_get(x_1, 3);
lean_dec(x_2187);
x_2188 = lean_ctor_get(x_1, 0);
lean_dec(x_2188);
x_2189 = !lean_is_exclusive(x_234);
if (x_2189 == 0)
{
uint8_t x_2190; 
x_2190 = !lean_is_exclusive(x_4);
if (x_2190 == 0)
{
lean_object* x_2191; lean_object* x_2192; lean_object* x_2193; lean_object* x_2194; lean_object* x_2195; lean_object* x_2196; lean_object* x_2197; lean_object* x_2198; uint8_t x_2199; 
x_2191 = lean_ctor_get(x_234, 0);
x_2192 = lean_ctor_get(x_234, 1);
x_2193 = lean_ctor_get(x_234, 2);
x_2194 = lean_ctor_get(x_234, 3);
x_2195 = lean_ctor_get(x_4, 1);
x_2196 = lean_ctor_get(x_4, 2);
x_2197 = lean_ctor_get(x_4, 3);
lean_dec(x_2197);
x_2198 = lean_ctor_get(x_4, 0);
lean_dec(x_2198);
x_2199 = !lean_is_exclusive(x_1890);
if (x_2199 == 0)
{
uint8_t x_2200; 
x_2200 = !lean_is_exclusive(x_2096);
if (x_2200 == 0)
{
lean_object* x_2201; lean_object* x_2202; lean_object* x_2203; lean_object* x_2204; lean_object* x_2205; lean_object* x_2206; lean_object* x_2207; lean_object* x_2208; uint8_t x_2209; 
x_2201 = lean_ctor_get(x_1890, 0);
x_2202 = lean_ctor_get(x_1890, 1);
x_2203 = lean_ctor_get(x_1890, 2);
x_2204 = lean_ctor_get(x_1890, 3);
x_2205 = lean_ctor_get(x_2096, 0);
x_2206 = lean_ctor_get(x_2096, 1);
x_2207 = lean_ctor_get(x_2096, 2);
x_2208 = lean_ctor_get(x_2096, 3);
lean_ctor_set(x_2096, 3, x_2194);
lean_ctor_set(x_2096, 2, x_2193);
lean_ctor_set(x_2096, 1, x_2192);
lean_ctor_set(x_2096, 0, x_2191);
lean_ctor_set_uint8(x_2096, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
lean_ctor_set(x_1890, 3, x_1265);
lean_ctor_set(x_1890, 2, x_2186);
lean_ctor_set(x_1890, 1, x_2185);
lean_ctor_set(x_1890, 0, x_2096);
x_2209 = !lean_is_exclusive(x_1265);
if (x_2209 == 0)
{
lean_object* x_2210; lean_object* x_2211; lean_object* x_2212; lean_object* x_2213; 
x_2210 = lean_ctor_get(x_1265, 3);
lean_dec(x_2210);
x_2211 = lean_ctor_get(x_1265, 2);
lean_dec(x_2211);
x_2212 = lean_ctor_get(x_1265, 1);
lean_dec(x_2212);
x_2213 = lean_ctor_get(x_1265, 0);
lean_dec(x_2213);
lean_ctor_set_uint8(x_1890, sizeof(void*)*4, x_2183);
lean_ctor_set(x_4, 3, x_2204);
lean_ctor_set(x_4, 2, x_2203);
lean_ctor_set(x_4, 1, x_2202);
lean_ctor_set(x_4, 0, x_2201);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2183);
lean_ctor_set(x_1265, 3, x_4);
lean_ctor_set(x_1265, 2, x_3);
lean_ctor_set(x_1265, 1, x_2);
lean_ctor_set(x_1265, 0, x_1890);
lean_ctor_set(x_234, 3, x_2208);
lean_ctor_set(x_234, 2, x_2207);
lean_ctor_set(x_234, 1, x_2206);
lean_ctor_set(x_234, 0, x_2205);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_2196);
lean_ctor_set(x_1, 1, x_2195);
lean_ctor_set(x_1, 0, x_1265);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2183);
return x_1;
}
else
{
lean_object* x_2214; 
lean_dec(x_1265);
lean_ctor_set_uint8(x_1890, sizeof(void*)*4, x_2183);
lean_ctor_set(x_4, 3, x_2204);
lean_ctor_set(x_4, 2, x_2203);
lean_ctor_set(x_4, 1, x_2202);
lean_ctor_set(x_4, 0, x_2201);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2183);
x_2214 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2214, 0, x_1890);
lean_ctor_set(x_2214, 1, x_2);
lean_ctor_set(x_2214, 2, x_3);
lean_ctor_set(x_2214, 3, x_4);
lean_ctor_set_uint8(x_2214, sizeof(void*)*4, x_1833);
lean_ctor_set(x_234, 3, x_2208);
lean_ctor_set(x_234, 2, x_2207);
lean_ctor_set(x_234, 1, x_2206);
lean_ctor_set(x_234, 0, x_2205);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_2196);
lean_ctor_set(x_1, 1, x_2195);
lean_ctor_set(x_1, 0, x_2214);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2183);
return x_1;
}
}
else
{
lean_object* x_2215; lean_object* x_2216; lean_object* x_2217; lean_object* x_2218; lean_object* x_2219; lean_object* x_2220; lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; lean_object* x_2224; lean_object* x_2225; 
x_2215 = lean_ctor_get(x_1890, 0);
x_2216 = lean_ctor_get(x_1890, 1);
x_2217 = lean_ctor_get(x_1890, 2);
x_2218 = lean_ctor_get(x_1890, 3);
x_2219 = lean_ctor_get(x_2096, 0);
x_2220 = lean_ctor_get(x_2096, 1);
x_2221 = lean_ctor_get(x_2096, 2);
x_2222 = lean_ctor_get(x_2096, 3);
lean_inc(x_2222);
lean_inc(x_2221);
lean_inc(x_2220);
lean_inc(x_2219);
lean_dec(x_2096);
x_2223 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2223, 0, x_2191);
lean_ctor_set(x_2223, 1, x_2192);
lean_ctor_set(x_2223, 2, x_2193);
lean_ctor_set(x_2223, 3, x_2194);
lean_ctor_set_uint8(x_2223, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
lean_ctor_set(x_1890, 3, x_1265);
lean_ctor_set(x_1890, 2, x_2186);
lean_ctor_set(x_1890, 1, x_2185);
lean_ctor_set(x_1890, 0, x_2223);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2224 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2224 = lean_box(0);
}
lean_ctor_set_uint8(x_1890, sizeof(void*)*4, x_2183);
lean_ctor_set(x_4, 3, x_2218);
lean_ctor_set(x_4, 2, x_2217);
lean_ctor_set(x_4, 1, x_2216);
lean_ctor_set(x_4, 0, x_2215);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2183);
if (lean_is_scalar(x_2224)) {
 x_2225 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2225 = x_2224;
}
lean_ctor_set(x_2225, 0, x_1890);
lean_ctor_set(x_2225, 1, x_2);
lean_ctor_set(x_2225, 2, x_3);
lean_ctor_set(x_2225, 3, x_4);
lean_ctor_set_uint8(x_2225, sizeof(void*)*4, x_1833);
lean_ctor_set(x_234, 3, x_2222);
lean_ctor_set(x_234, 2, x_2221);
lean_ctor_set(x_234, 1, x_2220);
lean_ctor_set(x_234, 0, x_2219);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_2196);
lean_ctor_set(x_1, 1, x_2195);
lean_ctor_set(x_1, 0, x_2225);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2183);
return x_1;
}
}
else
{
lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; lean_object* x_2230; lean_object* x_2231; lean_object* x_2232; lean_object* x_2233; lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; lean_object* x_2238; 
x_2226 = lean_ctor_get(x_1890, 0);
x_2227 = lean_ctor_get(x_1890, 1);
x_2228 = lean_ctor_get(x_1890, 2);
x_2229 = lean_ctor_get(x_1890, 3);
lean_inc(x_2229);
lean_inc(x_2228);
lean_inc(x_2227);
lean_inc(x_2226);
lean_dec(x_1890);
x_2230 = lean_ctor_get(x_2096, 0);
lean_inc(x_2230);
x_2231 = lean_ctor_get(x_2096, 1);
lean_inc(x_2231);
x_2232 = lean_ctor_get(x_2096, 2);
lean_inc(x_2232);
x_2233 = lean_ctor_get(x_2096, 3);
lean_inc(x_2233);
if (lean_is_exclusive(x_2096)) {
 lean_ctor_release(x_2096, 0);
 lean_ctor_release(x_2096, 1);
 lean_ctor_release(x_2096, 2);
 lean_ctor_release(x_2096, 3);
 x_2234 = x_2096;
} else {
 lean_dec_ref(x_2096);
 x_2234 = lean_box(0);
}
if (lean_is_scalar(x_2234)) {
 x_2235 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2235 = x_2234;
}
lean_ctor_set(x_2235, 0, x_2191);
lean_ctor_set(x_2235, 1, x_2192);
lean_ctor_set(x_2235, 2, x_2193);
lean_ctor_set(x_2235, 3, x_2194);
lean_ctor_set_uint8(x_2235, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
x_2236 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2236, 0, x_2235);
lean_ctor_set(x_2236, 1, x_2185);
lean_ctor_set(x_2236, 2, x_2186);
lean_ctor_set(x_2236, 3, x_1265);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2237 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2237 = lean_box(0);
}
lean_ctor_set_uint8(x_2236, sizeof(void*)*4, x_2183);
lean_ctor_set(x_4, 3, x_2229);
lean_ctor_set(x_4, 2, x_2228);
lean_ctor_set(x_4, 1, x_2227);
lean_ctor_set(x_4, 0, x_2226);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2183);
if (lean_is_scalar(x_2237)) {
 x_2238 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2238 = x_2237;
}
lean_ctor_set(x_2238, 0, x_2236);
lean_ctor_set(x_2238, 1, x_2);
lean_ctor_set(x_2238, 2, x_3);
lean_ctor_set(x_2238, 3, x_4);
lean_ctor_set_uint8(x_2238, sizeof(void*)*4, x_1833);
lean_ctor_set(x_234, 3, x_2233);
lean_ctor_set(x_234, 2, x_2232);
lean_ctor_set(x_234, 1, x_2231);
lean_ctor_set(x_234, 0, x_2230);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_2196);
lean_ctor_set(x_1, 1, x_2195);
lean_ctor_set(x_1, 0, x_2238);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2183);
return x_1;
}
}
else
{
lean_object* x_2239; lean_object* x_2240; lean_object* x_2241; lean_object* x_2242; lean_object* x_2243; lean_object* x_2244; lean_object* x_2245; lean_object* x_2246; lean_object* x_2247; lean_object* x_2248; lean_object* x_2249; lean_object* x_2250; lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; lean_object* x_2258; lean_object* x_2259; 
x_2239 = lean_ctor_get(x_234, 0);
x_2240 = lean_ctor_get(x_234, 1);
x_2241 = lean_ctor_get(x_234, 2);
x_2242 = lean_ctor_get(x_234, 3);
x_2243 = lean_ctor_get(x_4, 1);
x_2244 = lean_ctor_get(x_4, 2);
lean_inc(x_2244);
lean_inc(x_2243);
lean_dec(x_4);
x_2245 = lean_ctor_get(x_1890, 0);
lean_inc(x_2245);
x_2246 = lean_ctor_get(x_1890, 1);
lean_inc(x_2246);
x_2247 = lean_ctor_get(x_1890, 2);
lean_inc(x_2247);
x_2248 = lean_ctor_get(x_1890, 3);
lean_inc(x_2248);
if (lean_is_exclusive(x_1890)) {
 lean_ctor_release(x_1890, 0);
 lean_ctor_release(x_1890, 1);
 lean_ctor_release(x_1890, 2);
 lean_ctor_release(x_1890, 3);
 x_2249 = x_1890;
} else {
 lean_dec_ref(x_1890);
 x_2249 = lean_box(0);
}
x_2250 = lean_ctor_get(x_2096, 0);
lean_inc(x_2250);
x_2251 = lean_ctor_get(x_2096, 1);
lean_inc(x_2251);
x_2252 = lean_ctor_get(x_2096, 2);
lean_inc(x_2252);
x_2253 = lean_ctor_get(x_2096, 3);
lean_inc(x_2253);
if (lean_is_exclusive(x_2096)) {
 lean_ctor_release(x_2096, 0);
 lean_ctor_release(x_2096, 1);
 lean_ctor_release(x_2096, 2);
 lean_ctor_release(x_2096, 3);
 x_2254 = x_2096;
} else {
 lean_dec_ref(x_2096);
 x_2254 = lean_box(0);
}
if (lean_is_scalar(x_2254)) {
 x_2255 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2255 = x_2254;
}
lean_ctor_set(x_2255, 0, x_2239);
lean_ctor_set(x_2255, 1, x_2240);
lean_ctor_set(x_2255, 2, x_2241);
lean_ctor_set(x_2255, 3, x_2242);
lean_ctor_set_uint8(x_2255, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
if (lean_is_scalar(x_2249)) {
 x_2256 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2256 = x_2249;
}
lean_ctor_set(x_2256, 0, x_2255);
lean_ctor_set(x_2256, 1, x_2185);
lean_ctor_set(x_2256, 2, x_2186);
lean_ctor_set(x_2256, 3, x_1265);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2257 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2257 = lean_box(0);
}
lean_ctor_set_uint8(x_2256, sizeof(void*)*4, x_2183);
x_2258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2258, 0, x_2245);
lean_ctor_set(x_2258, 1, x_2246);
lean_ctor_set(x_2258, 2, x_2247);
lean_ctor_set(x_2258, 3, x_2248);
lean_ctor_set_uint8(x_2258, sizeof(void*)*4, x_2183);
if (lean_is_scalar(x_2257)) {
 x_2259 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2259 = x_2257;
}
lean_ctor_set(x_2259, 0, x_2256);
lean_ctor_set(x_2259, 1, x_2);
lean_ctor_set(x_2259, 2, x_3);
lean_ctor_set(x_2259, 3, x_2258);
lean_ctor_set_uint8(x_2259, sizeof(void*)*4, x_1833);
lean_ctor_set(x_234, 3, x_2253);
lean_ctor_set(x_234, 2, x_2252);
lean_ctor_set(x_234, 1, x_2251);
lean_ctor_set(x_234, 0, x_2250);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_2244);
lean_ctor_set(x_1, 1, x_2243);
lean_ctor_set(x_1, 0, x_2259);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2183);
return x_1;
}
}
else
{
lean_object* x_2260; lean_object* x_2261; lean_object* x_2262; lean_object* x_2263; lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; lean_object* x_2267; lean_object* x_2268; lean_object* x_2269; lean_object* x_2270; lean_object* x_2271; lean_object* x_2272; lean_object* x_2273; lean_object* x_2274; lean_object* x_2275; lean_object* x_2276; lean_object* x_2277; lean_object* x_2278; lean_object* x_2279; lean_object* x_2280; lean_object* x_2281; lean_object* x_2282; 
x_2260 = lean_ctor_get(x_234, 0);
x_2261 = lean_ctor_get(x_234, 1);
x_2262 = lean_ctor_get(x_234, 2);
x_2263 = lean_ctor_get(x_234, 3);
lean_inc(x_2263);
lean_inc(x_2262);
lean_inc(x_2261);
lean_inc(x_2260);
lean_dec(x_234);
x_2264 = lean_ctor_get(x_4, 1);
lean_inc(x_2264);
x_2265 = lean_ctor_get(x_4, 2);
lean_inc(x_2265);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_2266 = x_4;
} else {
 lean_dec_ref(x_4);
 x_2266 = lean_box(0);
}
x_2267 = lean_ctor_get(x_1890, 0);
lean_inc(x_2267);
x_2268 = lean_ctor_get(x_1890, 1);
lean_inc(x_2268);
x_2269 = lean_ctor_get(x_1890, 2);
lean_inc(x_2269);
x_2270 = lean_ctor_get(x_1890, 3);
lean_inc(x_2270);
if (lean_is_exclusive(x_1890)) {
 lean_ctor_release(x_1890, 0);
 lean_ctor_release(x_1890, 1);
 lean_ctor_release(x_1890, 2);
 lean_ctor_release(x_1890, 3);
 x_2271 = x_1890;
} else {
 lean_dec_ref(x_1890);
 x_2271 = lean_box(0);
}
x_2272 = lean_ctor_get(x_2096, 0);
lean_inc(x_2272);
x_2273 = lean_ctor_get(x_2096, 1);
lean_inc(x_2273);
x_2274 = lean_ctor_get(x_2096, 2);
lean_inc(x_2274);
x_2275 = lean_ctor_get(x_2096, 3);
lean_inc(x_2275);
if (lean_is_exclusive(x_2096)) {
 lean_ctor_release(x_2096, 0);
 lean_ctor_release(x_2096, 1);
 lean_ctor_release(x_2096, 2);
 lean_ctor_release(x_2096, 3);
 x_2276 = x_2096;
} else {
 lean_dec_ref(x_2096);
 x_2276 = lean_box(0);
}
if (lean_is_scalar(x_2276)) {
 x_2277 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2277 = x_2276;
}
lean_ctor_set(x_2277, 0, x_2260);
lean_ctor_set(x_2277, 1, x_2261);
lean_ctor_set(x_2277, 2, x_2262);
lean_ctor_set(x_2277, 3, x_2263);
lean_ctor_set_uint8(x_2277, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
if (lean_is_scalar(x_2271)) {
 x_2278 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2278 = x_2271;
}
lean_ctor_set(x_2278, 0, x_2277);
lean_ctor_set(x_2278, 1, x_2185);
lean_ctor_set(x_2278, 2, x_2186);
lean_ctor_set(x_2278, 3, x_1265);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2279 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2279 = lean_box(0);
}
lean_ctor_set_uint8(x_2278, sizeof(void*)*4, x_2183);
if (lean_is_scalar(x_2266)) {
 x_2280 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2280 = x_2266;
}
lean_ctor_set(x_2280, 0, x_2267);
lean_ctor_set(x_2280, 1, x_2268);
lean_ctor_set(x_2280, 2, x_2269);
lean_ctor_set(x_2280, 3, x_2270);
lean_ctor_set_uint8(x_2280, sizeof(void*)*4, x_2183);
if (lean_is_scalar(x_2279)) {
 x_2281 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2281 = x_2279;
}
lean_ctor_set(x_2281, 0, x_2278);
lean_ctor_set(x_2281, 1, x_2);
lean_ctor_set(x_2281, 2, x_3);
lean_ctor_set(x_2281, 3, x_2280);
lean_ctor_set_uint8(x_2281, sizeof(void*)*4, x_1833);
x_2282 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2282, 0, x_2272);
lean_ctor_set(x_2282, 1, x_2273);
lean_ctor_set(x_2282, 2, x_2274);
lean_ctor_set(x_2282, 3, x_2275);
lean_ctor_set_uint8(x_2282, sizeof(void*)*4, x_1833);
lean_ctor_set(x_1, 3, x_2282);
lean_ctor_set(x_1, 2, x_2265);
lean_ctor_set(x_1, 1, x_2264);
lean_ctor_set(x_1, 0, x_2281);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2183);
return x_1;
}
}
else
{
lean_object* x_2283; lean_object* x_2284; lean_object* x_2285; lean_object* x_2286; lean_object* x_2287; lean_object* x_2288; lean_object* x_2289; lean_object* x_2290; lean_object* x_2291; lean_object* x_2292; lean_object* x_2293; lean_object* x_2294; lean_object* x_2295; lean_object* x_2296; lean_object* x_2297; lean_object* x_2298; lean_object* x_2299; lean_object* x_2300; lean_object* x_2301; lean_object* x_2302; lean_object* x_2303; lean_object* x_2304; lean_object* x_2305; lean_object* x_2306; lean_object* x_2307; lean_object* x_2308; lean_object* x_2309; 
x_2283 = lean_ctor_get(x_1, 1);
x_2284 = lean_ctor_get(x_1, 2);
lean_inc(x_2284);
lean_inc(x_2283);
lean_dec(x_1);
x_2285 = lean_ctor_get(x_234, 0);
lean_inc(x_2285);
x_2286 = lean_ctor_get(x_234, 1);
lean_inc(x_2286);
x_2287 = lean_ctor_get(x_234, 2);
lean_inc(x_2287);
x_2288 = lean_ctor_get(x_234, 3);
lean_inc(x_2288);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_2289 = x_234;
} else {
 lean_dec_ref(x_234);
 x_2289 = lean_box(0);
}
x_2290 = lean_ctor_get(x_4, 1);
lean_inc(x_2290);
x_2291 = lean_ctor_get(x_4, 2);
lean_inc(x_2291);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_2292 = x_4;
} else {
 lean_dec_ref(x_4);
 x_2292 = lean_box(0);
}
x_2293 = lean_ctor_get(x_1890, 0);
lean_inc(x_2293);
x_2294 = lean_ctor_get(x_1890, 1);
lean_inc(x_2294);
x_2295 = lean_ctor_get(x_1890, 2);
lean_inc(x_2295);
x_2296 = lean_ctor_get(x_1890, 3);
lean_inc(x_2296);
if (lean_is_exclusive(x_1890)) {
 lean_ctor_release(x_1890, 0);
 lean_ctor_release(x_1890, 1);
 lean_ctor_release(x_1890, 2);
 lean_ctor_release(x_1890, 3);
 x_2297 = x_1890;
} else {
 lean_dec_ref(x_1890);
 x_2297 = lean_box(0);
}
x_2298 = lean_ctor_get(x_2096, 0);
lean_inc(x_2298);
x_2299 = lean_ctor_get(x_2096, 1);
lean_inc(x_2299);
x_2300 = lean_ctor_get(x_2096, 2);
lean_inc(x_2300);
x_2301 = lean_ctor_get(x_2096, 3);
lean_inc(x_2301);
if (lean_is_exclusive(x_2096)) {
 lean_ctor_release(x_2096, 0);
 lean_ctor_release(x_2096, 1);
 lean_ctor_release(x_2096, 2);
 lean_ctor_release(x_2096, 3);
 x_2302 = x_2096;
} else {
 lean_dec_ref(x_2096);
 x_2302 = lean_box(0);
}
if (lean_is_scalar(x_2302)) {
 x_2303 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2303 = x_2302;
}
lean_ctor_set(x_2303, 0, x_2285);
lean_ctor_set(x_2303, 1, x_2286);
lean_ctor_set(x_2303, 2, x_2287);
lean_ctor_set(x_2303, 3, x_2288);
lean_ctor_set_uint8(x_2303, sizeof(void*)*4, x_1833);
lean_inc(x_1265);
if (lean_is_scalar(x_2297)) {
 x_2304 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2304 = x_2297;
}
lean_ctor_set(x_2304, 0, x_2303);
lean_ctor_set(x_2304, 1, x_2283);
lean_ctor_set(x_2304, 2, x_2284);
lean_ctor_set(x_2304, 3, x_1265);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2305 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2305 = lean_box(0);
}
lean_ctor_set_uint8(x_2304, sizeof(void*)*4, x_2183);
if (lean_is_scalar(x_2292)) {
 x_2306 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2306 = x_2292;
}
lean_ctor_set(x_2306, 0, x_2293);
lean_ctor_set(x_2306, 1, x_2294);
lean_ctor_set(x_2306, 2, x_2295);
lean_ctor_set(x_2306, 3, x_2296);
lean_ctor_set_uint8(x_2306, sizeof(void*)*4, x_2183);
if (lean_is_scalar(x_2305)) {
 x_2307 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2307 = x_2305;
}
lean_ctor_set(x_2307, 0, x_2304);
lean_ctor_set(x_2307, 1, x_2);
lean_ctor_set(x_2307, 2, x_3);
lean_ctor_set(x_2307, 3, x_2306);
lean_ctor_set_uint8(x_2307, sizeof(void*)*4, x_1833);
if (lean_is_scalar(x_2289)) {
 x_2308 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2308 = x_2289;
}
lean_ctor_set(x_2308, 0, x_2298);
lean_ctor_set(x_2308, 1, x_2299);
lean_ctor_set(x_2308, 2, x_2300);
lean_ctor_set(x_2308, 3, x_2301);
lean_ctor_set_uint8(x_2308, sizeof(void*)*4, x_1833);
x_2309 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2309, 0, x_2307);
lean_ctor_set(x_2309, 1, x_2290);
lean_ctor_set(x_2309, 2, x_2291);
lean_ctor_set(x_2309, 3, x_2308);
lean_ctor_set_uint8(x_2309, sizeof(void*)*4, x_2183);
return x_2309;
}
}
else
{
uint8_t x_2310; 
x_2310 = !lean_is_exclusive(x_1);
if (x_2310 == 0)
{
lean_object* x_2311; lean_object* x_2312; lean_object* x_2313; lean_object* x_2314; uint8_t x_2315; 
x_2311 = lean_ctor_get(x_1, 1);
x_2312 = lean_ctor_get(x_1, 2);
x_2313 = lean_ctor_get(x_1, 3);
lean_dec(x_2313);
x_2314 = lean_ctor_get(x_1, 0);
lean_dec(x_2314);
x_2315 = !lean_is_exclusive(x_234);
if (x_2315 == 0)
{
uint8_t x_2316; 
x_2316 = !lean_is_exclusive(x_1265);
if (x_2316 == 0)
{
uint8_t x_2317; 
x_2317 = !lean_is_exclusive(x_4);
if (x_2317 == 0)
{
lean_object* x_2318; lean_object* x_2319; lean_object* x_2320; lean_object* x_2321; lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; lean_object* x_2329; uint8_t x_2330; 
x_2318 = lean_ctor_get(x_234, 0);
x_2319 = lean_ctor_get(x_234, 1);
x_2320 = lean_ctor_get(x_234, 2);
x_2321 = lean_ctor_get(x_234, 3);
x_2322 = lean_ctor_get(x_1265, 0);
x_2323 = lean_ctor_get(x_1265, 1);
x_2324 = lean_ctor_get(x_1265, 2);
x_2325 = lean_ctor_get(x_1265, 3);
x_2326 = lean_ctor_get(x_4, 1);
x_2327 = lean_ctor_get(x_4, 2);
x_2328 = lean_ctor_get(x_4, 3);
lean_dec(x_2328);
x_2329 = lean_ctor_get(x_4, 0);
lean_dec(x_2329);
x_2330 = !lean_is_exclusive(x_1890);
if (x_2330 == 0)
{
lean_object* x_2331; lean_object* x_2332; lean_object* x_2333; lean_object* x_2334; lean_object* x_2335; 
x_2331 = lean_ctor_get(x_1890, 0);
x_2332 = lean_ctor_get(x_1890, 1);
x_2333 = lean_ctor_get(x_1890, 2);
x_2334 = lean_ctor_get(x_1890, 3);
lean_ctor_set(x_1890, 3, x_2321);
lean_ctor_set(x_1890, 2, x_2320);
lean_ctor_set(x_1890, 1, x_2319);
lean_ctor_set(x_1890, 0, x_2318);
lean_ctor_set_uint8(x_1890, sizeof(void*)*4, x_2183);
lean_ctor_set(x_4, 3, x_2325);
lean_ctor_set(x_4, 2, x_2324);
lean_ctor_set(x_4, 1, x_2323);
lean_ctor_set(x_4, 0, x_2322);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2183);
lean_ctor_set(x_1265, 3, x_4);
lean_ctor_set(x_1265, 2, x_2312);
lean_ctor_set(x_1265, 1, x_2311);
lean_ctor_set(x_1265, 0, x_1890);
lean_ctor_set_uint8(x_1265, sizeof(void*)*4, x_2095);
lean_ctor_set(x_234, 3, x_2331);
lean_ctor_set(x_234, 2, x_3);
lean_ctor_set(x_234, 1, x_2);
lean_ctor_set(x_234, 0, x_1265);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_2183);
lean_ctor_set(x_1, 3, x_2096);
lean_ctor_set(x_1, 2, x_2327);
lean_ctor_set(x_1, 1, x_2326);
lean_ctor_set(x_1, 0, x_2334);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2183);
x_2335 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2335, 0, x_234);
lean_ctor_set(x_2335, 1, x_2332);
lean_ctor_set(x_2335, 2, x_2333);
lean_ctor_set(x_2335, 3, x_1);
lean_ctor_set_uint8(x_2335, sizeof(void*)*4, x_2095);
return x_2335;
}
else
{
lean_object* x_2336; lean_object* x_2337; lean_object* x_2338; lean_object* x_2339; lean_object* x_2340; lean_object* x_2341; 
x_2336 = lean_ctor_get(x_1890, 0);
x_2337 = lean_ctor_get(x_1890, 1);
x_2338 = lean_ctor_get(x_1890, 2);
x_2339 = lean_ctor_get(x_1890, 3);
lean_inc(x_2339);
lean_inc(x_2338);
lean_inc(x_2337);
lean_inc(x_2336);
lean_dec(x_1890);
x_2340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2340, 0, x_2318);
lean_ctor_set(x_2340, 1, x_2319);
lean_ctor_set(x_2340, 2, x_2320);
lean_ctor_set(x_2340, 3, x_2321);
lean_ctor_set_uint8(x_2340, sizeof(void*)*4, x_2183);
lean_ctor_set(x_4, 3, x_2325);
lean_ctor_set(x_4, 2, x_2324);
lean_ctor_set(x_4, 1, x_2323);
lean_ctor_set(x_4, 0, x_2322);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2183);
lean_ctor_set(x_1265, 3, x_4);
lean_ctor_set(x_1265, 2, x_2312);
lean_ctor_set(x_1265, 1, x_2311);
lean_ctor_set(x_1265, 0, x_2340);
lean_ctor_set_uint8(x_1265, sizeof(void*)*4, x_2095);
lean_ctor_set(x_234, 3, x_2336);
lean_ctor_set(x_234, 2, x_3);
lean_ctor_set(x_234, 1, x_2);
lean_ctor_set(x_234, 0, x_1265);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_2183);
lean_ctor_set(x_1, 3, x_2096);
lean_ctor_set(x_1, 2, x_2327);
lean_ctor_set(x_1, 1, x_2326);
lean_ctor_set(x_1, 0, x_2339);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2183);
x_2341 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2341, 0, x_234);
lean_ctor_set(x_2341, 1, x_2337);
lean_ctor_set(x_2341, 2, x_2338);
lean_ctor_set(x_2341, 3, x_1);
lean_ctor_set_uint8(x_2341, sizeof(void*)*4, x_2095);
return x_2341;
}
}
else
{
lean_object* x_2342; lean_object* x_2343; lean_object* x_2344; lean_object* x_2345; lean_object* x_2346; lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; lean_object* x_2350; lean_object* x_2351; lean_object* x_2352; lean_object* x_2353; lean_object* x_2354; lean_object* x_2355; lean_object* x_2356; lean_object* x_2357; lean_object* x_2358; lean_object* x_2359; 
x_2342 = lean_ctor_get(x_234, 0);
x_2343 = lean_ctor_get(x_234, 1);
x_2344 = lean_ctor_get(x_234, 2);
x_2345 = lean_ctor_get(x_234, 3);
x_2346 = lean_ctor_get(x_1265, 0);
x_2347 = lean_ctor_get(x_1265, 1);
x_2348 = lean_ctor_get(x_1265, 2);
x_2349 = lean_ctor_get(x_1265, 3);
x_2350 = lean_ctor_get(x_4, 1);
x_2351 = lean_ctor_get(x_4, 2);
lean_inc(x_2351);
lean_inc(x_2350);
lean_dec(x_4);
x_2352 = lean_ctor_get(x_1890, 0);
lean_inc(x_2352);
x_2353 = lean_ctor_get(x_1890, 1);
lean_inc(x_2353);
x_2354 = lean_ctor_get(x_1890, 2);
lean_inc(x_2354);
x_2355 = lean_ctor_get(x_1890, 3);
lean_inc(x_2355);
if (lean_is_exclusive(x_1890)) {
 lean_ctor_release(x_1890, 0);
 lean_ctor_release(x_1890, 1);
 lean_ctor_release(x_1890, 2);
 lean_ctor_release(x_1890, 3);
 x_2356 = x_1890;
} else {
 lean_dec_ref(x_1890);
 x_2356 = lean_box(0);
}
if (lean_is_scalar(x_2356)) {
 x_2357 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2357 = x_2356;
}
lean_ctor_set(x_2357, 0, x_2342);
lean_ctor_set(x_2357, 1, x_2343);
lean_ctor_set(x_2357, 2, x_2344);
lean_ctor_set(x_2357, 3, x_2345);
lean_ctor_set_uint8(x_2357, sizeof(void*)*4, x_2183);
x_2358 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2358, 0, x_2346);
lean_ctor_set(x_2358, 1, x_2347);
lean_ctor_set(x_2358, 2, x_2348);
lean_ctor_set(x_2358, 3, x_2349);
lean_ctor_set_uint8(x_2358, sizeof(void*)*4, x_2183);
lean_ctor_set(x_1265, 3, x_2358);
lean_ctor_set(x_1265, 2, x_2312);
lean_ctor_set(x_1265, 1, x_2311);
lean_ctor_set(x_1265, 0, x_2357);
lean_ctor_set_uint8(x_1265, sizeof(void*)*4, x_2095);
lean_ctor_set(x_234, 3, x_2352);
lean_ctor_set(x_234, 2, x_3);
lean_ctor_set(x_234, 1, x_2);
lean_ctor_set(x_234, 0, x_1265);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_2183);
lean_ctor_set(x_1, 3, x_2096);
lean_ctor_set(x_1, 2, x_2351);
lean_ctor_set(x_1, 1, x_2350);
lean_ctor_set(x_1, 0, x_2355);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2183);
x_2359 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2359, 0, x_234);
lean_ctor_set(x_2359, 1, x_2353);
lean_ctor_set(x_2359, 2, x_2354);
lean_ctor_set(x_2359, 3, x_1);
lean_ctor_set_uint8(x_2359, sizeof(void*)*4, x_2095);
return x_2359;
}
}
else
{
lean_object* x_2360; lean_object* x_2361; lean_object* x_2362; lean_object* x_2363; lean_object* x_2364; lean_object* x_2365; lean_object* x_2366; lean_object* x_2367; lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; lean_object* x_2373; lean_object* x_2374; lean_object* x_2375; lean_object* x_2376; lean_object* x_2377; lean_object* x_2378; lean_object* x_2379; 
x_2360 = lean_ctor_get(x_234, 0);
x_2361 = lean_ctor_get(x_234, 1);
x_2362 = lean_ctor_get(x_234, 2);
x_2363 = lean_ctor_get(x_234, 3);
x_2364 = lean_ctor_get(x_1265, 0);
x_2365 = lean_ctor_get(x_1265, 1);
x_2366 = lean_ctor_get(x_1265, 2);
x_2367 = lean_ctor_get(x_1265, 3);
lean_inc(x_2367);
lean_inc(x_2366);
lean_inc(x_2365);
lean_inc(x_2364);
lean_dec(x_1265);
x_2368 = lean_ctor_get(x_4, 1);
lean_inc(x_2368);
x_2369 = lean_ctor_get(x_4, 2);
lean_inc(x_2369);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_2370 = x_4;
} else {
 lean_dec_ref(x_4);
 x_2370 = lean_box(0);
}
x_2371 = lean_ctor_get(x_1890, 0);
lean_inc(x_2371);
x_2372 = lean_ctor_get(x_1890, 1);
lean_inc(x_2372);
x_2373 = lean_ctor_get(x_1890, 2);
lean_inc(x_2373);
x_2374 = lean_ctor_get(x_1890, 3);
lean_inc(x_2374);
if (lean_is_exclusive(x_1890)) {
 lean_ctor_release(x_1890, 0);
 lean_ctor_release(x_1890, 1);
 lean_ctor_release(x_1890, 2);
 lean_ctor_release(x_1890, 3);
 x_2375 = x_1890;
} else {
 lean_dec_ref(x_1890);
 x_2375 = lean_box(0);
}
if (lean_is_scalar(x_2375)) {
 x_2376 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2376 = x_2375;
}
lean_ctor_set(x_2376, 0, x_2360);
lean_ctor_set(x_2376, 1, x_2361);
lean_ctor_set(x_2376, 2, x_2362);
lean_ctor_set(x_2376, 3, x_2363);
lean_ctor_set_uint8(x_2376, sizeof(void*)*4, x_2183);
if (lean_is_scalar(x_2370)) {
 x_2377 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2377 = x_2370;
}
lean_ctor_set(x_2377, 0, x_2364);
lean_ctor_set(x_2377, 1, x_2365);
lean_ctor_set(x_2377, 2, x_2366);
lean_ctor_set(x_2377, 3, x_2367);
lean_ctor_set_uint8(x_2377, sizeof(void*)*4, x_2183);
x_2378 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2378, 0, x_2376);
lean_ctor_set(x_2378, 1, x_2311);
lean_ctor_set(x_2378, 2, x_2312);
lean_ctor_set(x_2378, 3, x_2377);
lean_ctor_set_uint8(x_2378, sizeof(void*)*4, x_2095);
lean_ctor_set(x_234, 3, x_2371);
lean_ctor_set(x_234, 2, x_3);
lean_ctor_set(x_234, 1, x_2);
lean_ctor_set(x_234, 0, x_2378);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_2183);
lean_ctor_set(x_1, 3, x_2096);
lean_ctor_set(x_1, 2, x_2369);
lean_ctor_set(x_1, 1, x_2368);
lean_ctor_set(x_1, 0, x_2374);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2183);
x_2379 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2379, 0, x_234);
lean_ctor_set(x_2379, 1, x_2372);
lean_ctor_set(x_2379, 2, x_2373);
lean_ctor_set(x_2379, 3, x_1);
lean_ctor_set_uint8(x_2379, sizeof(void*)*4, x_2095);
return x_2379;
}
}
else
{
lean_object* x_2380; lean_object* x_2381; lean_object* x_2382; lean_object* x_2383; lean_object* x_2384; lean_object* x_2385; lean_object* x_2386; lean_object* x_2387; lean_object* x_2388; lean_object* x_2389; lean_object* x_2390; lean_object* x_2391; lean_object* x_2392; lean_object* x_2393; lean_object* x_2394; lean_object* x_2395; lean_object* x_2396; lean_object* x_2397; lean_object* x_2398; lean_object* x_2399; lean_object* x_2400; lean_object* x_2401; 
x_2380 = lean_ctor_get(x_234, 0);
x_2381 = lean_ctor_get(x_234, 1);
x_2382 = lean_ctor_get(x_234, 2);
x_2383 = lean_ctor_get(x_234, 3);
lean_inc(x_2383);
lean_inc(x_2382);
lean_inc(x_2381);
lean_inc(x_2380);
lean_dec(x_234);
x_2384 = lean_ctor_get(x_1265, 0);
lean_inc(x_2384);
x_2385 = lean_ctor_get(x_1265, 1);
lean_inc(x_2385);
x_2386 = lean_ctor_get(x_1265, 2);
lean_inc(x_2386);
x_2387 = lean_ctor_get(x_1265, 3);
lean_inc(x_2387);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2388 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2388 = lean_box(0);
}
x_2389 = lean_ctor_get(x_4, 1);
lean_inc(x_2389);
x_2390 = lean_ctor_get(x_4, 2);
lean_inc(x_2390);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_2391 = x_4;
} else {
 lean_dec_ref(x_4);
 x_2391 = lean_box(0);
}
x_2392 = lean_ctor_get(x_1890, 0);
lean_inc(x_2392);
x_2393 = lean_ctor_get(x_1890, 1);
lean_inc(x_2393);
x_2394 = lean_ctor_get(x_1890, 2);
lean_inc(x_2394);
x_2395 = lean_ctor_get(x_1890, 3);
lean_inc(x_2395);
if (lean_is_exclusive(x_1890)) {
 lean_ctor_release(x_1890, 0);
 lean_ctor_release(x_1890, 1);
 lean_ctor_release(x_1890, 2);
 lean_ctor_release(x_1890, 3);
 x_2396 = x_1890;
} else {
 lean_dec_ref(x_1890);
 x_2396 = lean_box(0);
}
if (lean_is_scalar(x_2396)) {
 x_2397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2397 = x_2396;
}
lean_ctor_set(x_2397, 0, x_2380);
lean_ctor_set(x_2397, 1, x_2381);
lean_ctor_set(x_2397, 2, x_2382);
lean_ctor_set(x_2397, 3, x_2383);
lean_ctor_set_uint8(x_2397, sizeof(void*)*4, x_2183);
if (lean_is_scalar(x_2391)) {
 x_2398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2398 = x_2391;
}
lean_ctor_set(x_2398, 0, x_2384);
lean_ctor_set(x_2398, 1, x_2385);
lean_ctor_set(x_2398, 2, x_2386);
lean_ctor_set(x_2398, 3, x_2387);
lean_ctor_set_uint8(x_2398, sizeof(void*)*4, x_2183);
if (lean_is_scalar(x_2388)) {
 x_2399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2399 = x_2388;
}
lean_ctor_set(x_2399, 0, x_2397);
lean_ctor_set(x_2399, 1, x_2311);
lean_ctor_set(x_2399, 2, x_2312);
lean_ctor_set(x_2399, 3, x_2398);
lean_ctor_set_uint8(x_2399, sizeof(void*)*4, x_2095);
x_2400 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2400, 0, x_2399);
lean_ctor_set(x_2400, 1, x_2);
lean_ctor_set(x_2400, 2, x_3);
lean_ctor_set(x_2400, 3, x_2392);
lean_ctor_set_uint8(x_2400, sizeof(void*)*4, x_2183);
lean_ctor_set(x_1, 3, x_2096);
lean_ctor_set(x_1, 2, x_2390);
lean_ctor_set(x_1, 1, x_2389);
lean_ctor_set(x_1, 0, x_2395);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2183);
x_2401 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2401, 0, x_2400);
lean_ctor_set(x_2401, 1, x_2393);
lean_ctor_set(x_2401, 2, x_2394);
lean_ctor_set(x_2401, 3, x_1);
lean_ctor_set_uint8(x_2401, sizeof(void*)*4, x_2095);
return x_2401;
}
}
else
{
lean_object* x_2402; lean_object* x_2403; lean_object* x_2404; lean_object* x_2405; lean_object* x_2406; lean_object* x_2407; lean_object* x_2408; lean_object* x_2409; lean_object* x_2410; lean_object* x_2411; lean_object* x_2412; lean_object* x_2413; lean_object* x_2414; lean_object* x_2415; lean_object* x_2416; lean_object* x_2417; lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; lean_object* x_2421; lean_object* x_2422; lean_object* x_2423; lean_object* x_2424; lean_object* x_2425; lean_object* x_2426; lean_object* x_2427; 
x_2402 = lean_ctor_get(x_1, 1);
x_2403 = lean_ctor_get(x_1, 2);
lean_inc(x_2403);
lean_inc(x_2402);
lean_dec(x_1);
x_2404 = lean_ctor_get(x_234, 0);
lean_inc(x_2404);
x_2405 = lean_ctor_get(x_234, 1);
lean_inc(x_2405);
x_2406 = lean_ctor_get(x_234, 2);
lean_inc(x_2406);
x_2407 = lean_ctor_get(x_234, 3);
lean_inc(x_2407);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_2408 = x_234;
} else {
 lean_dec_ref(x_234);
 x_2408 = lean_box(0);
}
x_2409 = lean_ctor_get(x_1265, 0);
lean_inc(x_2409);
x_2410 = lean_ctor_get(x_1265, 1);
lean_inc(x_2410);
x_2411 = lean_ctor_get(x_1265, 2);
lean_inc(x_2411);
x_2412 = lean_ctor_get(x_1265, 3);
lean_inc(x_2412);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2413 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2413 = lean_box(0);
}
x_2414 = lean_ctor_get(x_4, 1);
lean_inc(x_2414);
x_2415 = lean_ctor_get(x_4, 2);
lean_inc(x_2415);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_2416 = x_4;
} else {
 lean_dec_ref(x_4);
 x_2416 = lean_box(0);
}
x_2417 = lean_ctor_get(x_1890, 0);
lean_inc(x_2417);
x_2418 = lean_ctor_get(x_1890, 1);
lean_inc(x_2418);
x_2419 = lean_ctor_get(x_1890, 2);
lean_inc(x_2419);
x_2420 = lean_ctor_get(x_1890, 3);
lean_inc(x_2420);
if (lean_is_exclusive(x_1890)) {
 lean_ctor_release(x_1890, 0);
 lean_ctor_release(x_1890, 1);
 lean_ctor_release(x_1890, 2);
 lean_ctor_release(x_1890, 3);
 x_2421 = x_1890;
} else {
 lean_dec_ref(x_1890);
 x_2421 = lean_box(0);
}
if (lean_is_scalar(x_2421)) {
 x_2422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2422 = x_2421;
}
lean_ctor_set(x_2422, 0, x_2404);
lean_ctor_set(x_2422, 1, x_2405);
lean_ctor_set(x_2422, 2, x_2406);
lean_ctor_set(x_2422, 3, x_2407);
lean_ctor_set_uint8(x_2422, sizeof(void*)*4, x_2183);
if (lean_is_scalar(x_2416)) {
 x_2423 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2423 = x_2416;
}
lean_ctor_set(x_2423, 0, x_2409);
lean_ctor_set(x_2423, 1, x_2410);
lean_ctor_set(x_2423, 2, x_2411);
lean_ctor_set(x_2423, 3, x_2412);
lean_ctor_set_uint8(x_2423, sizeof(void*)*4, x_2183);
if (lean_is_scalar(x_2413)) {
 x_2424 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2424 = x_2413;
}
lean_ctor_set(x_2424, 0, x_2422);
lean_ctor_set(x_2424, 1, x_2402);
lean_ctor_set(x_2424, 2, x_2403);
lean_ctor_set(x_2424, 3, x_2423);
lean_ctor_set_uint8(x_2424, sizeof(void*)*4, x_2095);
if (lean_is_scalar(x_2408)) {
 x_2425 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2425 = x_2408;
}
lean_ctor_set(x_2425, 0, x_2424);
lean_ctor_set(x_2425, 1, x_2);
lean_ctor_set(x_2425, 2, x_3);
lean_ctor_set(x_2425, 3, x_2417);
lean_ctor_set_uint8(x_2425, sizeof(void*)*4, x_2183);
x_2426 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2426, 0, x_2420);
lean_ctor_set(x_2426, 1, x_2414);
lean_ctor_set(x_2426, 2, x_2415);
lean_ctor_set(x_2426, 3, x_2096);
lean_ctor_set_uint8(x_2426, sizeof(void*)*4, x_2183);
x_2427 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2427, 0, x_2425);
lean_ctor_set(x_2427, 1, x_2418);
lean_ctor_set(x_2427, 2, x_2419);
lean_ctor_set(x_2427, 3, x_2426);
lean_ctor_set_uint8(x_2427, sizeof(void*)*4, x_2095);
return x_2427;
}
}
}
}
else
{
lean_object* x_2428; 
x_2428 = lean_ctor_get(x_4, 3);
lean_inc(x_2428);
if (lean_obj_tag(x_2428) == 0)
{
uint8_t x_2429; 
x_2429 = !lean_is_exclusive(x_1890);
if (x_2429 == 0)
{
lean_object* x_2430; lean_object* x_2431; lean_object* x_2432; lean_object* x_2433; uint8_t x_2434; 
x_2430 = lean_ctor_get(x_1890, 3);
lean_dec(x_2430);
x_2431 = lean_ctor_get(x_1890, 2);
lean_dec(x_2431);
x_2432 = lean_ctor_get(x_1890, 1);
lean_dec(x_2432);
x_2433 = lean_ctor_get(x_1890, 0);
lean_dec(x_2433);
x_2434 = !lean_is_exclusive(x_1);
if (x_2434 == 0)
{
lean_object* x_2435; lean_object* x_2436; lean_object* x_2437; lean_object* x_2438; uint8_t x_2439; 
x_2435 = lean_ctor_get(x_1, 1);
x_2436 = lean_ctor_get(x_1, 2);
x_2437 = lean_ctor_get(x_1, 3);
lean_dec(x_2437);
x_2438 = lean_ctor_get(x_1, 0);
lean_dec(x_2438);
x_2439 = !lean_is_exclusive(x_234);
if (x_2439 == 0)
{
uint8_t x_2440; 
x_2440 = !lean_is_exclusive(x_1265);
if (x_2440 == 0)
{
lean_object* x_2441; lean_object* x_2442; lean_object* x_2443; lean_object* x_2444; 
x_2441 = lean_ctor_get(x_234, 0);
x_2442 = lean_ctor_get(x_234, 1);
x_2443 = lean_ctor_get(x_234, 2);
x_2444 = lean_ctor_get(x_234, 3);
lean_ctor_set(x_1890, 3, x_2444);
lean_ctor_set(x_1890, 2, x_2443);
lean_ctor_set(x_1890, 1, x_2442);
lean_ctor_set(x_1890, 0, x_2441);
lean_ctor_set_uint8(x_1265, sizeof(void*)*4, x_2095);
lean_ctor_set(x_234, 3, x_1265);
lean_ctor_set(x_234, 2, x_2436);
lean_ctor_set(x_234, 1, x_2435);
lean_ctor_set(x_234, 0, x_1890);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
else
{
lean_object* x_2445; lean_object* x_2446; lean_object* x_2447; lean_object* x_2448; lean_object* x_2449; lean_object* x_2450; lean_object* x_2451; lean_object* x_2452; lean_object* x_2453; 
x_2445 = lean_ctor_get(x_234, 0);
x_2446 = lean_ctor_get(x_234, 1);
x_2447 = lean_ctor_get(x_234, 2);
x_2448 = lean_ctor_get(x_234, 3);
x_2449 = lean_ctor_get(x_1265, 0);
x_2450 = lean_ctor_get(x_1265, 1);
x_2451 = lean_ctor_get(x_1265, 2);
x_2452 = lean_ctor_get(x_1265, 3);
lean_inc(x_2452);
lean_inc(x_2451);
lean_inc(x_2450);
lean_inc(x_2449);
lean_dec(x_1265);
lean_ctor_set(x_1890, 3, x_2448);
lean_ctor_set(x_1890, 2, x_2447);
lean_ctor_set(x_1890, 1, x_2446);
lean_ctor_set(x_1890, 0, x_2445);
x_2453 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2453, 0, x_2449);
lean_ctor_set(x_2453, 1, x_2450);
lean_ctor_set(x_2453, 2, x_2451);
lean_ctor_set(x_2453, 3, x_2452);
lean_ctor_set_uint8(x_2453, sizeof(void*)*4, x_2095);
lean_ctor_set(x_234, 3, x_2453);
lean_ctor_set(x_234, 2, x_2436);
lean_ctor_set(x_234, 1, x_2435);
lean_ctor_set(x_234, 0, x_1890);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
}
else
{
lean_object* x_2454; lean_object* x_2455; lean_object* x_2456; lean_object* x_2457; lean_object* x_2458; lean_object* x_2459; lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; lean_object* x_2463; lean_object* x_2464; 
x_2454 = lean_ctor_get(x_234, 0);
x_2455 = lean_ctor_get(x_234, 1);
x_2456 = lean_ctor_get(x_234, 2);
x_2457 = lean_ctor_get(x_234, 3);
lean_inc(x_2457);
lean_inc(x_2456);
lean_inc(x_2455);
lean_inc(x_2454);
lean_dec(x_234);
x_2458 = lean_ctor_get(x_1265, 0);
lean_inc(x_2458);
x_2459 = lean_ctor_get(x_1265, 1);
lean_inc(x_2459);
x_2460 = lean_ctor_get(x_1265, 2);
lean_inc(x_2460);
x_2461 = lean_ctor_get(x_1265, 3);
lean_inc(x_2461);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2462 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2462 = lean_box(0);
}
lean_ctor_set(x_1890, 3, x_2457);
lean_ctor_set(x_1890, 2, x_2456);
lean_ctor_set(x_1890, 1, x_2455);
lean_ctor_set(x_1890, 0, x_2454);
if (lean_is_scalar(x_2462)) {
 x_2463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2463 = x_2462;
}
lean_ctor_set(x_2463, 0, x_2458);
lean_ctor_set(x_2463, 1, x_2459);
lean_ctor_set(x_2463, 2, x_2460);
lean_ctor_set(x_2463, 3, x_2461);
lean_ctor_set_uint8(x_2463, sizeof(void*)*4, x_2095);
x_2464 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2464, 0, x_1890);
lean_ctor_set(x_2464, 1, x_2435);
lean_ctor_set(x_2464, 2, x_2436);
lean_ctor_set(x_2464, 3, x_2463);
lean_ctor_set_uint8(x_2464, sizeof(void*)*4, x_1889);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_2464);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2095);
return x_1;
}
}
else
{
lean_object* x_2465; lean_object* x_2466; lean_object* x_2467; lean_object* x_2468; lean_object* x_2469; lean_object* x_2470; lean_object* x_2471; lean_object* x_2472; lean_object* x_2473; lean_object* x_2474; lean_object* x_2475; lean_object* x_2476; lean_object* x_2477; lean_object* x_2478; lean_object* x_2479; 
x_2465 = lean_ctor_get(x_1, 1);
x_2466 = lean_ctor_get(x_1, 2);
lean_inc(x_2466);
lean_inc(x_2465);
lean_dec(x_1);
x_2467 = lean_ctor_get(x_234, 0);
lean_inc(x_2467);
x_2468 = lean_ctor_get(x_234, 1);
lean_inc(x_2468);
x_2469 = lean_ctor_get(x_234, 2);
lean_inc(x_2469);
x_2470 = lean_ctor_get(x_234, 3);
lean_inc(x_2470);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_2471 = x_234;
} else {
 lean_dec_ref(x_234);
 x_2471 = lean_box(0);
}
x_2472 = lean_ctor_get(x_1265, 0);
lean_inc(x_2472);
x_2473 = lean_ctor_get(x_1265, 1);
lean_inc(x_2473);
x_2474 = lean_ctor_get(x_1265, 2);
lean_inc(x_2474);
x_2475 = lean_ctor_get(x_1265, 3);
lean_inc(x_2475);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2476 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2476 = lean_box(0);
}
lean_ctor_set(x_1890, 3, x_2470);
lean_ctor_set(x_1890, 2, x_2469);
lean_ctor_set(x_1890, 1, x_2468);
lean_ctor_set(x_1890, 0, x_2467);
if (lean_is_scalar(x_2476)) {
 x_2477 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2477 = x_2476;
}
lean_ctor_set(x_2477, 0, x_2472);
lean_ctor_set(x_2477, 1, x_2473);
lean_ctor_set(x_2477, 2, x_2474);
lean_ctor_set(x_2477, 3, x_2475);
lean_ctor_set_uint8(x_2477, sizeof(void*)*4, x_2095);
if (lean_is_scalar(x_2471)) {
 x_2478 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2478 = x_2471;
}
lean_ctor_set(x_2478, 0, x_1890);
lean_ctor_set(x_2478, 1, x_2465);
lean_ctor_set(x_2478, 2, x_2466);
lean_ctor_set(x_2478, 3, x_2477);
lean_ctor_set_uint8(x_2478, sizeof(void*)*4, x_1889);
x_2479 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2479, 0, x_2478);
lean_ctor_set(x_2479, 1, x_2);
lean_ctor_set(x_2479, 2, x_3);
lean_ctor_set(x_2479, 3, x_4);
lean_ctor_set_uint8(x_2479, sizeof(void*)*4, x_2095);
return x_2479;
}
}
else
{
lean_object* x_2480; lean_object* x_2481; lean_object* x_2482; lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; lean_object* x_2486; lean_object* x_2487; lean_object* x_2488; lean_object* x_2489; lean_object* x_2490; lean_object* x_2491; lean_object* x_2492; lean_object* x_2493; lean_object* x_2494; lean_object* x_2495; lean_object* x_2496; 
lean_dec(x_1890);
x_2480 = lean_ctor_get(x_1, 1);
lean_inc(x_2480);
x_2481 = lean_ctor_get(x_1, 2);
lean_inc(x_2481);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_2482 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2482 = lean_box(0);
}
x_2483 = lean_ctor_get(x_234, 0);
lean_inc(x_2483);
x_2484 = lean_ctor_get(x_234, 1);
lean_inc(x_2484);
x_2485 = lean_ctor_get(x_234, 2);
lean_inc(x_2485);
x_2486 = lean_ctor_get(x_234, 3);
lean_inc(x_2486);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_2487 = x_234;
} else {
 lean_dec_ref(x_234);
 x_2487 = lean_box(0);
}
x_2488 = lean_ctor_get(x_1265, 0);
lean_inc(x_2488);
x_2489 = lean_ctor_get(x_1265, 1);
lean_inc(x_2489);
x_2490 = lean_ctor_get(x_1265, 2);
lean_inc(x_2490);
x_2491 = lean_ctor_get(x_1265, 3);
lean_inc(x_2491);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2492 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2492 = lean_box(0);
}
x_2493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2493, 0, x_2483);
lean_ctor_set(x_2493, 1, x_2484);
lean_ctor_set(x_2493, 2, x_2485);
lean_ctor_set(x_2493, 3, x_2486);
lean_ctor_set_uint8(x_2493, sizeof(void*)*4, x_2095);
if (lean_is_scalar(x_2492)) {
 x_2494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2494 = x_2492;
}
lean_ctor_set(x_2494, 0, x_2488);
lean_ctor_set(x_2494, 1, x_2489);
lean_ctor_set(x_2494, 2, x_2490);
lean_ctor_set(x_2494, 3, x_2491);
lean_ctor_set_uint8(x_2494, sizeof(void*)*4, x_2095);
if (lean_is_scalar(x_2487)) {
 x_2495 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2495 = x_2487;
}
lean_ctor_set(x_2495, 0, x_2493);
lean_ctor_set(x_2495, 1, x_2480);
lean_ctor_set(x_2495, 2, x_2481);
lean_ctor_set(x_2495, 3, x_2494);
lean_ctor_set_uint8(x_2495, sizeof(void*)*4, x_1889);
if (lean_is_scalar(x_2482)) {
 x_2496 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2496 = x_2482;
}
lean_ctor_set(x_2496, 0, x_2495);
lean_ctor_set(x_2496, 1, x_2);
lean_ctor_set(x_2496, 2, x_3);
lean_ctor_set(x_2496, 3, x_4);
lean_ctor_set_uint8(x_2496, sizeof(void*)*4, x_2095);
return x_2496;
}
}
else
{
uint8_t x_2497; 
x_2497 = lean_ctor_get_uint8(x_2428, sizeof(void*)*4);
if (x_2497 == 0)
{
uint8_t x_2498; 
x_2498 = !lean_is_exclusive(x_1);
if (x_2498 == 0)
{
lean_object* x_2499; lean_object* x_2500; lean_object* x_2501; lean_object* x_2502; uint8_t x_2503; 
x_2499 = lean_ctor_get(x_1, 1);
x_2500 = lean_ctor_get(x_1, 2);
x_2501 = lean_ctor_get(x_1, 3);
lean_dec(x_2501);
x_2502 = lean_ctor_get(x_1, 0);
lean_dec(x_2502);
x_2503 = !lean_is_exclusive(x_234);
if (x_2503 == 0)
{
uint8_t x_2504; 
x_2504 = !lean_is_exclusive(x_1265);
if (x_2504 == 0)
{
uint8_t x_2505; 
x_2505 = !lean_is_exclusive(x_4);
if (x_2505 == 0)
{
lean_object* x_2506; lean_object* x_2507; lean_object* x_2508; lean_object* x_2509; lean_object* x_2510; lean_object* x_2511; lean_object* x_2512; lean_object* x_2513; lean_object* x_2514; lean_object* x_2515; lean_object* x_2516; lean_object* x_2517; uint8_t x_2518; 
x_2506 = lean_ctor_get(x_234, 0);
x_2507 = lean_ctor_get(x_234, 1);
x_2508 = lean_ctor_get(x_234, 2);
x_2509 = lean_ctor_get(x_234, 3);
x_2510 = lean_ctor_get(x_1265, 0);
x_2511 = lean_ctor_get(x_1265, 1);
x_2512 = lean_ctor_get(x_1265, 2);
x_2513 = lean_ctor_get(x_1265, 3);
x_2514 = lean_ctor_get(x_4, 1);
x_2515 = lean_ctor_get(x_4, 2);
x_2516 = lean_ctor_get(x_4, 3);
lean_dec(x_2516);
x_2517 = lean_ctor_get(x_4, 0);
lean_dec(x_2517);
x_2518 = !lean_is_exclusive(x_2428);
if (x_2518 == 0)
{
lean_object* x_2519; lean_object* x_2520; lean_object* x_2521; lean_object* x_2522; lean_object* x_2523; 
x_2519 = lean_ctor_get(x_2428, 0);
x_2520 = lean_ctor_get(x_2428, 1);
x_2521 = lean_ctor_get(x_2428, 2);
x_2522 = lean_ctor_get(x_2428, 3);
lean_ctor_set(x_2428, 3, x_2509);
lean_ctor_set(x_2428, 2, x_2508);
lean_ctor_set(x_2428, 1, x_2507);
lean_ctor_set(x_2428, 0, x_2506);
lean_ctor_set_uint8(x_2428, sizeof(void*)*4, x_2095);
lean_ctor_set(x_4, 3, x_2513);
lean_ctor_set(x_4, 2, x_2512);
lean_ctor_set(x_4, 1, x_2511);
lean_ctor_set(x_4, 0, x_2510);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2095);
lean_ctor_set(x_1265, 3, x_4);
lean_ctor_set(x_1265, 2, x_2500);
lean_ctor_set(x_1265, 1, x_2499);
lean_ctor_set(x_1265, 0, x_2428);
lean_ctor_set_uint8(x_1265, sizeof(void*)*4, x_2497);
lean_ctor_set(x_234, 3, x_1890);
lean_ctor_set(x_234, 2, x_3);
lean_ctor_set(x_234, 1, x_2);
lean_ctor_set(x_234, 0, x_1265);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_2095);
lean_ctor_set(x_1, 3, x_2522);
lean_ctor_set(x_1, 2, x_2521);
lean_ctor_set(x_1, 1, x_2520);
lean_ctor_set(x_1, 0, x_2519);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2095);
x_2523 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2523, 0, x_234);
lean_ctor_set(x_2523, 1, x_2514);
lean_ctor_set(x_2523, 2, x_2515);
lean_ctor_set(x_2523, 3, x_1);
lean_ctor_set_uint8(x_2523, sizeof(void*)*4, x_2497);
return x_2523;
}
else
{
lean_object* x_2524; lean_object* x_2525; lean_object* x_2526; lean_object* x_2527; lean_object* x_2528; lean_object* x_2529; 
x_2524 = lean_ctor_get(x_2428, 0);
x_2525 = lean_ctor_get(x_2428, 1);
x_2526 = lean_ctor_get(x_2428, 2);
x_2527 = lean_ctor_get(x_2428, 3);
lean_inc(x_2527);
lean_inc(x_2526);
lean_inc(x_2525);
lean_inc(x_2524);
lean_dec(x_2428);
x_2528 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2528, 0, x_2506);
lean_ctor_set(x_2528, 1, x_2507);
lean_ctor_set(x_2528, 2, x_2508);
lean_ctor_set(x_2528, 3, x_2509);
lean_ctor_set_uint8(x_2528, sizeof(void*)*4, x_2095);
lean_ctor_set(x_4, 3, x_2513);
lean_ctor_set(x_4, 2, x_2512);
lean_ctor_set(x_4, 1, x_2511);
lean_ctor_set(x_4, 0, x_2510);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2095);
lean_ctor_set(x_1265, 3, x_4);
lean_ctor_set(x_1265, 2, x_2500);
lean_ctor_set(x_1265, 1, x_2499);
lean_ctor_set(x_1265, 0, x_2528);
lean_ctor_set_uint8(x_1265, sizeof(void*)*4, x_2497);
lean_ctor_set(x_234, 3, x_1890);
lean_ctor_set(x_234, 2, x_3);
lean_ctor_set(x_234, 1, x_2);
lean_ctor_set(x_234, 0, x_1265);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_2095);
lean_ctor_set(x_1, 3, x_2527);
lean_ctor_set(x_1, 2, x_2526);
lean_ctor_set(x_1, 1, x_2525);
lean_ctor_set(x_1, 0, x_2524);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2095);
x_2529 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2529, 0, x_234);
lean_ctor_set(x_2529, 1, x_2514);
lean_ctor_set(x_2529, 2, x_2515);
lean_ctor_set(x_2529, 3, x_1);
lean_ctor_set_uint8(x_2529, sizeof(void*)*4, x_2497);
return x_2529;
}
}
else
{
lean_object* x_2530; lean_object* x_2531; lean_object* x_2532; lean_object* x_2533; lean_object* x_2534; lean_object* x_2535; lean_object* x_2536; lean_object* x_2537; lean_object* x_2538; lean_object* x_2539; lean_object* x_2540; lean_object* x_2541; lean_object* x_2542; lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; lean_object* x_2546; lean_object* x_2547; 
x_2530 = lean_ctor_get(x_234, 0);
x_2531 = lean_ctor_get(x_234, 1);
x_2532 = lean_ctor_get(x_234, 2);
x_2533 = lean_ctor_get(x_234, 3);
x_2534 = lean_ctor_get(x_1265, 0);
x_2535 = lean_ctor_get(x_1265, 1);
x_2536 = lean_ctor_get(x_1265, 2);
x_2537 = lean_ctor_get(x_1265, 3);
x_2538 = lean_ctor_get(x_4, 1);
x_2539 = lean_ctor_get(x_4, 2);
lean_inc(x_2539);
lean_inc(x_2538);
lean_dec(x_4);
x_2540 = lean_ctor_get(x_2428, 0);
lean_inc(x_2540);
x_2541 = lean_ctor_get(x_2428, 1);
lean_inc(x_2541);
x_2542 = lean_ctor_get(x_2428, 2);
lean_inc(x_2542);
x_2543 = lean_ctor_get(x_2428, 3);
lean_inc(x_2543);
if (lean_is_exclusive(x_2428)) {
 lean_ctor_release(x_2428, 0);
 lean_ctor_release(x_2428, 1);
 lean_ctor_release(x_2428, 2);
 lean_ctor_release(x_2428, 3);
 x_2544 = x_2428;
} else {
 lean_dec_ref(x_2428);
 x_2544 = lean_box(0);
}
if (lean_is_scalar(x_2544)) {
 x_2545 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2545 = x_2544;
}
lean_ctor_set(x_2545, 0, x_2530);
lean_ctor_set(x_2545, 1, x_2531);
lean_ctor_set(x_2545, 2, x_2532);
lean_ctor_set(x_2545, 3, x_2533);
lean_ctor_set_uint8(x_2545, sizeof(void*)*4, x_2095);
x_2546 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2546, 0, x_2534);
lean_ctor_set(x_2546, 1, x_2535);
lean_ctor_set(x_2546, 2, x_2536);
lean_ctor_set(x_2546, 3, x_2537);
lean_ctor_set_uint8(x_2546, sizeof(void*)*4, x_2095);
lean_ctor_set(x_1265, 3, x_2546);
lean_ctor_set(x_1265, 2, x_2500);
lean_ctor_set(x_1265, 1, x_2499);
lean_ctor_set(x_1265, 0, x_2545);
lean_ctor_set_uint8(x_1265, sizeof(void*)*4, x_2497);
lean_ctor_set(x_234, 3, x_1890);
lean_ctor_set(x_234, 2, x_3);
lean_ctor_set(x_234, 1, x_2);
lean_ctor_set(x_234, 0, x_1265);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_2095);
lean_ctor_set(x_1, 3, x_2543);
lean_ctor_set(x_1, 2, x_2542);
lean_ctor_set(x_1, 1, x_2541);
lean_ctor_set(x_1, 0, x_2540);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2095);
x_2547 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2547, 0, x_234);
lean_ctor_set(x_2547, 1, x_2538);
lean_ctor_set(x_2547, 2, x_2539);
lean_ctor_set(x_2547, 3, x_1);
lean_ctor_set_uint8(x_2547, sizeof(void*)*4, x_2497);
return x_2547;
}
}
else
{
lean_object* x_2548; lean_object* x_2549; lean_object* x_2550; lean_object* x_2551; lean_object* x_2552; lean_object* x_2553; lean_object* x_2554; lean_object* x_2555; lean_object* x_2556; lean_object* x_2557; lean_object* x_2558; lean_object* x_2559; lean_object* x_2560; lean_object* x_2561; lean_object* x_2562; lean_object* x_2563; lean_object* x_2564; lean_object* x_2565; lean_object* x_2566; lean_object* x_2567; 
x_2548 = lean_ctor_get(x_234, 0);
x_2549 = lean_ctor_get(x_234, 1);
x_2550 = lean_ctor_get(x_234, 2);
x_2551 = lean_ctor_get(x_234, 3);
x_2552 = lean_ctor_get(x_1265, 0);
x_2553 = lean_ctor_get(x_1265, 1);
x_2554 = lean_ctor_get(x_1265, 2);
x_2555 = lean_ctor_get(x_1265, 3);
lean_inc(x_2555);
lean_inc(x_2554);
lean_inc(x_2553);
lean_inc(x_2552);
lean_dec(x_1265);
x_2556 = lean_ctor_get(x_4, 1);
lean_inc(x_2556);
x_2557 = lean_ctor_get(x_4, 2);
lean_inc(x_2557);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_2558 = x_4;
} else {
 lean_dec_ref(x_4);
 x_2558 = lean_box(0);
}
x_2559 = lean_ctor_get(x_2428, 0);
lean_inc(x_2559);
x_2560 = lean_ctor_get(x_2428, 1);
lean_inc(x_2560);
x_2561 = lean_ctor_get(x_2428, 2);
lean_inc(x_2561);
x_2562 = lean_ctor_get(x_2428, 3);
lean_inc(x_2562);
if (lean_is_exclusive(x_2428)) {
 lean_ctor_release(x_2428, 0);
 lean_ctor_release(x_2428, 1);
 lean_ctor_release(x_2428, 2);
 lean_ctor_release(x_2428, 3);
 x_2563 = x_2428;
} else {
 lean_dec_ref(x_2428);
 x_2563 = lean_box(0);
}
if (lean_is_scalar(x_2563)) {
 x_2564 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2564 = x_2563;
}
lean_ctor_set(x_2564, 0, x_2548);
lean_ctor_set(x_2564, 1, x_2549);
lean_ctor_set(x_2564, 2, x_2550);
lean_ctor_set(x_2564, 3, x_2551);
lean_ctor_set_uint8(x_2564, sizeof(void*)*4, x_2095);
if (lean_is_scalar(x_2558)) {
 x_2565 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2565 = x_2558;
}
lean_ctor_set(x_2565, 0, x_2552);
lean_ctor_set(x_2565, 1, x_2553);
lean_ctor_set(x_2565, 2, x_2554);
lean_ctor_set(x_2565, 3, x_2555);
lean_ctor_set_uint8(x_2565, sizeof(void*)*4, x_2095);
x_2566 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2566, 0, x_2564);
lean_ctor_set(x_2566, 1, x_2499);
lean_ctor_set(x_2566, 2, x_2500);
lean_ctor_set(x_2566, 3, x_2565);
lean_ctor_set_uint8(x_2566, sizeof(void*)*4, x_2497);
lean_ctor_set(x_234, 3, x_1890);
lean_ctor_set(x_234, 2, x_3);
lean_ctor_set(x_234, 1, x_2);
lean_ctor_set(x_234, 0, x_2566);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_2095);
lean_ctor_set(x_1, 3, x_2562);
lean_ctor_set(x_1, 2, x_2561);
lean_ctor_set(x_1, 1, x_2560);
lean_ctor_set(x_1, 0, x_2559);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2095);
x_2567 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2567, 0, x_234);
lean_ctor_set(x_2567, 1, x_2556);
lean_ctor_set(x_2567, 2, x_2557);
lean_ctor_set(x_2567, 3, x_1);
lean_ctor_set_uint8(x_2567, sizeof(void*)*4, x_2497);
return x_2567;
}
}
else
{
lean_object* x_2568; lean_object* x_2569; lean_object* x_2570; lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; lean_object* x_2574; lean_object* x_2575; lean_object* x_2576; lean_object* x_2577; lean_object* x_2578; lean_object* x_2579; lean_object* x_2580; lean_object* x_2581; lean_object* x_2582; lean_object* x_2583; lean_object* x_2584; lean_object* x_2585; lean_object* x_2586; lean_object* x_2587; lean_object* x_2588; lean_object* x_2589; 
x_2568 = lean_ctor_get(x_234, 0);
x_2569 = lean_ctor_get(x_234, 1);
x_2570 = lean_ctor_get(x_234, 2);
x_2571 = lean_ctor_get(x_234, 3);
lean_inc(x_2571);
lean_inc(x_2570);
lean_inc(x_2569);
lean_inc(x_2568);
lean_dec(x_234);
x_2572 = lean_ctor_get(x_1265, 0);
lean_inc(x_2572);
x_2573 = lean_ctor_get(x_1265, 1);
lean_inc(x_2573);
x_2574 = lean_ctor_get(x_1265, 2);
lean_inc(x_2574);
x_2575 = lean_ctor_get(x_1265, 3);
lean_inc(x_2575);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2576 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2576 = lean_box(0);
}
x_2577 = lean_ctor_get(x_4, 1);
lean_inc(x_2577);
x_2578 = lean_ctor_get(x_4, 2);
lean_inc(x_2578);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_2579 = x_4;
} else {
 lean_dec_ref(x_4);
 x_2579 = lean_box(0);
}
x_2580 = lean_ctor_get(x_2428, 0);
lean_inc(x_2580);
x_2581 = lean_ctor_get(x_2428, 1);
lean_inc(x_2581);
x_2582 = lean_ctor_get(x_2428, 2);
lean_inc(x_2582);
x_2583 = lean_ctor_get(x_2428, 3);
lean_inc(x_2583);
if (lean_is_exclusive(x_2428)) {
 lean_ctor_release(x_2428, 0);
 lean_ctor_release(x_2428, 1);
 lean_ctor_release(x_2428, 2);
 lean_ctor_release(x_2428, 3);
 x_2584 = x_2428;
} else {
 lean_dec_ref(x_2428);
 x_2584 = lean_box(0);
}
if (lean_is_scalar(x_2584)) {
 x_2585 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2585 = x_2584;
}
lean_ctor_set(x_2585, 0, x_2568);
lean_ctor_set(x_2585, 1, x_2569);
lean_ctor_set(x_2585, 2, x_2570);
lean_ctor_set(x_2585, 3, x_2571);
lean_ctor_set_uint8(x_2585, sizeof(void*)*4, x_2095);
if (lean_is_scalar(x_2579)) {
 x_2586 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2586 = x_2579;
}
lean_ctor_set(x_2586, 0, x_2572);
lean_ctor_set(x_2586, 1, x_2573);
lean_ctor_set(x_2586, 2, x_2574);
lean_ctor_set(x_2586, 3, x_2575);
lean_ctor_set_uint8(x_2586, sizeof(void*)*4, x_2095);
if (lean_is_scalar(x_2576)) {
 x_2587 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2587 = x_2576;
}
lean_ctor_set(x_2587, 0, x_2585);
lean_ctor_set(x_2587, 1, x_2499);
lean_ctor_set(x_2587, 2, x_2500);
lean_ctor_set(x_2587, 3, x_2586);
lean_ctor_set_uint8(x_2587, sizeof(void*)*4, x_2497);
x_2588 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2588, 0, x_2587);
lean_ctor_set(x_2588, 1, x_2);
lean_ctor_set(x_2588, 2, x_3);
lean_ctor_set(x_2588, 3, x_1890);
lean_ctor_set_uint8(x_2588, sizeof(void*)*4, x_2095);
lean_ctor_set(x_1, 3, x_2583);
lean_ctor_set(x_1, 2, x_2582);
lean_ctor_set(x_1, 1, x_2581);
lean_ctor_set(x_1, 0, x_2580);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2095);
x_2589 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2589, 0, x_2588);
lean_ctor_set(x_2589, 1, x_2577);
lean_ctor_set(x_2589, 2, x_2578);
lean_ctor_set(x_2589, 3, x_1);
lean_ctor_set_uint8(x_2589, sizeof(void*)*4, x_2497);
return x_2589;
}
}
else
{
lean_object* x_2590; lean_object* x_2591; lean_object* x_2592; lean_object* x_2593; lean_object* x_2594; lean_object* x_2595; lean_object* x_2596; lean_object* x_2597; lean_object* x_2598; lean_object* x_2599; lean_object* x_2600; lean_object* x_2601; lean_object* x_2602; lean_object* x_2603; lean_object* x_2604; lean_object* x_2605; lean_object* x_2606; lean_object* x_2607; lean_object* x_2608; lean_object* x_2609; lean_object* x_2610; lean_object* x_2611; lean_object* x_2612; lean_object* x_2613; lean_object* x_2614; lean_object* x_2615; 
x_2590 = lean_ctor_get(x_1, 1);
x_2591 = lean_ctor_get(x_1, 2);
lean_inc(x_2591);
lean_inc(x_2590);
lean_dec(x_1);
x_2592 = lean_ctor_get(x_234, 0);
lean_inc(x_2592);
x_2593 = lean_ctor_get(x_234, 1);
lean_inc(x_2593);
x_2594 = lean_ctor_get(x_234, 2);
lean_inc(x_2594);
x_2595 = lean_ctor_get(x_234, 3);
lean_inc(x_2595);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_2596 = x_234;
} else {
 lean_dec_ref(x_234);
 x_2596 = lean_box(0);
}
x_2597 = lean_ctor_get(x_1265, 0);
lean_inc(x_2597);
x_2598 = lean_ctor_get(x_1265, 1);
lean_inc(x_2598);
x_2599 = lean_ctor_get(x_1265, 2);
lean_inc(x_2599);
x_2600 = lean_ctor_get(x_1265, 3);
lean_inc(x_2600);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2601 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2601 = lean_box(0);
}
x_2602 = lean_ctor_get(x_4, 1);
lean_inc(x_2602);
x_2603 = lean_ctor_get(x_4, 2);
lean_inc(x_2603);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_2604 = x_4;
} else {
 lean_dec_ref(x_4);
 x_2604 = lean_box(0);
}
x_2605 = lean_ctor_get(x_2428, 0);
lean_inc(x_2605);
x_2606 = lean_ctor_get(x_2428, 1);
lean_inc(x_2606);
x_2607 = lean_ctor_get(x_2428, 2);
lean_inc(x_2607);
x_2608 = lean_ctor_get(x_2428, 3);
lean_inc(x_2608);
if (lean_is_exclusive(x_2428)) {
 lean_ctor_release(x_2428, 0);
 lean_ctor_release(x_2428, 1);
 lean_ctor_release(x_2428, 2);
 lean_ctor_release(x_2428, 3);
 x_2609 = x_2428;
} else {
 lean_dec_ref(x_2428);
 x_2609 = lean_box(0);
}
if (lean_is_scalar(x_2609)) {
 x_2610 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2610 = x_2609;
}
lean_ctor_set(x_2610, 0, x_2592);
lean_ctor_set(x_2610, 1, x_2593);
lean_ctor_set(x_2610, 2, x_2594);
lean_ctor_set(x_2610, 3, x_2595);
lean_ctor_set_uint8(x_2610, sizeof(void*)*4, x_2095);
if (lean_is_scalar(x_2604)) {
 x_2611 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2611 = x_2604;
}
lean_ctor_set(x_2611, 0, x_2597);
lean_ctor_set(x_2611, 1, x_2598);
lean_ctor_set(x_2611, 2, x_2599);
lean_ctor_set(x_2611, 3, x_2600);
lean_ctor_set_uint8(x_2611, sizeof(void*)*4, x_2095);
if (lean_is_scalar(x_2601)) {
 x_2612 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2612 = x_2601;
}
lean_ctor_set(x_2612, 0, x_2610);
lean_ctor_set(x_2612, 1, x_2590);
lean_ctor_set(x_2612, 2, x_2591);
lean_ctor_set(x_2612, 3, x_2611);
lean_ctor_set_uint8(x_2612, sizeof(void*)*4, x_2497);
if (lean_is_scalar(x_2596)) {
 x_2613 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2613 = x_2596;
}
lean_ctor_set(x_2613, 0, x_2612);
lean_ctor_set(x_2613, 1, x_2);
lean_ctor_set(x_2613, 2, x_3);
lean_ctor_set(x_2613, 3, x_1890);
lean_ctor_set_uint8(x_2613, sizeof(void*)*4, x_2095);
x_2614 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2614, 0, x_2605);
lean_ctor_set(x_2614, 1, x_2606);
lean_ctor_set(x_2614, 2, x_2607);
lean_ctor_set(x_2614, 3, x_2608);
lean_ctor_set_uint8(x_2614, sizeof(void*)*4, x_2095);
x_2615 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2615, 0, x_2613);
lean_ctor_set(x_2615, 1, x_2602);
lean_ctor_set(x_2615, 2, x_2603);
lean_ctor_set(x_2615, 3, x_2614);
lean_ctor_set_uint8(x_2615, sizeof(void*)*4, x_2497);
return x_2615;
}
}
else
{
uint8_t x_2616; 
x_2616 = !lean_is_exclusive(x_1);
if (x_2616 == 0)
{
lean_object* x_2617; lean_object* x_2618; lean_object* x_2619; lean_object* x_2620; uint8_t x_2621; 
x_2617 = lean_ctor_get(x_1, 1);
x_2618 = lean_ctor_get(x_1, 2);
x_2619 = lean_ctor_get(x_1, 3);
lean_dec(x_2619);
x_2620 = lean_ctor_get(x_1, 0);
lean_dec(x_2620);
x_2621 = !lean_is_exclusive(x_234);
if (x_2621 == 0)
{
uint8_t x_2622; 
x_2622 = !lean_is_exclusive(x_1265);
if (x_2622 == 0)
{
uint8_t x_2623; 
x_2623 = !lean_is_exclusive(x_4);
if (x_2623 == 0)
{
lean_object* x_2624; lean_object* x_2625; lean_object* x_2626; lean_object* x_2627; lean_object* x_2628; lean_object* x_2629; lean_object* x_2630; lean_object* x_2631; lean_object* x_2632; lean_object* x_2633; lean_object* x_2634; lean_object* x_2635; uint8_t x_2636; 
x_2624 = lean_ctor_get(x_234, 0);
x_2625 = lean_ctor_get(x_234, 1);
x_2626 = lean_ctor_get(x_234, 2);
x_2627 = lean_ctor_get(x_234, 3);
x_2628 = lean_ctor_get(x_1265, 0);
x_2629 = lean_ctor_get(x_1265, 1);
x_2630 = lean_ctor_get(x_1265, 2);
x_2631 = lean_ctor_get(x_1265, 3);
x_2632 = lean_ctor_get(x_4, 1);
x_2633 = lean_ctor_get(x_4, 2);
x_2634 = lean_ctor_get(x_4, 3);
lean_dec(x_2634);
x_2635 = lean_ctor_get(x_4, 0);
lean_dec(x_2635);
x_2636 = !lean_is_exclusive(x_1890);
if (x_2636 == 0)
{
lean_object* x_2637; lean_object* x_2638; lean_object* x_2639; lean_object* x_2640; lean_object* x_2641; 
x_2637 = lean_ctor_get(x_1890, 0);
x_2638 = lean_ctor_get(x_1890, 1);
x_2639 = lean_ctor_get(x_1890, 2);
x_2640 = lean_ctor_get(x_1890, 3);
lean_ctor_set(x_1890, 3, x_2627);
lean_ctor_set(x_1890, 2, x_2626);
lean_ctor_set(x_1890, 1, x_2625);
lean_ctor_set(x_1890, 0, x_2624);
lean_ctor_set_uint8(x_1890, sizeof(void*)*4, x_2497);
lean_ctor_set(x_4, 3, x_2631);
lean_ctor_set(x_4, 2, x_2630);
lean_ctor_set(x_4, 1, x_2629);
lean_ctor_set(x_4, 0, x_2628);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2497);
lean_ctor_set(x_1265, 3, x_4);
lean_ctor_set(x_1265, 2, x_2618);
lean_ctor_set(x_1265, 1, x_2617);
lean_ctor_set(x_1265, 0, x_1890);
lean_ctor_set_uint8(x_1265, sizeof(void*)*4, x_1889);
lean_ctor_set(x_234, 3, x_2640);
lean_ctor_set(x_234, 2, x_2639);
lean_ctor_set(x_234, 1, x_2638);
lean_ctor_set(x_234, 0, x_2637);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_2497);
lean_ctor_set(x_1, 3, x_2428);
lean_ctor_set(x_1, 2, x_2633);
lean_ctor_set(x_1, 1, x_2632);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_2641 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2641, 0, x_1265);
lean_ctor_set(x_2641, 1, x_2);
lean_ctor_set(x_2641, 2, x_3);
lean_ctor_set(x_2641, 3, x_1);
lean_ctor_set_uint8(x_2641, sizeof(void*)*4, x_2497);
return x_2641;
}
else
{
lean_object* x_2642; lean_object* x_2643; lean_object* x_2644; lean_object* x_2645; lean_object* x_2646; lean_object* x_2647; 
x_2642 = lean_ctor_get(x_1890, 0);
x_2643 = lean_ctor_get(x_1890, 1);
x_2644 = lean_ctor_get(x_1890, 2);
x_2645 = lean_ctor_get(x_1890, 3);
lean_inc(x_2645);
lean_inc(x_2644);
lean_inc(x_2643);
lean_inc(x_2642);
lean_dec(x_1890);
x_2646 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2646, 0, x_2624);
lean_ctor_set(x_2646, 1, x_2625);
lean_ctor_set(x_2646, 2, x_2626);
lean_ctor_set(x_2646, 3, x_2627);
lean_ctor_set_uint8(x_2646, sizeof(void*)*4, x_2497);
lean_ctor_set(x_4, 3, x_2631);
lean_ctor_set(x_4, 2, x_2630);
lean_ctor_set(x_4, 1, x_2629);
lean_ctor_set(x_4, 0, x_2628);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2497);
lean_ctor_set(x_1265, 3, x_4);
lean_ctor_set(x_1265, 2, x_2618);
lean_ctor_set(x_1265, 1, x_2617);
lean_ctor_set(x_1265, 0, x_2646);
lean_ctor_set_uint8(x_1265, sizeof(void*)*4, x_1889);
lean_ctor_set(x_234, 3, x_2645);
lean_ctor_set(x_234, 2, x_2644);
lean_ctor_set(x_234, 1, x_2643);
lean_ctor_set(x_234, 0, x_2642);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_2497);
lean_ctor_set(x_1, 3, x_2428);
lean_ctor_set(x_1, 2, x_2633);
lean_ctor_set(x_1, 1, x_2632);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_2647 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2647, 0, x_1265);
lean_ctor_set(x_2647, 1, x_2);
lean_ctor_set(x_2647, 2, x_3);
lean_ctor_set(x_2647, 3, x_1);
lean_ctor_set_uint8(x_2647, sizeof(void*)*4, x_2497);
return x_2647;
}
}
else
{
lean_object* x_2648; lean_object* x_2649; lean_object* x_2650; lean_object* x_2651; lean_object* x_2652; lean_object* x_2653; lean_object* x_2654; lean_object* x_2655; lean_object* x_2656; lean_object* x_2657; lean_object* x_2658; lean_object* x_2659; lean_object* x_2660; lean_object* x_2661; lean_object* x_2662; lean_object* x_2663; lean_object* x_2664; lean_object* x_2665; 
x_2648 = lean_ctor_get(x_234, 0);
x_2649 = lean_ctor_get(x_234, 1);
x_2650 = lean_ctor_get(x_234, 2);
x_2651 = lean_ctor_get(x_234, 3);
x_2652 = lean_ctor_get(x_1265, 0);
x_2653 = lean_ctor_get(x_1265, 1);
x_2654 = lean_ctor_get(x_1265, 2);
x_2655 = lean_ctor_get(x_1265, 3);
x_2656 = lean_ctor_get(x_4, 1);
x_2657 = lean_ctor_get(x_4, 2);
lean_inc(x_2657);
lean_inc(x_2656);
lean_dec(x_4);
x_2658 = lean_ctor_get(x_1890, 0);
lean_inc(x_2658);
x_2659 = lean_ctor_get(x_1890, 1);
lean_inc(x_2659);
x_2660 = lean_ctor_get(x_1890, 2);
lean_inc(x_2660);
x_2661 = lean_ctor_get(x_1890, 3);
lean_inc(x_2661);
if (lean_is_exclusive(x_1890)) {
 lean_ctor_release(x_1890, 0);
 lean_ctor_release(x_1890, 1);
 lean_ctor_release(x_1890, 2);
 lean_ctor_release(x_1890, 3);
 x_2662 = x_1890;
} else {
 lean_dec_ref(x_1890);
 x_2662 = lean_box(0);
}
if (lean_is_scalar(x_2662)) {
 x_2663 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2663 = x_2662;
}
lean_ctor_set(x_2663, 0, x_2648);
lean_ctor_set(x_2663, 1, x_2649);
lean_ctor_set(x_2663, 2, x_2650);
lean_ctor_set(x_2663, 3, x_2651);
lean_ctor_set_uint8(x_2663, sizeof(void*)*4, x_2497);
x_2664 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2664, 0, x_2652);
lean_ctor_set(x_2664, 1, x_2653);
lean_ctor_set(x_2664, 2, x_2654);
lean_ctor_set(x_2664, 3, x_2655);
lean_ctor_set_uint8(x_2664, sizeof(void*)*4, x_2497);
lean_ctor_set(x_1265, 3, x_2664);
lean_ctor_set(x_1265, 2, x_2618);
lean_ctor_set(x_1265, 1, x_2617);
lean_ctor_set(x_1265, 0, x_2663);
lean_ctor_set_uint8(x_1265, sizeof(void*)*4, x_1889);
lean_ctor_set(x_234, 3, x_2661);
lean_ctor_set(x_234, 2, x_2660);
lean_ctor_set(x_234, 1, x_2659);
lean_ctor_set(x_234, 0, x_2658);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_2497);
lean_ctor_set(x_1, 3, x_2428);
lean_ctor_set(x_1, 2, x_2657);
lean_ctor_set(x_1, 1, x_2656);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_2665 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2665, 0, x_1265);
lean_ctor_set(x_2665, 1, x_2);
lean_ctor_set(x_2665, 2, x_3);
lean_ctor_set(x_2665, 3, x_1);
lean_ctor_set_uint8(x_2665, sizeof(void*)*4, x_2497);
return x_2665;
}
}
else
{
lean_object* x_2666; lean_object* x_2667; lean_object* x_2668; lean_object* x_2669; lean_object* x_2670; lean_object* x_2671; lean_object* x_2672; lean_object* x_2673; lean_object* x_2674; lean_object* x_2675; lean_object* x_2676; lean_object* x_2677; lean_object* x_2678; lean_object* x_2679; lean_object* x_2680; lean_object* x_2681; lean_object* x_2682; lean_object* x_2683; lean_object* x_2684; lean_object* x_2685; 
x_2666 = lean_ctor_get(x_234, 0);
x_2667 = lean_ctor_get(x_234, 1);
x_2668 = lean_ctor_get(x_234, 2);
x_2669 = lean_ctor_get(x_234, 3);
x_2670 = lean_ctor_get(x_1265, 0);
x_2671 = lean_ctor_get(x_1265, 1);
x_2672 = lean_ctor_get(x_1265, 2);
x_2673 = lean_ctor_get(x_1265, 3);
lean_inc(x_2673);
lean_inc(x_2672);
lean_inc(x_2671);
lean_inc(x_2670);
lean_dec(x_1265);
x_2674 = lean_ctor_get(x_4, 1);
lean_inc(x_2674);
x_2675 = lean_ctor_get(x_4, 2);
lean_inc(x_2675);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_2676 = x_4;
} else {
 lean_dec_ref(x_4);
 x_2676 = lean_box(0);
}
x_2677 = lean_ctor_get(x_1890, 0);
lean_inc(x_2677);
x_2678 = lean_ctor_get(x_1890, 1);
lean_inc(x_2678);
x_2679 = lean_ctor_get(x_1890, 2);
lean_inc(x_2679);
x_2680 = lean_ctor_get(x_1890, 3);
lean_inc(x_2680);
if (lean_is_exclusive(x_1890)) {
 lean_ctor_release(x_1890, 0);
 lean_ctor_release(x_1890, 1);
 lean_ctor_release(x_1890, 2);
 lean_ctor_release(x_1890, 3);
 x_2681 = x_1890;
} else {
 lean_dec_ref(x_1890);
 x_2681 = lean_box(0);
}
if (lean_is_scalar(x_2681)) {
 x_2682 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2682 = x_2681;
}
lean_ctor_set(x_2682, 0, x_2666);
lean_ctor_set(x_2682, 1, x_2667);
lean_ctor_set(x_2682, 2, x_2668);
lean_ctor_set(x_2682, 3, x_2669);
lean_ctor_set_uint8(x_2682, sizeof(void*)*4, x_2497);
if (lean_is_scalar(x_2676)) {
 x_2683 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2683 = x_2676;
}
lean_ctor_set(x_2683, 0, x_2670);
lean_ctor_set(x_2683, 1, x_2671);
lean_ctor_set(x_2683, 2, x_2672);
lean_ctor_set(x_2683, 3, x_2673);
lean_ctor_set_uint8(x_2683, sizeof(void*)*4, x_2497);
x_2684 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2684, 0, x_2682);
lean_ctor_set(x_2684, 1, x_2617);
lean_ctor_set(x_2684, 2, x_2618);
lean_ctor_set(x_2684, 3, x_2683);
lean_ctor_set_uint8(x_2684, sizeof(void*)*4, x_1889);
lean_ctor_set(x_234, 3, x_2680);
lean_ctor_set(x_234, 2, x_2679);
lean_ctor_set(x_234, 1, x_2678);
lean_ctor_set(x_234, 0, x_2677);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_2497);
lean_ctor_set(x_1, 3, x_2428);
lean_ctor_set(x_1, 2, x_2675);
lean_ctor_set(x_1, 1, x_2674);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_2685 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2685, 0, x_2684);
lean_ctor_set(x_2685, 1, x_2);
lean_ctor_set(x_2685, 2, x_3);
lean_ctor_set(x_2685, 3, x_1);
lean_ctor_set_uint8(x_2685, sizeof(void*)*4, x_2497);
return x_2685;
}
}
else
{
lean_object* x_2686; lean_object* x_2687; lean_object* x_2688; lean_object* x_2689; lean_object* x_2690; lean_object* x_2691; lean_object* x_2692; lean_object* x_2693; lean_object* x_2694; lean_object* x_2695; lean_object* x_2696; lean_object* x_2697; lean_object* x_2698; lean_object* x_2699; lean_object* x_2700; lean_object* x_2701; lean_object* x_2702; lean_object* x_2703; lean_object* x_2704; lean_object* x_2705; lean_object* x_2706; lean_object* x_2707; 
x_2686 = lean_ctor_get(x_234, 0);
x_2687 = lean_ctor_get(x_234, 1);
x_2688 = lean_ctor_get(x_234, 2);
x_2689 = lean_ctor_get(x_234, 3);
lean_inc(x_2689);
lean_inc(x_2688);
lean_inc(x_2687);
lean_inc(x_2686);
lean_dec(x_234);
x_2690 = lean_ctor_get(x_1265, 0);
lean_inc(x_2690);
x_2691 = lean_ctor_get(x_1265, 1);
lean_inc(x_2691);
x_2692 = lean_ctor_get(x_1265, 2);
lean_inc(x_2692);
x_2693 = lean_ctor_get(x_1265, 3);
lean_inc(x_2693);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2694 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2694 = lean_box(0);
}
x_2695 = lean_ctor_get(x_4, 1);
lean_inc(x_2695);
x_2696 = lean_ctor_get(x_4, 2);
lean_inc(x_2696);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_2697 = x_4;
} else {
 lean_dec_ref(x_4);
 x_2697 = lean_box(0);
}
x_2698 = lean_ctor_get(x_1890, 0);
lean_inc(x_2698);
x_2699 = lean_ctor_get(x_1890, 1);
lean_inc(x_2699);
x_2700 = lean_ctor_get(x_1890, 2);
lean_inc(x_2700);
x_2701 = lean_ctor_get(x_1890, 3);
lean_inc(x_2701);
if (lean_is_exclusive(x_1890)) {
 lean_ctor_release(x_1890, 0);
 lean_ctor_release(x_1890, 1);
 lean_ctor_release(x_1890, 2);
 lean_ctor_release(x_1890, 3);
 x_2702 = x_1890;
} else {
 lean_dec_ref(x_1890);
 x_2702 = lean_box(0);
}
if (lean_is_scalar(x_2702)) {
 x_2703 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2703 = x_2702;
}
lean_ctor_set(x_2703, 0, x_2686);
lean_ctor_set(x_2703, 1, x_2687);
lean_ctor_set(x_2703, 2, x_2688);
lean_ctor_set(x_2703, 3, x_2689);
lean_ctor_set_uint8(x_2703, sizeof(void*)*4, x_2497);
if (lean_is_scalar(x_2697)) {
 x_2704 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2704 = x_2697;
}
lean_ctor_set(x_2704, 0, x_2690);
lean_ctor_set(x_2704, 1, x_2691);
lean_ctor_set(x_2704, 2, x_2692);
lean_ctor_set(x_2704, 3, x_2693);
lean_ctor_set_uint8(x_2704, sizeof(void*)*4, x_2497);
if (lean_is_scalar(x_2694)) {
 x_2705 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2705 = x_2694;
}
lean_ctor_set(x_2705, 0, x_2703);
lean_ctor_set(x_2705, 1, x_2617);
lean_ctor_set(x_2705, 2, x_2618);
lean_ctor_set(x_2705, 3, x_2704);
lean_ctor_set_uint8(x_2705, sizeof(void*)*4, x_1889);
x_2706 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2706, 0, x_2698);
lean_ctor_set(x_2706, 1, x_2699);
lean_ctor_set(x_2706, 2, x_2700);
lean_ctor_set(x_2706, 3, x_2701);
lean_ctor_set_uint8(x_2706, sizeof(void*)*4, x_2497);
lean_ctor_set(x_1, 3, x_2428);
lean_ctor_set(x_1, 2, x_2696);
lean_ctor_set(x_1, 1, x_2695);
lean_ctor_set(x_1, 0, x_2706);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_1889);
x_2707 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2707, 0, x_2705);
lean_ctor_set(x_2707, 1, x_2);
lean_ctor_set(x_2707, 2, x_3);
lean_ctor_set(x_2707, 3, x_1);
lean_ctor_set_uint8(x_2707, sizeof(void*)*4, x_2497);
return x_2707;
}
}
else
{
lean_object* x_2708; lean_object* x_2709; lean_object* x_2710; lean_object* x_2711; lean_object* x_2712; lean_object* x_2713; lean_object* x_2714; lean_object* x_2715; lean_object* x_2716; lean_object* x_2717; lean_object* x_2718; lean_object* x_2719; lean_object* x_2720; lean_object* x_2721; lean_object* x_2722; lean_object* x_2723; lean_object* x_2724; lean_object* x_2725; lean_object* x_2726; lean_object* x_2727; lean_object* x_2728; lean_object* x_2729; lean_object* x_2730; lean_object* x_2731; lean_object* x_2732; lean_object* x_2733; 
x_2708 = lean_ctor_get(x_1, 1);
x_2709 = lean_ctor_get(x_1, 2);
lean_inc(x_2709);
lean_inc(x_2708);
lean_dec(x_1);
x_2710 = lean_ctor_get(x_234, 0);
lean_inc(x_2710);
x_2711 = lean_ctor_get(x_234, 1);
lean_inc(x_2711);
x_2712 = lean_ctor_get(x_234, 2);
lean_inc(x_2712);
x_2713 = lean_ctor_get(x_234, 3);
lean_inc(x_2713);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_2714 = x_234;
} else {
 lean_dec_ref(x_234);
 x_2714 = lean_box(0);
}
x_2715 = lean_ctor_get(x_1265, 0);
lean_inc(x_2715);
x_2716 = lean_ctor_get(x_1265, 1);
lean_inc(x_2716);
x_2717 = lean_ctor_get(x_1265, 2);
lean_inc(x_2717);
x_2718 = lean_ctor_get(x_1265, 3);
lean_inc(x_2718);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2719 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2719 = lean_box(0);
}
x_2720 = lean_ctor_get(x_4, 1);
lean_inc(x_2720);
x_2721 = lean_ctor_get(x_4, 2);
lean_inc(x_2721);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_2722 = x_4;
} else {
 lean_dec_ref(x_4);
 x_2722 = lean_box(0);
}
x_2723 = lean_ctor_get(x_1890, 0);
lean_inc(x_2723);
x_2724 = lean_ctor_get(x_1890, 1);
lean_inc(x_2724);
x_2725 = lean_ctor_get(x_1890, 2);
lean_inc(x_2725);
x_2726 = lean_ctor_get(x_1890, 3);
lean_inc(x_2726);
if (lean_is_exclusive(x_1890)) {
 lean_ctor_release(x_1890, 0);
 lean_ctor_release(x_1890, 1);
 lean_ctor_release(x_1890, 2);
 lean_ctor_release(x_1890, 3);
 x_2727 = x_1890;
} else {
 lean_dec_ref(x_1890);
 x_2727 = lean_box(0);
}
if (lean_is_scalar(x_2727)) {
 x_2728 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2728 = x_2727;
}
lean_ctor_set(x_2728, 0, x_2710);
lean_ctor_set(x_2728, 1, x_2711);
lean_ctor_set(x_2728, 2, x_2712);
lean_ctor_set(x_2728, 3, x_2713);
lean_ctor_set_uint8(x_2728, sizeof(void*)*4, x_2497);
if (lean_is_scalar(x_2722)) {
 x_2729 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2729 = x_2722;
}
lean_ctor_set(x_2729, 0, x_2715);
lean_ctor_set(x_2729, 1, x_2716);
lean_ctor_set(x_2729, 2, x_2717);
lean_ctor_set(x_2729, 3, x_2718);
lean_ctor_set_uint8(x_2729, sizeof(void*)*4, x_2497);
if (lean_is_scalar(x_2719)) {
 x_2730 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2730 = x_2719;
}
lean_ctor_set(x_2730, 0, x_2728);
lean_ctor_set(x_2730, 1, x_2708);
lean_ctor_set(x_2730, 2, x_2709);
lean_ctor_set(x_2730, 3, x_2729);
lean_ctor_set_uint8(x_2730, sizeof(void*)*4, x_1889);
if (lean_is_scalar(x_2714)) {
 x_2731 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2731 = x_2714;
}
lean_ctor_set(x_2731, 0, x_2723);
lean_ctor_set(x_2731, 1, x_2724);
lean_ctor_set(x_2731, 2, x_2725);
lean_ctor_set(x_2731, 3, x_2726);
lean_ctor_set_uint8(x_2731, sizeof(void*)*4, x_2497);
x_2732 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2732, 0, x_2731);
lean_ctor_set(x_2732, 1, x_2720);
lean_ctor_set(x_2732, 2, x_2721);
lean_ctor_set(x_2732, 3, x_2428);
lean_ctor_set_uint8(x_2732, sizeof(void*)*4, x_1889);
x_2733 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2733, 0, x_2730);
lean_ctor_set(x_2733, 1, x_2);
lean_ctor_set(x_2733, 2, x_3);
lean_ctor_set(x_2733, 3, x_2732);
lean_ctor_set_uint8(x_2733, sizeof(void*)*4, x_2497);
return x_2733;
}
}
}
}
}
}
else
{
uint8_t x_2734; 
x_2734 = !lean_is_exclusive(x_1);
if (x_2734 == 0)
{
lean_object* x_2735; lean_object* x_2736; uint8_t x_2737; 
x_2735 = lean_ctor_get(x_1, 3);
lean_dec(x_2735);
x_2736 = lean_ctor_get(x_1, 0);
lean_dec(x_2736);
x_2737 = !lean_is_exclusive(x_234);
if (x_2737 == 0)
{
uint8_t x_2738; 
x_2738 = !lean_is_exclusive(x_1265);
if (x_2738 == 0)
{
lean_object* x_2739; lean_object* x_2740; lean_object* x_2741; lean_object* x_2742; lean_object* x_2743; lean_object* x_2744; lean_object* x_2745; lean_object* x_2746; lean_object* x_2747; 
x_2739 = lean_ctor_get(x_234, 0);
x_2740 = lean_ctor_get(x_234, 1);
x_2741 = lean_ctor_get(x_234, 2);
x_2742 = lean_ctor_get(x_234, 3);
x_2743 = lean_ctor_get(x_1265, 0);
x_2744 = lean_ctor_get(x_1265, 1);
x_2745 = lean_ctor_get(x_1265, 2);
x_2746 = lean_ctor_get(x_1265, 3);
lean_ctor_set(x_1265, 3, x_2742);
lean_ctor_set(x_1265, 2, x_2741);
lean_ctor_set(x_1265, 1, x_2740);
lean_ctor_set(x_1265, 0, x_2739);
lean_ctor_set_uint8(x_1265, sizeof(void*)*4, x_1889);
lean_ctor_set(x_234, 3, x_2746);
lean_ctor_set(x_234, 2, x_2745);
lean_ctor_set(x_234, 1, x_2744);
lean_ctor_set(x_234, 0, x_2743);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 0, x_1265);
x_2747 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2747, 0, x_1);
lean_ctor_set(x_2747, 1, x_2);
lean_ctor_set(x_2747, 2, x_3);
lean_ctor_set(x_2747, 3, x_4);
lean_ctor_set_uint8(x_2747, sizeof(void*)*4, x_1889);
return x_2747;
}
else
{
lean_object* x_2748; lean_object* x_2749; lean_object* x_2750; lean_object* x_2751; lean_object* x_2752; lean_object* x_2753; lean_object* x_2754; lean_object* x_2755; lean_object* x_2756; lean_object* x_2757; 
x_2748 = lean_ctor_get(x_234, 0);
x_2749 = lean_ctor_get(x_234, 1);
x_2750 = lean_ctor_get(x_234, 2);
x_2751 = lean_ctor_get(x_234, 3);
x_2752 = lean_ctor_get(x_1265, 0);
x_2753 = lean_ctor_get(x_1265, 1);
x_2754 = lean_ctor_get(x_1265, 2);
x_2755 = lean_ctor_get(x_1265, 3);
lean_inc(x_2755);
lean_inc(x_2754);
lean_inc(x_2753);
lean_inc(x_2752);
lean_dec(x_1265);
x_2756 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2756, 0, x_2748);
lean_ctor_set(x_2756, 1, x_2749);
lean_ctor_set(x_2756, 2, x_2750);
lean_ctor_set(x_2756, 3, x_2751);
lean_ctor_set_uint8(x_2756, sizeof(void*)*4, x_1889);
lean_ctor_set(x_234, 3, x_2755);
lean_ctor_set(x_234, 2, x_2754);
lean_ctor_set(x_234, 1, x_2753);
lean_ctor_set(x_234, 0, x_2752);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_1889);
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 0, x_2756);
x_2757 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2757, 0, x_1);
lean_ctor_set(x_2757, 1, x_2);
lean_ctor_set(x_2757, 2, x_3);
lean_ctor_set(x_2757, 3, x_4);
lean_ctor_set_uint8(x_2757, sizeof(void*)*4, x_1889);
return x_2757;
}
}
else
{
lean_object* x_2758; lean_object* x_2759; lean_object* x_2760; lean_object* x_2761; lean_object* x_2762; lean_object* x_2763; lean_object* x_2764; lean_object* x_2765; lean_object* x_2766; lean_object* x_2767; lean_object* x_2768; lean_object* x_2769; 
x_2758 = lean_ctor_get(x_234, 0);
x_2759 = lean_ctor_get(x_234, 1);
x_2760 = lean_ctor_get(x_234, 2);
x_2761 = lean_ctor_get(x_234, 3);
lean_inc(x_2761);
lean_inc(x_2760);
lean_inc(x_2759);
lean_inc(x_2758);
lean_dec(x_234);
x_2762 = lean_ctor_get(x_1265, 0);
lean_inc(x_2762);
x_2763 = lean_ctor_get(x_1265, 1);
lean_inc(x_2763);
x_2764 = lean_ctor_get(x_1265, 2);
lean_inc(x_2764);
x_2765 = lean_ctor_get(x_1265, 3);
lean_inc(x_2765);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2766 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2766 = lean_box(0);
}
if (lean_is_scalar(x_2766)) {
 x_2767 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2767 = x_2766;
}
lean_ctor_set(x_2767, 0, x_2758);
lean_ctor_set(x_2767, 1, x_2759);
lean_ctor_set(x_2767, 2, x_2760);
lean_ctor_set(x_2767, 3, x_2761);
lean_ctor_set_uint8(x_2767, sizeof(void*)*4, x_1889);
x_2768 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2768, 0, x_2762);
lean_ctor_set(x_2768, 1, x_2763);
lean_ctor_set(x_2768, 2, x_2764);
lean_ctor_set(x_2768, 3, x_2765);
lean_ctor_set_uint8(x_2768, sizeof(void*)*4, x_1889);
lean_ctor_set(x_1, 3, x_2768);
lean_ctor_set(x_1, 0, x_2767);
x_2769 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2769, 0, x_1);
lean_ctor_set(x_2769, 1, x_2);
lean_ctor_set(x_2769, 2, x_3);
lean_ctor_set(x_2769, 3, x_4);
lean_ctor_set_uint8(x_2769, sizeof(void*)*4, x_1889);
return x_2769;
}
}
else
{
lean_object* x_2770; lean_object* x_2771; lean_object* x_2772; lean_object* x_2773; lean_object* x_2774; lean_object* x_2775; lean_object* x_2776; lean_object* x_2777; lean_object* x_2778; lean_object* x_2779; lean_object* x_2780; lean_object* x_2781; lean_object* x_2782; lean_object* x_2783; lean_object* x_2784; lean_object* x_2785; 
x_2770 = lean_ctor_get(x_1, 1);
x_2771 = lean_ctor_get(x_1, 2);
lean_inc(x_2771);
lean_inc(x_2770);
lean_dec(x_1);
x_2772 = lean_ctor_get(x_234, 0);
lean_inc(x_2772);
x_2773 = lean_ctor_get(x_234, 1);
lean_inc(x_2773);
x_2774 = lean_ctor_get(x_234, 2);
lean_inc(x_2774);
x_2775 = lean_ctor_get(x_234, 3);
lean_inc(x_2775);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_2776 = x_234;
} else {
 lean_dec_ref(x_234);
 x_2776 = lean_box(0);
}
x_2777 = lean_ctor_get(x_1265, 0);
lean_inc(x_2777);
x_2778 = lean_ctor_get(x_1265, 1);
lean_inc(x_2778);
x_2779 = lean_ctor_get(x_1265, 2);
lean_inc(x_2779);
x_2780 = lean_ctor_get(x_1265, 3);
lean_inc(x_2780);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 lean_ctor_release(x_1265, 2);
 lean_ctor_release(x_1265, 3);
 x_2781 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_2781 = lean_box(0);
}
if (lean_is_scalar(x_2781)) {
 x_2782 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2782 = x_2781;
}
lean_ctor_set(x_2782, 0, x_2772);
lean_ctor_set(x_2782, 1, x_2773);
lean_ctor_set(x_2782, 2, x_2774);
lean_ctor_set(x_2782, 3, x_2775);
lean_ctor_set_uint8(x_2782, sizeof(void*)*4, x_1889);
if (lean_is_scalar(x_2776)) {
 x_2783 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2783 = x_2776;
}
lean_ctor_set(x_2783, 0, x_2777);
lean_ctor_set(x_2783, 1, x_2778);
lean_ctor_set(x_2783, 2, x_2779);
lean_ctor_set(x_2783, 3, x_2780);
lean_ctor_set_uint8(x_2783, sizeof(void*)*4, x_1889);
x_2784 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2784, 0, x_2782);
lean_ctor_set(x_2784, 1, x_2770);
lean_ctor_set(x_2784, 2, x_2771);
lean_ctor_set(x_2784, 3, x_2783);
lean_ctor_set_uint8(x_2784, sizeof(void*)*4, x_233);
x_2785 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2785, 0, x_2784);
lean_ctor_set(x_2785, 1, x_2);
lean_ctor_set(x_2785, 2, x_3);
lean_ctor_set(x_2785, 3, x_4);
lean_ctor_set_uint8(x_2785, sizeof(void*)*4, x_1889);
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
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_2786; 
x_2786 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2786, 0, x_1);
lean_ctor_set(x_2786, 1, x_2);
lean_ctor_set(x_2786, 2, x_3);
lean_ctor_set(x_2786, 3, x_4);
lean_ctor_set_uint8(x_2786, sizeof(void*)*4, x_233);
return x_2786;
}
else
{
uint8_t x_2787; 
x_2787 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_2787 == 0)
{
lean_object* x_2788; 
x_2788 = lean_ctor_get(x_4, 0);
lean_inc(x_2788);
if (lean_obj_tag(x_2788) == 0)
{
lean_object* x_2789; 
x_2789 = lean_ctor_get(x_4, 3);
lean_inc(x_2789);
if (lean_obj_tag(x_2789) == 0)
{
uint8_t x_2790; 
x_2790 = !lean_is_exclusive(x_4);
if (x_2790 == 0)
{
lean_object* x_2791; lean_object* x_2792; lean_object* x_2793; 
x_2791 = lean_ctor_get(x_4, 3);
lean_dec(x_2791);
x_2792 = lean_ctor_get(x_4, 0);
lean_dec(x_2792);
lean_ctor_set(x_4, 0, x_2789);
x_2793 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2793, 0, x_1);
lean_ctor_set(x_2793, 1, x_2);
lean_ctor_set(x_2793, 2, x_3);
lean_ctor_set(x_2793, 3, x_4);
lean_ctor_set_uint8(x_2793, sizeof(void*)*4, x_233);
return x_2793;
}
else
{
lean_object* x_2794; lean_object* x_2795; lean_object* x_2796; lean_object* x_2797; 
x_2794 = lean_ctor_get(x_4, 1);
x_2795 = lean_ctor_get(x_4, 2);
lean_inc(x_2795);
lean_inc(x_2794);
lean_dec(x_4);
x_2796 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2796, 0, x_2789);
lean_ctor_set(x_2796, 1, x_2794);
lean_ctor_set(x_2796, 2, x_2795);
lean_ctor_set(x_2796, 3, x_2789);
lean_ctor_set_uint8(x_2796, sizeof(void*)*4, x_2787);
x_2797 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2797, 0, x_1);
lean_ctor_set(x_2797, 1, x_2);
lean_ctor_set(x_2797, 2, x_3);
lean_ctor_set(x_2797, 3, x_2796);
lean_ctor_set_uint8(x_2797, sizeof(void*)*4, x_233);
return x_2797;
}
}
else
{
uint8_t x_2798; 
x_2798 = lean_ctor_get_uint8(x_2789, sizeof(void*)*4);
if (x_2798 == 0)
{
uint8_t x_2799; 
x_2799 = !lean_is_exclusive(x_4);
if (x_2799 == 0)
{
lean_object* x_2800; lean_object* x_2801; lean_object* x_2802; lean_object* x_2803; uint8_t x_2804; 
x_2800 = lean_ctor_get(x_4, 1);
x_2801 = lean_ctor_get(x_4, 2);
x_2802 = lean_ctor_get(x_4, 3);
lean_dec(x_2802);
x_2803 = lean_ctor_get(x_4, 0);
lean_dec(x_2803);
x_2804 = !lean_is_exclusive(x_2789);
if (x_2804 == 0)
{
lean_object* x_2805; lean_object* x_2806; lean_object* x_2807; lean_object* x_2808; uint8_t x_2809; 
x_2805 = lean_ctor_get(x_2789, 0);
x_2806 = lean_ctor_get(x_2789, 1);
x_2807 = lean_ctor_get(x_2789, 2);
x_2808 = lean_ctor_get(x_2789, 3);
lean_inc(x_1);
lean_ctor_set(x_2789, 3, x_2788);
lean_ctor_set(x_2789, 2, x_3);
lean_ctor_set(x_2789, 1, x_2);
lean_ctor_set(x_2789, 0, x_1);
x_2809 = !lean_is_exclusive(x_1);
if (x_2809 == 0)
{
lean_object* x_2810; lean_object* x_2811; lean_object* x_2812; lean_object* x_2813; 
x_2810 = lean_ctor_get(x_1, 3);
lean_dec(x_2810);
x_2811 = lean_ctor_get(x_1, 2);
lean_dec(x_2811);
x_2812 = lean_ctor_get(x_1, 1);
lean_dec(x_2812);
x_2813 = lean_ctor_get(x_1, 0);
lean_dec(x_2813);
lean_ctor_set_uint8(x_2789, sizeof(void*)*4, x_233);
lean_ctor_set(x_4, 3, x_2808);
lean_ctor_set(x_4, 2, x_2807);
lean_ctor_set(x_4, 1, x_2806);
lean_ctor_set(x_4, 0, x_2805);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_233);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_2801);
lean_ctor_set(x_1, 1, x_2800);
lean_ctor_set(x_1, 0, x_2789);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2798);
return x_1;
}
else
{
lean_object* x_2814; 
lean_dec(x_1);
lean_ctor_set_uint8(x_2789, sizeof(void*)*4, x_233);
lean_ctor_set(x_4, 3, x_2808);
lean_ctor_set(x_4, 2, x_2807);
lean_ctor_set(x_4, 1, x_2806);
lean_ctor_set(x_4, 0, x_2805);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_233);
x_2814 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2814, 0, x_2789);
lean_ctor_set(x_2814, 1, x_2800);
lean_ctor_set(x_2814, 2, x_2801);
lean_ctor_set(x_2814, 3, x_4);
lean_ctor_set_uint8(x_2814, sizeof(void*)*4, x_2798);
return x_2814;
}
}
else
{
lean_object* x_2815; lean_object* x_2816; lean_object* x_2817; lean_object* x_2818; lean_object* x_2819; lean_object* x_2820; lean_object* x_2821; 
x_2815 = lean_ctor_get(x_2789, 0);
x_2816 = lean_ctor_get(x_2789, 1);
x_2817 = lean_ctor_get(x_2789, 2);
x_2818 = lean_ctor_get(x_2789, 3);
lean_inc(x_2818);
lean_inc(x_2817);
lean_inc(x_2816);
lean_inc(x_2815);
lean_dec(x_2789);
lean_inc(x_1);
x_2819 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2819, 0, x_1);
lean_ctor_set(x_2819, 1, x_2);
lean_ctor_set(x_2819, 2, x_3);
lean_ctor_set(x_2819, 3, x_2788);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_2820 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2820 = lean_box(0);
}
lean_ctor_set_uint8(x_2819, sizeof(void*)*4, x_233);
lean_ctor_set(x_4, 3, x_2818);
lean_ctor_set(x_4, 2, x_2817);
lean_ctor_set(x_4, 1, x_2816);
lean_ctor_set(x_4, 0, x_2815);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_233);
if (lean_is_scalar(x_2820)) {
 x_2821 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2821 = x_2820;
}
lean_ctor_set(x_2821, 0, x_2819);
lean_ctor_set(x_2821, 1, x_2800);
lean_ctor_set(x_2821, 2, x_2801);
lean_ctor_set(x_2821, 3, x_4);
lean_ctor_set_uint8(x_2821, sizeof(void*)*4, x_2798);
return x_2821;
}
}
else
{
lean_object* x_2822; lean_object* x_2823; lean_object* x_2824; lean_object* x_2825; lean_object* x_2826; lean_object* x_2827; lean_object* x_2828; lean_object* x_2829; lean_object* x_2830; lean_object* x_2831; lean_object* x_2832; 
x_2822 = lean_ctor_get(x_4, 1);
x_2823 = lean_ctor_get(x_4, 2);
lean_inc(x_2823);
lean_inc(x_2822);
lean_dec(x_4);
x_2824 = lean_ctor_get(x_2789, 0);
lean_inc(x_2824);
x_2825 = lean_ctor_get(x_2789, 1);
lean_inc(x_2825);
x_2826 = lean_ctor_get(x_2789, 2);
lean_inc(x_2826);
x_2827 = lean_ctor_get(x_2789, 3);
lean_inc(x_2827);
if (lean_is_exclusive(x_2789)) {
 lean_ctor_release(x_2789, 0);
 lean_ctor_release(x_2789, 1);
 lean_ctor_release(x_2789, 2);
 lean_ctor_release(x_2789, 3);
 x_2828 = x_2789;
} else {
 lean_dec_ref(x_2789);
 x_2828 = lean_box(0);
}
lean_inc(x_1);
if (lean_is_scalar(x_2828)) {
 x_2829 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2829 = x_2828;
}
lean_ctor_set(x_2829, 0, x_1);
lean_ctor_set(x_2829, 1, x_2);
lean_ctor_set(x_2829, 2, x_3);
lean_ctor_set(x_2829, 3, x_2788);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_2830 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2830 = lean_box(0);
}
lean_ctor_set_uint8(x_2829, sizeof(void*)*4, x_233);
x_2831 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2831, 0, x_2824);
lean_ctor_set(x_2831, 1, x_2825);
lean_ctor_set(x_2831, 2, x_2826);
lean_ctor_set(x_2831, 3, x_2827);
lean_ctor_set_uint8(x_2831, sizeof(void*)*4, x_233);
if (lean_is_scalar(x_2830)) {
 x_2832 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2832 = x_2830;
}
lean_ctor_set(x_2832, 0, x_2829);
lean_ctor_set(x_2832, 1, x_2822);
lean_ctor_set(x_2832, 2, x_2823);
lean_ctor_set(x_2832, 3, x_2831);
lean_ctor_set_uint8(x_2832, sizeof(void*)*4, x_2798);
return x_2832;
}
}
else
{
uint8_t x_2833; 
x_2833 = !lean_is_exclusive(x_2789);
if (x_2833 == 0)
{
lean_object* x_2834; lean_object* x_2835; lean_object* x_2836; lean_object* x_2837; uint8_t x_2838; 
x_2834 = lean_ctor_get(x_2789, 3);
lean_dec(x_2834);
x_2835 = lean_ctor_get(x_2789, 2);
lean_dec(x_2835);
x_2836 = lean_ctor_get(x_2789, 1);
lean_dec(x_2836);
x_2837 = lean_ctor_get(x_2789, 0);
lean_dec(x_2837);
x_2838 = !lean_is_exclusive(x_1);
if (x_2838 == 0)
{
lean_object* x_2839; lean_object* x_2840; lean_object* x_2841; lean_object* x_2842; 
x_2839 = lean_ctor_get(x_1, 0);
x_2840 = lean_ctor_get(x_1, 1);
x_2841 = lean_ctor_get(x_1, 2);
x_2842 = lean_ctor_get(x_1, 3);
lean_ctor_set(x_2789, 3, x_2842);
lean_ctor_set(x_2789, 2, x_2841);
lean_ctor_set(x_2789, 1, x_2840);
lean_ctor_set(x_2789, 0, x_2839);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_2789);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2798);
return x_1;
}
else
{
lean_object* x_2843; lean_object* x_2844; lean_object* x_2845; lean_object* x_2846; lean_object* x_2847; 
x_2843 = lean_ctor_get(x_1, 0);
x_2844 = lean_ctor_get(x_1, 1);
x_2845 = lean_ctor_get(x_1, 2);
x_2846 = lean_ctor_get(x_1, 3);
lean_inc(x_2846);
lean_inc(x_2845);
lean_inc(x_2844);
lean_inc(x_2843);
lean_dec(x_1);
lean_ctor_set(x_2789, 3, x_2846);
lean_ctor_set(x_2789, 2, x_2845);
lean_ctor_set(x_2789, 1, x_2844);
lean_ctor_set(x_2789, 0, x_2843);
x_2847 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2847, 0, x_2789);
lean_ctor_set(x_2847, 1, x_2);
lean_ctor_set(x_2847, 2, x_3);
lean_ctor_set(x_2847, 3, x_4);
lean_ctor_set_uint8(x_2847, sizeof(void*)*4, x_2798);
return x_2847;
}
}
else
{
lean_object* x_2848; lean_object* x_2849; lean_object* x_2850; lean_object* x_2851; lean_object* x_2852; lean_object* x_2853; lean_object* x_2854; 
lean_dec(x_2789);
x_2848 = lean_ctor_get(x_1, 0);
lean_inc(x_2848);
x_2849 = lean_ctor_get(x_1, 1);
lean_inc(x_2849);
x_2850 = lean_ctor_get(x_1, 2);
lean_inc(x_2850);
x_2851 = lean_ctor_get(x_1, 3);
lean_inc(x_2851);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_2852 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2852 = lean_box(0);
}
x_2853 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2853, 0, x_2848);
lean_ctor_set(x_2853, 1, x_2849);
lean_ctor_set(x_2853, 2, x_2850);
lean_ctor_set(x_2853, 3, x_2851);
lean_ctor_set_uint8(x_2853, sizeof(void*)*4, x_2798);
if (lean_is_scalar(x_2852)) {
 x_2854 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2854 = x_2852;
}
lean_ctor_set(x_2854, 0, x_2853);
lean_ctor_set(x_2854, 1, x_2);
lean_ctor_set(x_2854, 2, x_3);
lean_ctor_set(x_2854, 3, x_4);
lean_ctor_set_uint8(x_2854, sizeof(void*)*4, x_2798);
return x_2854;
}
}
}
}
else
{
uint8_t x_2855; 
x_2855 = lean_ctor_get_uint8(x_2788, sizeof(void*)*4);
if (x_2855 == 0)
{
lean_object* x_2856; 
x_2856 = lean_ctor_get(x_4, 3);
lean_inc(x_2856);
if (lean_obj_tag(x_2856) == 0)
{
uint8_t x_2857; 
x_2857 = !lean_is_exclusive(x_4);
if (x_2857 == 0)
{
lean_object* x_2858; lean_object* x_2859; uint8_t x_2860; 
x_2858 = lean_ctor_get(x_4, 3);
lean_dec(x_2858);
x_2859 = lean_ctor_get(x_4, 0);
lean_dec(x_2859);
x_2860 = !lean_is_exclusive(x_2788);
if (x_2860 == 0)
{
lean_object* x_2861; lean_object* x_2862; lean_object* x_2863; lean_object* x_2864; uint8_t x_2865; 
x_2861 = lean_ctor_get(x_2788, 0);
x_2862 = lean_ctor_get(x_2788, 1);
x_2863 = lean_ctor_get(x_2788, 2);
x_2864 = lean_ctor_get(x_2788, 3);
lean_inc(x_1);
lean_ctor_set(x_2788, 3, x_2861);
lean_ctor_set(x_2788, 2, x_3);
lean_ctor_set(x_2788, 1, x_2);
lean_ctor_set(x_2788, 0, x_1);
x_2865 = !lean_is_exclusive(x_1);
if (x_2865 == 0)
{
lean_object* x_2866; lean_object* x_2867; lean_object* x_2868; lean_object* x_2869; 
x_2866 = lean_ctor_get(x_1, 3);
lean_dec(x_2866);
x_2867 = lean_ctor_get(x_1, 2);
lean_dec(x_2867);
x_2868 = lean_ctor_get(x_1, 1);
lean_dec(x_2868);
x_2869 = lean_ctor_get(x_1, 0);
lean_dec(x_2869);
lean_ctor_set_uint8(x_2788, sizeof(void*)*4, x_233);
lean_ctor_set(x_4, 0, x_2864);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_233);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_2863);
lean_ctor_set(x_1, 1, x_2862);
lean_ctor_set(x_1, 0, x_2788);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2855);
return x_1;
}
else
{
lean_object* x_2870; 
lean_dec(x_1);
lean_ctor_set_uint8(x_2788, sizeof(void*)*4, x_233);
lean_ctor_set(x_4, 0, x_2864);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_233);
x_2870 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2870, 0, x_2788);
lean_ctor_set(x_2870, 1, x_2862);
lean_ctor_set(x_2870, 2, x_2863);
lean_ctor_set(x_2870, 3, x_4);
lean_ctor_set_uint8(x_2870, sizeof(void*)*4, x_2855);
return x_2870;
}
}
else
{
lean_object* x_2871; lean_object* x_2872; lean_object* x_2873; lean_object* x_2874; lean_object* x_2875; lean_object* x_2876; lean_object* x_2877; 
x_2871 = lean_ctor_get(x_2788, 0);
x_2872 = lean_ctor_get(x_2788, 1);
x_2873 = lean_ctor_get(x_2788, 2);
x_2874 = lean_ctor_get(x_2788, 3);
lean_inc(x_2874);
lean_inc(x_2873);
lean_inc(x_2872);
lean_inc(x_2871);
lean_dec(x_2788);
lean_inc(x_1);
x_2875 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2875, 0, x_1);
lean_ctor_set(x_2875, 1, x_2);
lean_ctor_set(x_2875, 2, x_3);
lean_ctor_set(x_2875, 3, x_2871);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_2876 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2876 = lean_box(0);
}
lean_ctor_set_uint8(x_2875, sizeof(void*)*4, x_233);
lean_ctor_set(x_4, 0, x_2874);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_233);
if (lean_is_scalar(x_2876)) {
 x_2877 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2877 = x_2876;
}
lean_ctor_set(x_2877, 0, x_2875);
lean_ctor_set(x_2877, 1, x_2872);
lean_ctor_set(x_2877, 2, x_2873);
lean_ctor_set(x_2877, 3, x_4);
lean_ctor_set_uint8(x_2877, sizeof(void*)*4, x_2855);
return x_2877;
}
}
else
{
lean_object* x_2878; lean_object* x_2879; lean_object* x_2880; lean_object* x_2881; lean_object* x_2882; lean_object* x_2883; lean_object* x_2884; lean_object* x_2885; lean_object* x_2886; lean_object* x_2887; lean_object* x_2888; 
x_2878 = lean_ctor_get(x_4, 1);
x_2879 = lean_ctor_get(x_4, 2);
lean_inc(x_2879);
lean_inc(x_2878);
lean_dec(x_4);
x_2880 = lean_ctor_get(x_2788, 0);
lean_inc(x_2880);
x_2881 = lean_ctor_get(x_2788, 1);
lean_inc(x_2881);
x_2882 = lean_ctor_get(x_2788, 2);
lean_inc(x_2882);
x_2883 = lean_ctor_get(x_2788, 3);
lean_inc(x_2883);
if (lean_is_exclusive(x_2788)) {
 lean_ctor_release(x_2788, 0);
 lean_ctor_release(x_2788, 1);
 lean_ctor_release(x_2788, 2);
 lean_ctor_release(x_2788, 3);
 x_2884 = x_2788;
} else {
 lean_dec_ref(x_2788);
 x_2884 = lean_box(0);
}
lean_inc(x_1);
if (lean_is_scalar(x_2884)) {
 x_2885 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2885 = x_2884;
}
lean_ctor_set(x_2885, 0, x_1);
lean_ctor_set(x_2885, 1, x_2);
lean_ctor_set(x_2885, 2, x_3);
lean_ctor_set(x_2885, 3, x_2880);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_2886 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2886 = lean_box(0);
}
lean_ctor_set_uint8(x_2885, sizeof(void*)*4, x_233);
x_2887 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2887, 0, x_2883);
lean_ctor_set(x_2887, 1, x_2878);
lean_ctor_set(x_2887, 2, x_2879);
lean_ctor_set(x_2887, 3, x_2856);
lean_ctor_set_uint8(x_2887, sizeof(void*)*4, x_233);
if (lean_is_scalar(x_2886)) {
 x_2888 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2888 = x_2886;
}
lean_ctor_set(x_2888, 0, x_2885);
lean_ctor_set(x_2888, 1, x_2881);
lean_ctor_set(x_2888, 2, x_2882);
lean_ctor_set(x_2888, 3, x_2887);
lean_ctor_set_uint8(x_2888, sizeof(void*)*4, x_2855);
return x_2888;
}
}
else
{
uint8_t x_2889; 
x_2889 = lean_ctor_get_uint8(x_2856, sizeof(void*)*4);
if (x_2889 == 0)
{
uint8_t x_2890; 
x_2890 = !lean_is_exclusive(x_4);
if (x_2890 == 0)
{
lean_object* x_2891; lean_object* x_2892; lean_object* x_2893; lean_object* x_2894; uint8_t x_2895; 
x_2891 = lean_ctor_get(x_4, 1);
x_2892 = lean_ctor_get(x_4, 2);
x_2893 = lean_ctor_get(x_4, 3);
lean_dec(x_2893);
x_2894 = lean_ctor_get(x_4, 0);
lean_dec(x_2894);
x_2895 = !lean_is_exclusive(x_2788);
if (x_2895 == 0)
{
uint8_t x_2896; 
x_2896 = !lean_is_exclusive(x_2856);
if (x_2896 == 0)
{
lean_object* x_2897; lean_object* x_2898; lean_object* x_2899; lean_object* x_2900; lean_object* x_2901; lean_object* x_2902; lean_object* x_2903; lean_object* x_2904; uint8_t x_2905; 
x_2897 = lean_ctor_get(x_2788, 0);
x_2898 = lean_ctor_get(x_2788, 1);
x_2899 = lean_ctor_get(x_2788, 2);
x_2900 = lean_ctor_get(x_2788, 3);
x_2901 = lean_ctor_get(x_2856, 0);
x_2902 = lean_ctor_get(x_2856, 1);
x_2903 = lean_ctor_get(x_2856, 2);
x_2904 = lean_ctor_get(x_2856, 3);
lean_ctor_set(x_2856, 3, x_2900);
lean_ctor_set(x_2856, 2, x_2899);
lean_ctor_set(x_2856, 1, x_2898);
lean_ctor_set(x_2856, 0, x_2897);
lean_inc(x_1);
lean_ctor_set(x_2788, 3, x_2856);
lean_ctor_set(x_2788, 2, x_3);
lean_ctor_set(x_2788, 1, x_2);
lean_ctor_set(x_2788, 0, x_1);
x_2905 = !lean_is_exclusive(x_1);
if (x_2905 == 0)
{
lean_object* x_2906; lean_object* x_2907; lean_object* x_2908; lean_object* x_2909; 
x_2906 = lean_ctor_get(x_1, 3);
lean_dec(x_2906);
x_2907 = lean_ctor_get(x_1, 2);
lean_dec(x_2907);
x_2908 = lean_ctor_get(x_1, 1);
lean_dec(x_2908);
x_2909 = lean_ctor_get(x_1, 0);
lean_dec(x_2909);
lean_ctor_set_uint8(x_2788, sizeof(void*)*4, x_233);
lean_ctor_set(x_4, 3, x_2904);
lean_ctor_set(x_4, 2, x_2903);
lean_ctor_set(x_4, 1, x_2902);
lean_ctor_set(x_4, 0, x_2901);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_233);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_2892);
lean_ctor_set(x_1, 1, x_2891);
lean_ctor_set(x_1, 0, x_2788);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2889);
return x_1;
}
else
{
lean_object* x_2910; 
lean_dec(x_1);
lean_ctor_set_uint8(x_2788, sizeof(void*)*4, x_233);
lean_ctor_set(x_4, 3, x_2904);
lean_ctor_set(x_4, 2, x_2903);
lean_ctor_set(x_4, 1, x_2902);
lean_ctor_set(x_4, 0, x_2901);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_233);
x_2910 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2910, 0, x_2788);
lean_ctor_set(x_2910, 1, x_2891);
lean_ctor_set(x_2910, 2, x_2892);
lean_ctor_set(x_2910, 3, x_4);
lean_ctor_set_uint8(x_2910, sizeof(void*)*4, x_2889);
return x_2910;
}
}
else
{
lean_object* x_2911; lean_object* x_2912; lean_object* x_2913; lean_object* x_2914; lean_object* x_2915; lean_object* x_2916; lean_object* x_2917; lean_object* x_2918; lean_object* x_2919; lean_object* x_2920; lean_object* x_2921; 
x_2911 = lean_ctor_get(x_2788, 0);
x_2912 = lean_ctor_get(x_2788, 1);
x_2913 = lean_ctor_get(x_2788, 2);
x_2914 = lean_ctor_get(x_2788, 3);
x_2915 = lean_ctor_get(x_2856, 0);
x_2916 = lean_ctor_get(x_2856, 1);
x_2917 = lean_ctor_get(x_2856, 2);
x_2918 = lean_ctor_get(x_2856, 3);
lean_inc(x_2918);
lean_inc(x_2917);
lean_inc(x_2916);
lean_inc(x_2915);
lean_dec(x_2856);
x_2919 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2919, 0, x_2911);
lean_ctor_set(x_2919, 1, x_2912);
lean_ctor_set(x_2919, 2, x_2913);
lean_ctor_set(x_2919, 3, x_2914);
lean_ctor_set_uint8(x_2919, sizeof(void*)*4, x_2889);
lean_inc(x_1);
lean_ctor_set(x_2788, 3, x_2919);
lean_ctor_set(x_2788, 2, x_3);
lean_ctor_set(x_2788, 1, x_2);
lean_ctor_set(x_2788, 0, x_1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_2920 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2920 = lean_box(0);
}
lean_ctor_set_uint8(x_2788, sizeof(void*)*4, x_233);
lean_ctor_set(x_4, 3, x_2918);
lean_ctor_set(x_4, 2, x_2917);
lean_ctor_set(x_4, 1, x_2916);
lean_ctor_set(x_4, 0, x_2915);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_233);
if (lean_is_scalar(x_2920)) {
 x_2921 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2921 = x_2920;
}
lean_ctor_set(x_2921, 0, x_2788);
lean_ctor_set(x_2921, 1, x_2891);
lean_ctor_set(x_2921, 2, x_2892);
lean_ctor_set(x_2921, 3, x_4);
lean_ctor_set_uint8(x_2921, sizeof(void*)*4, x_2889);
return x_2921;
}
}
else
{
lean_object* x_2922; lean_object* x_2923; lean_object* x_2924; lean_object* x_2925; lean_object* x_2926; lean_object* x_2927; lean_object* x_2928; lean_object* x_2929; lean_object* x_2930; lean_object* x_2931; lean_object* x_2932; lean_object* x_2933; lean_object* x_2934; 
x_2922 = lean_ctor_get(x_2788, 0);
x_2923 = lean_ctor_get(x_2788, 1);
x_2924 = lean_ctor_get(x_2788, 2);
x_2925 = lean_ctor_get(x_2788, 3);
lean_inc(x_2925);
lean_inc(x_2924);
lean_inc(x_2923);
lean_inc(x_2922);
lean_dec(x_2788);
x_2926 = lean_ctor_get(x_2856, 0);
lean_inc(x_2926);
x_2927 = lean_ctor_get(x_2856, 1);
lean_inc(x_2927);
x_2928 = lean_ctor_get(x_2856, 2);
lean_inc(x_2928);
x_2929 = lean_ctor_get(x_2856, 3);
lean_inc(x_2929);
if (lean_is_exclusive(x_2856)) {
 lean_ctor_release(x_2856, 0);
 lean_ctor_release(x_2856, 1);
 lean_ctor_release(x_2856, 2);
 lean_ctor_release(x_2856, 3);
 x_2930 = x_2856;
} else {
 lean_dec_ref(x_2856);
 x_2930 = lean_box(0);
}
if (lean_is_scalar(x_2930)) {
 x_2931 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2931 = x_2930;
}
lean_ctor_set(x_2931, 0, x_2922);
lean_ctor_set(x_2931, 1, x_2923);
lean_ctor_set(x_2931, 2, x_2924);
lean_ctor_set(x_2931, 3, x_2925);
lean_ctor_set_uint8(x_2931, sizeof(void*)*4, x_2889);
lean_inc(x_1);
x_2932 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2932, 0, x_1);
lean_ctor_set(x_2932, 1, x_2);
lean_ctor_set(x_2932, 2, x_3);
lean_ctor_set(x_2932, 3, x_2931);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_2933 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2933 = lean_box(0);
}
lean_ctor_set_uint8(x_2932, sizeof(void*)*4, x_233);
lean_ctor_set(x_4, 3, x_2929);
lean_ctor_set(x_4, 2, x_2928);
lean_ctor_set(x_4, 1, x_2927);
lean_ctor_set(x_4, 0, x_2926);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_233);
if (lean_is_scalar(x_2933)) {
 x_2934 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2934 = x_2933;
}
lean_ctor_set(x_2934, 0, x_2932);
lean_ctor_set(x_2934, 1, x_2891);
lean_ctor_set(x_2934, 2, x_2892);
lean_ctor_set(x_2934, 3, x_4);
lean_ctor_set_uint8(x_2934, sizeof(void*)*4, x_2889);
return x_2934;
}
}
else
{
lean_object* x_2935; lean_object* x_2936; lean_object* x_2937; lean_object* x_2938; lean_object* x_2939; lean_object* x_2940; lean_object* x_2941; lean_object* x_2942; lean_object* x_2943; lean_object* x_2944; lean_object* x_2945; lean_object* x_2946; lean_object* x_2947; lean_object* x_2948; lean_object* x_2949; lean_object* x_2950; lean_object* x_2951; 
x_2935 = lean_ctor_get(x_4, 1);
x_2936 = lean_ctor_get(x_4, 2);
lean_inc(x_2936);
lean_inc(x_2935);
lean_dec(x_4);
x_2937 = lean_ctor_get(x_2788, 0);
lean_inc(x_2937);
x_2938 = lean_ctor_get(x_2788, 1);
lean_inc(x_2938);
x_2939 = lean_ctor_get(x_2788, 2);
lean_inc(x_2939);
x_2940 = lean_ctor_get(x_2788, 3);
lean_inc(x_2940);
if (lean_is_exclusive(x_2788)) {
 lean_ctor_release(x_2788, 0);
 lean_ctor_release(x_2788, 1);
 lean_ctor_release(x_2788, 2);
 lean_ctor_release(x_2788, 3);
 x_2941 = x_2788;
} else {
 lean_dec_ref(x_2788);
 x_2941 = lean_box(0);
}
x_2942 = lean_ctor_get(x_2856, 0);
lean_inc(x_2942);
x_2943 = lean_ctor_get(x_2856, 1);
lean_inc(x_2943);
x_2944 = lean_ctor_get(x_2856, 2);
lean_inc(x_2944);
x_2945 = lean_ctor_get(x_2856, 3);
lean_inc(x_2945);
if (lean_is_exclusive(x_2856)) {
 lean_ctor_release(x_2856, 0);
 lean_ctor_release(x_2856, 1);
 lean_ctor_release(x_2856, 2);
 lean_ctor_release(x_2856, 3);
 x_2946 = x_2856;
} else {
 lean_dec_ref(x_2856);
 x_2946 = lean_box(0);
}
if (lean_is_scalar(x_2946)) {
 x_2947 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2947 = x_2946;
}
lean_ctor_set(x_2947, 0, x_2937);
lean_ctor_set(x_2947, 1, x_2938);
lean_ctor_set(x_2947, 2, x_2939);
lean_ctor_set(x_2947, 3, x_2940);
lean_ctor_set_uint8(x_2947, sizeof(void*)*4, x_2889);
lean_inc(x_1);
if (lean_is_scalar(x_2941)) {
 x_2948 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2948 = x_2941;
}
lean_ctor_set(x_2948, 0, x_1);
lean_ctor_set(x_2948, 1, x_2);
lean_ctor_set(x_2948, 2, x_3);
lean_ctor_set(x_2948, 3, x_2947);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_2949 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2949 = lean_box(0);
}
lean_ctor_set_uint8(x_2948, sizeof(void*)*4, x_233);
x_2950 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2950, 0, x_2942);
lean_ctor_set(x_2950, 1, x_2943);
lean_ctor_set(x_2950, 2, x_2944);
lean_ctor_set(x_2950, 3, x_2945);
lean_ctor_set_uint8(x_2950, sizeof(void*)*4, x_233);
if (lean_is_scalar(x_2949)) {
 x_2951 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2951 = x_2949;
}
lean_ctor_set(x_2951, 0, x_2948);
lean_ctor_set(x_2951, 1, x_2935);
lean_ctor_set(x_2951, 2, x_2936);
lean_ctor_set(x_2951, 3, x_2950);
lean_ctor_set_uint8(x_2951, sizeof(void*)*4, x_2889);
return x_2951;
}
}
else
{
uint8_t x_2952; 
x_2952 = !lean_is_exclusive(x_1);
if (x_2952 == 0)
{
uint8_t x_2953; 
x_2953 = !lean_is_exclusive(x_4);
if (x_2953 == 0)
{
lean_object* x_2954; lean_object* x_2955; lean_object* x_2956; lean_object* x_2957; lean_object* x_2958; lean_object* x_2959; lean_object* x_2960; lean_object* x_2961; uint8_t x_2962; 
x_2954 = lean_ctor_get(x_1, 0);
x_2955 = lean_ctor_get(x_1, 1);
x_2956 = lean_ctor_get(x_1, 2);
x_2957 = lean_ctor_get(x_1, 3);
x_2958 = lean_ctor_get(x_4, 1);
x_2959 = lean_ctor_get(x_4, 2);
x_2960 = lean_ctor_get(x_4, 3);
lean_dec(x_2960);
x_2961 = lean_ctor_get(x_4, 0);
lean_dec(x_2961);
x_2962 = !lean_is_exclusive(x_2788);
if (x_2962 == 0)
{
lean_object* x_2963; lean_object* x_2964; lean_object* x_2965; lean_object* x_2966; lean_object* x_2967; 
x_2963 = lean_ctor_get(x_2788, 0);
x_2964 = lean_ctor_get(x_2788, 1);
x_2965 = lean_ctor_get(x_2788, 2);
x_2966 = lean_ctor_get(x_2788, 3);
lean_ctor_set(x_2788, 3, x_2957);
lean_ctor_set(x_2788, 2, x_2956);
lean_ctor_set(x_2788, 1, x_2955);
lean_ctor_set(x_2788, 0, x_2954);
lean_ctor_set_uint8(x_2788, sizeof(void*)*4, x_2889);
lean_ctor_set(x_4, 3, x_2963);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2889);
lean_ctor_set(x_1, 3, x_2856);
lean_ctor_set(x_1, 2, x_2959);
lean_ctor_set(x_1, 1, x_2958);
lean_ctor_set(x_1, 0, x_2966);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2889);
x_2967 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2967, 0, x_4);
lean_ctor_set(x_2967, 1, x_2964);
lean_ctor_set(x_2967, 2, x_2965);
lean_ctor_set(x_2967, 3, x_1);
lean_ctor_set_uint8(x_2967, sizeof(void*)*4, x_2855);
return x_2967;
}
else
{
lean_object* x_2968; lean_object* x_2969; lean_object* x_2970; lean_object* x_2971; lean_object* x_2972; lean_object* x_2973; 
x_2968 = lean_ctor_get(x_2788, 0);
x_2969 = lean_ctor_get(x_2788, 1);
x_2970 = lean_ctor_get(x_2788, 2);
x_2971 = lean_ctor_get(x_2788, 3);
lean_inc(x_2971);
lean_inc(x_2970);
lean_inc(x_2969);
lean_inc(x_2968);
lean_dec(x_2788);
x_2972 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2972, 0, x_2954);
lean_ctor_set(x_2972, 1, x_2955);
lean_ctor_set(x_2972, 2, x_2956);
lean_ctor_set(x_2972, 3, x_2957);
lean_ctor_set_uint8(x_2972, sizeof(void*)*4, x_2889);
lean_ctor_set(x_4, 3, x_2968);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_2972);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2889);
lean_ctor_set(x_1, 3, x_2856);
lean_ctor_set(x_1, 2, x_2959);
lean_ctor_set(x_1, 1, x_2958);
lean_ctor_set(x_1, 0, x_2971);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2889);
x_2973 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2973, 0, x_4);
lean_ctor_set(x_2973, 1, x_2969);
lean_ctor_set(x_2973, 2, x_2970);
lean_ctor_set(x_2973, 3, x_1);
lean_ctor_set_uint8(x_2973, sizeof(void*)*4, x_2855);
return x_2973;
}
}
else
{
lean_object* x_2974; lean_object* x_2975; lean_object* x_2976; lean_object* x_2977; lean_object* x_2978; lean_object* x_2979; lean_object* x_2980; lean_object* x_2981; lean_object* x_2982; lean_object* x_2983; lean_object* x_2984; lean_object* x_2985; lean_object* x_2986; lean_object* x_2987; 
x_2974 = lean_ctor_get(x_1, 0);
x_2975 = lean_ctor_get(x_1, 1);
x_2976 = lean_ctor_get(x_1, 2);
x_2977 = lean_ctor_get(x_1, 3);
x_2978 = lean_ctor_get(x_4, 1);
x_2979 = lean_ctor_get(x_4, 2);
lean_inc(x_2979);
lean_inc(x_2978);
lean_dec(x_4);
x_2980 = lean_ctor_get(x_2788, 0);
lean_inc(x_2980);
x_2981 = lean_ctor_get(x_2788, 1);
lean_inc(x_2981);
x_2982 = lean_ctor_get(x_2788, 2);
lean_inc(x_2982);
x_2983 = lean_ctor_get(x_2788, 3);
lean_inc(x_2983);
if (lean_is_exclusive(x_2788)) {
 lean_ctor_release(x_2788, 0);
 lean_ctor_release(x_2788, 1);
 lean_ctor_release(x_2788, 2);
 lean_ctor_release(x_2788, 3);
 x_2984 = x_2788;
} else {
 lean_dec_ref(x_2788);
 x_2984 = lean_box(0);
}
if (lean_is_scalar(x_2984)) {
 x_2985 = lean_alloc_ctor(1, 4, 1);
} else {
 x_2985 = x_2984;
}
lean_ctor_set(x_2985, 0, x_2974);
lean_ctor_set(x_2985, 1, x_2975);
lean_ctor_set(x_2985, 2, x_2976);
lean_ctor_set(x_2985, 3, x_2977);
lean_ctor_set_uint8(x_2985, sizeof(void*)*4, x_2889);
x_2986 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2986, 0, x_2985);
lean_ctor_set(x_2986, 1, x_2);
lean_ctor_set(x_2986, 2, x_3);
lean_ctor_set(x_2986, 3, x_2980);
lean_ctor_set_uint8(x_2986, sizeof(void*)*4, x_2889);
lean_ctor_set(x_1, 3, x_2856);
lean_ctor_set(x_1, 2, x_2979);
lean_ctor_set(x_1, 1, x_2978);
lean_ctor_set(x_1, 0, x_2983);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2889);
x_2987 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_2987, 0, x_2986);
lean_ctor_set(x_2987, 1, x_2981);
lean_ctor_set(x_2987, 2, x_2982);
lean_ctor_set(x_2987, 3, x_1);
lean_ctor_set_uint8(x_2987, sizeof(void*)*4, x_2855);
return x_2987;
}
}
else
{
lean_object* x_2988; lean_object* x_2989; lean_object* x_2990; lean_object* x_2991; lean_object* x_2992; lean_object* x_2993; lean_object* x_2994; lean_object* x_2995; lean_object* x_2996; lean_object* x_2997; lean_object* x_2998; lean_object* x_2999; lean_object* x_3000; lean_object* x_3001; lean_object* x_3002; lean_object* x_3003; 
x_2988 = lean_ctor_get(x_1, 0);
x_2989 = lean_ctor_get(x_1, 1);
x_2990 = lean_ctor_get(x_1, 2);
x_2991 = lean_ctor_get(x_1, 3);
lean_inc(x_2991);
lean_inc(x_2990);
lean_inc(x_2989);
lean_inc(x_2988);
lean_dec(x_1);
x_2992 = lean_ctor_get(x_4, 1);
lean_inc(x_2992);
x_2993 = lean_ctor_get(x_4, 2);
lean_inc(x_2993);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_2994 = x_4;
} else {
 lean_dec_ref(x_4);
 x_2994 = lean_box(0);
}
x_2995 = lean_ctor_get(x_2788, 0);
lean_inc(x_2995);
x_2996 = lean_ctor_get(x_2788, 1);
lean_inc(x_2996);
x_2997 = lean_ctor_get(x_2788, 2);
lean_inc(x_2997);
x_2998 = lean_ctor_get(x_2788, 3);
lean_inc(x_2998);
if (lean_is_exclusive(x_2788)) {
 lean_ctor_release(x_2788, 0);
 lean_ctor_release(x_2788, 1);
 lean_ctor_release(x_2788, 2);
 lean_ctor_release(x_2788, 3);
 x_2999 = x_2788;
} else {
 lean_dec_ref(x_2788);
 x_2999 = lean_box(0);
}
if (lean_is_scalar(x_2999)) {
 x_3000 = lean_alloc_ctor(1, 4, 1);
} else {
 x_3000 = x_2999;
}
lean_ctor_set(x_3000, 0, x_2988);
lean_ctor_set(x_3000, 1, x_2989);
lean_ctor_set(x_3000, 2, x_2990);
lean_ctor_set(x_3000, 3, x_2991);
lean_ctor_set_uint8(x_3000, sizeof(void*)*4, x_2889);
if (lean_is_scalar(x_2994)) {
 x_3001 = lean_alloc_ctor(1, 4, 1);
} else {
 x_3001 = x_2994;
}
lean_ctor_set(x_3001, 0, x_3000);
lean_ctor_set(x_3001, 1, x_2);
lean_ctor_set(x_3001, 2, x_3);
lean_ctor_set(x_3001, 3, x_2995);
lean_ctor_set_uint8(x_3001, sizeof(void*)*4, x_2889);
x_3002 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3002, 0, x_2998);
lean_ctor_set(x_3002, 1, x_2992);
lean_ctor_set(x_3002, 2, x_2993);
lean_ctor_set(x_3002, 3, x_2856);
lean_ctor_set_uint8(x_3002, sizeof(void*)*4, x_2889);
x_3003 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3003, 0, x_3001);
lean_ctor_set(x_3003, 1, x_2996);
lean_ctor_set(x_3003, 2, x_2997);
lean_ctor_set(x_3003, 3, x_3002);
lean_ctor_set_uint8(x_3003, sizeof(void*)*4, x_2855);
return x_3003;
}
}
}
}
else
{
lean_object* x_3004; 
x_3004 = lean_ctor_get(x_4, 3);
lean_inc(x_3004);
if (lean_obj_tag(x_3004) == 0)
{
uint8_t x_3005; 
x_3005 = !lean_is_exclusive(x_2788);
if (x_3005 == 0)
{
lean_object* x_3006; lean_object* x_3007; lean_object* x_3008; lean_object* x_3009; uint8_t x_3010; 
x_3006 = lean_ctor_get(x_2788, 3);
lean_dec(x_3006);
x_3007 = lean_ctor_get(x_2788, 2);
lean_dec(x_3007);
x_3008 = lean_ctor_get(x_2788, 1);
lean_dec(x_3008);
x_3009 = lean_ctor_get(x_2788, 0);
lean_dec(x_3009);
x_3010 = !lean_is_exclusive(x_1);
if (x_3010 == 0)
{
lean_object* x_3011; lean_object* x_3012; lean_object* x_3013; lean_object* x_3014; 
x_3011 = lean_ctor_get(x_1, 0);
x_3012 = lean_ctor_get(x_1, 1);
x_3013 = lean_ctor_get(x_1, 2);
x_3014 = lean_ctor_get(x_1, 3);
lean_ctor_set(x_2788, 3, x_3014);
lean_ctor_set(x_2788, 2, x_3013);
lean_ctor_set(x_2788, 1, x_3012);
lean_ctor_set(x_2788, 0, x_3011);
lean_ctor_set(x_1, 3, x_4);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_2788);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2855);
return x_1;
}
else
{
lean_object* x_3015; lean_object* x_3016; lean_object* x_3017; lean_object* x_3018; lean_object* x_3019; 
x_3015 = lean_ctor_get(x_1, 0);
x_3016 = lean_ctor_get(x_1, 1);
x_3017 = lean_ctor_get(x_1, 2);
x_3018 = lean_ctor_get(x_1, 3);
lean_inc(x_3018);
lean_inc(x_3017);
lean_inc(x_3016);
lean_inc(x_3015);
lean_dec(x_1);
lean_ctor_set(x_2788, 3, x_3018);
lean_ctor_set(x_2788, 2, x_3017);
lean_ctor_set(x_2788, 1, x_3016);
lean_ctor_set(x_2788, 0, x_3015);
x_3019 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3019, 0, x_2788);
lean_ctor_set(x_3019, 1, x_2);
lean_ctor_set(x_3019, 2, x_3);
lean_ctor_set(x_3019, 3, x_4);
lean_ctor_set_uint8(x_3019, sizeof(void*)*4, x_2855);
return x_3019;
}
}
else
{
lean_object* x_3020; lean_object* x_3021; lean_object* x_3022; lean_object* x_3023; lean_object* x_3024; lean_object* x_3025; lean_object* x_3026; 
lean_dec(x_2788);
x_3020 = lean_ctor_get(x_1, 0);
lean_inc(x_3020);
x_3021 = lean_ctor_get(x_1, 1);
lean_inc(x_3021);
x_3022 = lean_ctor_get(x_1, 2);
lean_inc(x_3022);
x_3023 = lean_ctor_get(x_1, 3);
lean_inc(x_3023);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_3024 = x_1;
} else {
 lean_dec_ref(x_1);
 x_3024 = lean_box(0);
}
x_3025 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3025, 0, x_3020);
lean_ctor_set(x_3025, 1, x_3021);
lean_ctor_set(x_3025, 2, x_3022);
lean_ctor_set(x_3025, 3, x_3023);
lean_ctor_set_uint8(x_3025, sizeof(void*)*4, x_2855);
if (lean_is_scalar(x_3024)) {
 x_3026 = lean_alloc_ctor(1, 4, 1);
} else {
 x_3026 = x_3024;
}
lean_ctor_set(x_3026, 0, x_3025);
lean_ctor_set(x_3026, 1, x_2);
lean_ctor_set(x_3026, 2, x_3);
lean_ctor_set(x_3026, 3, x_4);
lean_ctor_set_uint8(x_3026, sizeof(void*)*4, x_2855);
return x_3026;
}
}
else
{
uint8_t x_3027; 
x_3027 = lean_ctor_get_uint8(x_3004, sizeof(void*)*4);
if (x_3027 == 0)
{
uint8_t x_3028; 
x_3028 = !lean_is_exclusive(x_1);
if (x_3028 == 0)
{
uint8_t x_3029; 
x_3029 = !lean_is_exclusive(x_4);
if (x_3029 == 0)
{
lean_object* x_3030; lean_object* x_3031; lean_object* x_3032; lean_object* x_3033; lean_object* x_3034; lean_object* x_3035; lean_object* x_3036; lean_object* x_3037; uint8_t x_3038; 
x_3030 = lean_ctor_get(x_1, 0);
x_3031 = lean_ctor_get(x_1, 1);
x_3032 = lean_ctor_get(x_1, 2);
x_3033 = lean_ctor_get(x_1, 3);
x_3034 = lean_ctor_get(x_4, 1);
x_3035 = lean_ctor_get(x_4, 2);
x_3036 = lean_ctor_get(x_4, 3);
lean_dec(x_3036);
x_3037 = lean_ctor_get(x_4, 0);
lean_dec(x_3037);
x_3038 = !lean_is_exclusive(x_3004);
if (x_3038 == 0)
{
lean_object* x_3039; lean_object* x_3040; lean_object* x_3041; lean_object* x_3042; lean_object* x_3043; 
x_3039 = lean_ctor_get(x_3004, 0);
x_3040 = lean_ctor_get(x_3004, 1);
x_3041 = lean_ctor_get(x_3004, 2);
x_3042 = lean_ctor_get(x_3004, 3);
lean_ctor_set(x_3004, 3, x_3033);
lean_ctor_set(x_3004, 2, x_3032);
lean_ctor_set(x_3004, 1, x_3031);
lean_ctor_set(x_3004, 0, x_3030);
lean_ctor_set_uint8(x_3004, sizeof(void*)*4, x_2855);
lean_ctor_set(x_4, 3, x_2788);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_3004);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2855);
lean_ctor_set(x_1, 3, x_3042);
lean_ctor_set(x_1, 2, x_3041);
lean_ctor_set(x_1, 1, x_3040);
lean_ctor_set(x_1, 0, x_3039);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2855);
x_3043 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3043, 0, x_4);
lean_ctor_set(x_3043, 1, x_3034);
lean_ctor_set(x_3043, 2, x_3035);
lean_ctor_set(x_3043, 3, x_1);
lean_ctor_set_uint8(x_3043, sizeof(void*)*4, x_3027);
return x_3043;
}
else
{
lean_object* x_3044; lean_object* x_3045; lean_object* x_3046; lean_object* x_3047; lean_object* x_3048; lean_object* x_3049; 
x_3044 = lean_ctor_get(x_3004, 0);
x_3045 = lean_ctor_get(x_3004, 1);
x_3046 = lean_ctor_get(x_3004, 2);
x_3047 = lean_ctor_get(x_3004, 3);
lean_inc(x_3047);
lean_inc(x_3046);
lean_inc(x_3045);
lean_inc(x_3044);
lean_dec(x_3004);
x_3048 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3048, 0, x_3030);
lean_ctor_set(x_3048, 1, x_3031);
lean_ctor_set(x_3048, 2, x_3032);
lean_ctor_set(x_3048, 3, x_3033);
lean_ctor_set_uint8(x_3048, sizeof(void*)*4, x_2855);
lean_ctor_set(x_4, 3, x_2788);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_3048);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_2855);
lean_ctor_set(x_1, 3, x_3047);
lean_ctor_set(x_1, 2, x_3046);
lean_ctor_set(x_1, 1, x_3045);
lean_ctor_set(x_1, 0, x_3044);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2855);
x_3049 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3049, 0, x_4);
lean_ctor_set(x_3049, 1, x_3034);
lean_ctor_set(x_3049, 2, x_3035);
lean_ctor_set(x_3049, 3, x_1);
lean_ctor_set_uint8(x_3049, sizeof(void*)*4, x_3027);
return x_3049;
}
}
else
{
lean_object* x_3050; lean_object* x_3051; lean_object* x_3052; lean_object* x_3053; lean_object* x_3054; lean_object* x_3055; lean_object* x_3056; lean_object* x_3057; lean_object* x_3058; lean_object* x_3059; lean_object* x_3060; lean_object* x_3061; lean_object* x_3062; lean_object* x_3063; 
x_3050 = lean_ctor_get(x_1, 0);
x_3051 = lean_ctor_get(x_1, 1);
x_3052 = lean_ctor_get(x_1, 2);
x_3053 = lean_ctor_get(x_1, 3);
x_3054 = lean_ctor_get(x_4, 1);
x_3055 = lean_ctor_get(x_4, 2);
lean_inc(x_3055);
lean_inc(x_3054);
lean_dec(x_4);
x_3056 = lean_ctor_get(x_3004, 0);
lean_inc(x_3056);
x_3057 = lean_ctor_get(x_3004, 1);
lean_inc(x_3057);
x_3058 = lean_ctor_get(x_3004, 2);
lean_inc(x_3058);
x_3059 = lean_ctor_get(x_3004, 3);
lean_inc(x_3059);
if (lean_is_exclusive(x_3004)) {
 lean_ctor_release(x_3004, 0);
 lean_ctor_release(x_3004, 1);
 lean_ctor_release(x_3004, 2);
 lean_ctor_release(x_3004, 3);
 x_3060 = x_3004;
} else {
 lean_dec_ref(x_3004);
 x_3060 = lean_box(0);
}
if (lean_is_scalar(x_3060)) {
 x_3061 = lean_alloc_ctor(1, 4, 1);
} else {
 x_3061 = x_3060;
}
lean_ctor_set(x_3061, 0, x_3050);
lean_ctor_set(x_3061, 1, x_3051);
lean_ctor_set(x_3061, 2, x_3052);
lean_ctor_set(x_3061, 3, x_3053);
lean_ctor_set_uint8(x_3061, sizeof(void*)*4, x_2855);
x_3062 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3062, 0, x_3061);
lean_ctor_set(x_3062, 1, x_2);
lean_ctor_set(x_3062, 2, x_3);
lean_ctor_set(x_3062, 3, x_2788);
lean_ctor_set_uint8(x_3062, sizeof(void*)*4, x_2855);
lean_ctor_set(x_1, 3, x_3059);
lean_ctor_set(x_1, 2, x_3058);
lean_ctor_set(x_1, 1, x_3057);
lean_ctor_set(x_1, 0, x_3056);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2855);
x_3063 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3063, 0, x_3062);
lean_ctor_set(x_3063, 1, x_3054);
lean_ctor_set(x_3063, 2, x_3055);
lean_ctor_set(x_3063, 3, x_1);
lean_ctor_set_uint8(x_3063, sizeof(void*)*4, x_3027);
return x_3063;
}
}
else
{
lean_object* x_3064; lean_object* x_3065; lean_object* x_3066; lean_object* x_3067; lean_object* x_3068; lean_object* x_3069; lean_object* x_3070; lean_object* x_3071; lean_object* x_3072; lean_object* x_3073; lean_object* x_3074; lean_object* x_3075; lean_object* x_3076; lean_object* x_3077; lean_object* x_3078; lean_object* x_3079; 
x_3064 = lean_ctor_get(x_1, 0);
x_3065 = lean_ctor_get(x_1, 1);
x_3066 = lean_ctor_get(x_1, 2);
x_3067 = lean_ctor_get(x_1, 3);
lean_inc(x_3067);
lean_inc(x_3066);
lean_inc(x_3065);
lean_inc(x_3064);
lean_dec(x_1);
x_3068 = lean_ctor_get(x_4, 1);
lean_inc(x_3068);
x_3069 = lean_ctor_get(x_4, 2);
lean_inc(x_3069);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_3070 = x_4;
} else {
 lean_dec_ref(x_4);
 x_3070 = lean_box(0);
}
x_3071 = lean_ctor_get(x_3004, 0);
lean_inc(x_3071);
x_3072 = lean_ctor_get(x_3004, 1);
lean_inc(x_3072);
x_3073 = lean_ctor_get(x_3004, 2);
lean_inc(x_3073);
x_3074 = lean_ctor_get(x_3004, 3);
lean_inc(x_3074);
if (lean_is_exclusive(x_3004)) {
 lean_ctor_release(x_3004, 0);
 lean_ctor_release(x_3004, 1);
 lean_ctor_release(x_3004, 2);
 lean_ctor_release(x_3004, 3);
 x_3075 = x_3004;
} else {
 lean_dec_ref(x_3004);
 x_3075 = lean_box(0);
}
if (lean_is_scalar(x_3075)) {
 x_3076 = lean_alloc_ctor(1, 4, 1);
} else {
 x_3076 = x_3075;
}
lean_ctor_set(x_3076, 0, x_3064);
lean_ctor_set(x_3076, 1, x_3065);
lean_ctor_set(x_3076, 2, x_3066);
lean_ctor_set(x_3076, 3, x_3067);
lean_ctor_set_uint8(x_3076, sizeof(void*)*4, x_2855);
if (lean_is_scalar(x_3070)) {
 x_3077 = lean_alloc_ctor(1, 4, 1);
} else {
 x_3077 = x_3070;
}
lean_ctor_set(x_3077, 0, x_3076);
lean_ctor_set(x_3077, 1, x_2);
lean_ctor_set(x_3077, 2, x_3);
lean_ctor_set(x_3077, 3, x_2788);
lean_ctor_set_uint8(x_3077, sizeof(void*)*4, x_2855);
x_3078 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3078, 0, x_3071);
lean_ctor_set(x_3078, 1, x_3072);
lean_ctor_set(x_3078, 2, x_3073);
lean_ctor_set(x_3078, 3, x_3074);
lean_ctor_set_uint8(x_3078, sizeof(void*)*4, x_2855);
x_3079 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3079, 0, x_3077);
lean_ctor_set(x_3079, 1, x_3068);
lean_ctor_set(x_3079, 2, x_3069);
lean_ctor_set(x_3079, 3, x_3078);
lean_ctor_set_uint8(x_3079, sizeof(void*)*4, x_3027);
return x_3079;
}
}
else
{
uint8_t x_3080; 
x_3080 = !lean_is_exclusive(x_1);
if (x_3080 == 0)
{
uint8_t x_3081; 
x_3081 = !lean_is_exclusive(x_4);
if (x_3081 == 0)
{
lean_object* x_3082; lean_object* x_3083; lean_object* x_3084; lean_object* x_3085; lean_object* x_3086; lean_object* x_3087; lean_object* x_3088; lean_object* x_3089; uint8_t x_3090; 
x_3082 = lean_ctor_get(x_1, 0);
x_3083 = lean_ctor_get(x_1, 1);
x_3084 = lean_ctor_get(x_1, 2);
x_3085 = lean_ctor_get(x_1, 3);
x_3086 = lean_ctor_get(x_4, 1);
x_3087 = lean_ctor_get(x_4, 2);
x_3088 = lean_ctor_get(x_4, 3);
lean_dec(x_3088);
x_3089 = lean_ctor_get(x_4, 0);
lean_dec(x_3089);
x_3090 = !lean_is_exclusive(x_2788);
if (x_3090 == 0)
{
lean_object* x_3091; lean_object* x_3092; lean_object* x_3093; lean_object* x_3094; lean_object* x_3095; 
x_3091 = lean_ctor_get(x_2788, 0);
x_3092 = lean_ctor_get(x_2788, 1);
x_3093 = lean_ctor_get(x_2788, 2);
x_3094 = lean_ctor_get(x_2788, 3);
lean_ctor_set(x_2788, 3, x_3085);
lean_ctor_set(x_2788, 2, x_3084);
lean_ctor_set(x_2788, 1, x_3083);
lean_ctor_set(x_2788, 0, x_3082);
lean_ctor_set_uint8(x_2788, sizeof(void*)*4, x_3027);
lean_ctor_set(x_4, 3, x_3094);
lean_ctor_set(x_4, 2, x_3093);
lean_ctor_set(x_4, 1, x_3092);
lean_ctor_set(x_4, 0, x_3091);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_3027);
lean_ctor_set(x_1, 3, x_3004);
lean_ctor_set(x_1, 2, x_3087);
lean_ctor_set(x_1, 1, x_3086);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2787);
x_3095 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3095, 0, x_2788);
lean_ctor_set(x_3095, 1, x_2);
lean_ctor_set(x_3095, 2, x_3);
lean_ctor_set(x_3095, 3, x_1);
lean_ctor_set_uint8(x_3095, sizeof(void*)*4, x_3027);
return x_3095;
}
else
{
lean_object* x_3096; lean_object* x_3097; lean_object* x_3098; lean_object* x_3099; lean_object* x_3100; lean_object* x_3101; 
x_3096 = lean_ctor_get(x_2788, 0);
x_3097 = lean_ctor_get(x_2788, 1);
x_3098 = lean_ctor_get(x_2788, 2);
x_3099 = lean_ctor_get(x_2788, 3);
lean_inc(x_3099);
lean_inc(x_3098);
lean_inc(x_3097);
lean_inc(x_3096);
lean_dec(x_2788);
x_3100 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3100, 0, x_3082);
lean_ctor_set(x_3100, 1, x_3083);
lean_ctor_set(x_3100, 2, x_3084);
lean_ctor_set(x_3100, 3, x_3085);
lean_ctor_set_uint8(x_3100, sizeof(void*)*4, x_3027);
lean_ctor_set(x_4, 3, x_3099);
lean_ctor_set(x_4, 2, x_3098);
lean_ctor_set(x_4, 1, x_3097);
lean_ctor_set(x_4, 0, x_3096);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_3027);
lean_ctor_set(x_1, 3, x_3004);
lean_ctor_set(x_1, 2, x_3087);
lean_ctor_set(x_1, 1, x_3086);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2787);
x_3101 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3101, 0, x_3100);
lean_ctor_set(x_3101, 1, x_2);
lean_ctor_set(x_3101, 2, x_3);
lean_ctor_set(x_3101, 3, x_1);
lean_ctor_set_uint8(x_3101, sizeof(void*)*4, x_3027);
return x_3101;
}
}
else
{
lean_object* x_3102; lean_object* x_3103; lean_object* x_3104; lean_object* x_3105; lean_object* x_3106; lean_object* x_3107; lean_object* x_3108; lean_object* x_3109; lean_object* x_3110; lean_object* x_3111; lean_object* x_3112; lean_object* x_3113; lean_object* x_3114; lean_object* x_3115; 
x_3102 = lean_ctor_get(x_1, 0);
x_3103 = lean_ctor_get(x_1, 1);
x_3104 = lean_ctor_get(x_1, 2);
x_3105 = lean_ctor_get(x_1, 3);
x_3106 = lean_ctor_get(x_4, 1);
x_3107 = lean_ctor_get(x_4, 2);
lean_inc(x_3107);
lean_inc(x_3106);
lean_dec(x_4);
x_3108 = lean_ctor_get(x_2788, 0);
lean_inc(x_3108);
x_3109 = lean_ctor_get(x_2788, 1);
lean_inc(x_3109);
x_3110 = lean_ctor_get(x_2788, 2);
lean_inc(x_3110);
x_3111 = lean_ctor_get(x_2788, 3);
lean_inc(x_3111);
if (lean_is_exclusive(x_2788)) {
 lean_ctor_release(x_2788, 0);
 lean_ctor_release(x_2788, 1);
 lean_ctor_release(x_2788, 2);
 lean_ctor_release(x_2788, 3);
 x_3112 = x_2788;
} else {
 lean_dec_ref(x_2788);
 x_3112 = lean_box(0);
}
if (lean_is_scalar(x_3112)) {
 x_3113 = lean_alloc_ctor(1, 4, 1);
} else {
 x_3113 = x_3112;
}
lean_ctor_set(x_3113, 0, x_3102);
lean_ctor_set(x_3113, 1, x_3103);
lean_ctor_set(x_3113, 2, x_3104);
lean_ctor_set(x_3113, 3, x_3105);
lean_ctor_set_uint8(x_3113, sizeof(void*)*4, x_3027);
x_3114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3114, 0, x_3108);
lean_ctor_set(x_3114, 1, x_3109);
lean_ctor_set(x_3114, 2, x_3110);
lean_ctor_set(x_3114, 3, x_3111);
lean_ctor_set_uint8(x_3114, sizeof(void*)*4, x_3027);
lean_ctor_set(x_1, 3, x_3004);
lean_ctor_set(x_1, 2, x_3107);
lean_ctor_set(x_1, 1, x_3106);
lean_ctor_set(x_1, 0, x_3114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2787);
x_3115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3115, 0, x_3113);
lean_ctor_set(x_3115, 1, x_2);
lean_ctor_set(x_3115, 2, x_3);
lean_ctor_set(x_3115, 3, x_1);
lean_ctor_set_uint8(x_3115, sizeof(void*)*4, x_3027);
return x_3115;
}
}
else
{
lean_object* x_3116; lean_object* x_3117; lean_object* x_3118; lean_object* x_3119; lean_object* x_3120; lean_object* x_3121; lean_object* x_3122; lean_object* x_3123; lean_object* x_3124; lean_object* x_3125; lean_object* x_3126; lean_object* x_3127; lean_object* x_3128; lean_object* x_3129; lean_object* x_3130; lean_object* x_3131; 
x_3116 = lean_ctor_get(x_1, 0);
x_3117 = lean_ctor_get(x_1, 1);
x_3118 = lean_ctor_get(x_1, 2);
x_3119 = lean_ctor_get(x_1, 3);
lean_inc(x_3119);
lean_inc(x_3118);
lean_inc(x_3117);
lean_inc(x_3116);
lean_dec(x_1);
x_3120 = lean_ctor_get(x_4, 1);
lean_inc(x_3120);
x_3121 = lean_ctor_get(x_4, 2);
lean_inc(x_3121);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_3122 = x_4;
} else {
 lean_dec_ref(x_4);
 x_3122 = lean_box(0);
}
x_3123 = lean_ctor_get(x_2788, 0);
lean_inc(x_3123);
x_3124 = lean_ctor_get(x_2788, 1);
lean_inc(x_3124);
x_3125 = lean_ctor_get(x_2788, 2);
lean_inc(x_3125);
x_3126 = lean_ctor_get(x_2788, 3);
lean_inc(x_3126);
if (lean_is_exclusive(x_2788)) {
 lean_ctor_release(x_2788, 0);
 lean_ctor_release(x_2788, 1);
 lean_ctor_release(x_2788, 2);
 lean_ctor_release(x_2788, 3);
 x_3127 = x_2788;
} else {
 lean_dec_ref(x_2788);
 x_3127 = lean_box(0);
}
if (lean_is_scalar(x_3127)) {
 x_3128 = lean_alloc_ctor(1, 4, 1);
} else {
 x_3128 = x_3127;
}
lean_ctor_set(x_3128, 0, x_3116);
lean_ctor_set(x_3128, 1, x_3117);
lean_ctor_set(x_3128, 2, x_3118);
lean_ctor_set(x_3128, 3, x_3119);
lean_ctor_set_uint8(x_3128, sizeof(void*)*4, x_3027);
if (lean_is_scalar(x_3122)) {
 x_3129 = lean_alloc_ctor(1, 4, 1);
} else {
 x_3129 = x_3122;
}
lean_ctor_set(x_3129, 0, x_3123);
lean_ctor_set(x_3129, 1, x_3124);
lean_ctor_set(x_3129, 2, x_3125);
lean_ctor_set(x_3129, 3, x_3126);
lean_ctor_set_uint8(x_3129, sizeof(void*)*4, x_3027);
x_3130 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3130, 0, x_3129);
lean_ctor_set(x_3130, 1, x_3120);
lean_ctor_set(x_3130, 2, x_3121);
lean_ctor_set(x_3130, 3, x_3004);
lean_ctor_set_uint8(x_3130, sizeof(void*)*4, x_2787);
x_3131 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3131, 0, x_3128);
lean_ctor_set(x_3131, 1, x_2);
lean_ctor_set(x_3131, 2, x_3);
lean_ctor_set(x_3131, 3, x_3130);
lean_ctor_set_uint8(x_3131, sizeof(void*)*4, x_3027);
return x_3131;
}
}
}
}
}
}
else
{
uint8_t x_3132; 
x_3132 = !lean_is_exclusive(x_1);
if (x_3132 == 0)
{
lean_object* x_3133; 
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_2787);
x_3133 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3133, 0, x_1);
lean_ctor_set(x_3133, 1, x_2);
lean_ctor_set(x_3133, 2, x_3);
lean_ctor_set(x_3133, 3, x_4);
lean_ctor_set_uint8(x_3133, sizeof(void*)*4, x_2787);
return x_3133;
}
else
{
lean_object* x_3134; lean_object* x_3135; lean_object* x_3136; lean_object* x_3137; lean_object* x_3138; lean_object* x_3139; 
x_3134 = lean_ctor_get(x_1, 0);
x_3135 = lean_ctor_get(x_1, 1);
x_3136 = lean_ctor_get(x_1, 2);
x_3137 = lean_ctor_get(x_1, 3);
lean_inc(x_3137);
lean_inc(x_3136);
lean_inc(x_3135);
lean_inc(x_3134);
lean_dec(x_1);
x_3138 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3138, 0, x_3134);
lean_ctor_set(x_3138, 1, x_3135);
lean_ctor_set(x_3138, 2, x_3136);
lean_ctor_set(x_3138, 3, x_3137);
lean_ctor_set_uint8(x_3138, sizeof(void*)*4, x_2787);
x_3139 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_3139, 0, x_3138);
lean_ctor_set(x_3139, 1, x_2);
lean_ctor_set(x_3139, 2, x_3);
lean_ctor_set(x_3139, 3, x_4);
lean_ctor_set_uint8(x_3139, sizeof(void*)*4, x_2787);
return x_3139;
}
}
}
}
}
}
}
lean_object* l_RBNode_balance_u2083(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_balance_u2083___rarg), 4, 0);
return x_3;
}
}
lean_object* l_RBNode_balance_u2083___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_balance_u2083(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_setRed___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_3);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_8 = 0;
x_9 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_8);
return x_9;
}
}
}
}
lean_object* l_RBNode_setRed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_setRed___rarg), 1, 0);
return x_3;
}
}
lean_object* l_RBNode_setRed___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_setRed(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_balLeft___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_8, sizeof(void*)*4);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_10);
x_13 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set_uint8(x_13, sizeof(void*)*4, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*4, x_10);
x_18 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_3);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_10);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_4, 1);
x_21 = lean_ctor_get(x_4, 2);
x_22 = lean_ctor_get(x_4, 3);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
x_27 = lean_ctor_get(x_8, 2);
x_28 = lean_ctor_get(x_8, 3);
lean_ctor_set(x_8, 3, x_25);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
x_29 = l_RBNode_setRed___rarg(x_22);
x_30 = l_RBNode_balance_u2083___rarg(x_28, x_20, x_21, x_29);
lean_ctor_set(x_4, 3, x_30);
lean_ctor_set(x_4, 2, x_27);
lean_ctor_set(x_4, 1, x_26);
return x_4;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
x_33 = lean_ctor_get(x_8, 2);
x_34 = lean_ctor_get(x_8, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_35 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_2);
lean_ctor_set(x_35, 2, x_3);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_10);
x_36 = l_RBNode_setRed___rarg(x_22);
x_37 = l_RBNode_balance_u2083___rarg(x_34, x_20, x_21, x_36);
lean_ctor_set(x_4, 3, x_37);
lean_ctor_set(x_4, 2, x_33);
lean_ctor_set(x_4, 1, x_32);
lean_ctor_set(x_4, 0, x_35);
return x_4;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_4, 1);
x_39 = lean_ctor_get(x_4, 2);
x_40 = lean_ctor_get(x_4, 3);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_4);
x_41 = lean_ctor_get(x_8, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_8, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_8, 3);
lean_inc(x_44);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_45 = x_8;
} else {
 lean_dec_ref(x_8);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 4, 1);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_2);
lean_ctor_set(x_46, 2, x_3);
lean_ctor_set(x_46, 3, x_41);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_10);
x_47 = l_RBNode_setRed___rarg(x_40);
x_48 = l_RBNode_balance_u2083___rarg(x_44, x_38, x_39, x_47);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_7);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_4);
if (x_50 == 0)
{
uint8_t x_51; lean_object* x_52; 
x_51 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_51);
x_52 = l_RBNode_balance_u2083___rarg(x_1, x_2, x_3, x_4);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_4, 0);
x_54 = lean_ctor_get(x_4, 1);
x_55 = lean_ctor_get(x_4, 2);
x_56 = lean_ctor_get(x_4, 3);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_4);
x_57 = 0;
x_58 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_55);
lean_ctor_set(x_58, 3, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_57);
x_59 = l_RBNode_balance_u2083___rarg(x_1, x_2, x_3, x_58);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_1);
if (x_61 == 0)
{
uint8_t x_62; lean_object* x_63; 
x_62 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_62);
x_63 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_2);
lean_ctor_set(x_63, 2, x_3);
lean_ctor_set(x_63, 3, x_4);
lean_ctor_set_uint8(x_63, sizeof(void*)*4, x_60);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_1, 0);
x_65 = lean_ctor_get(x_1, 1);
x_66 = lean_ctor_get(x_1, 2);
x_67 = lean_ctor_get(x_1, 3);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_1);
x_68 = 1;
x_69 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_65);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*4, x_68);
x_70 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_2);
lean_ctor_set(x_70, 2, x_3);
lean_ctor_set(x_70, 3, x_4);
lean_ctor_set_uint8(x_70, sizeof(void*)*4, x_60);
return x_70;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_71; lean_object* x_72; 
x_71 = 0;
x_72 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_2);
lean_ctor_set(x_72, 2, x_3);
lean_ctor_set(x_72, 3, x_4);
lean_ctor_set_uint8(x_72, sizeof(void*)*4, x_71);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_4, 0);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_2);
lean_ctor_set(x_75, 2, x_3);
lean_ctor_set(x_75, 3, x_4);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_73);
return x_75;
}
else
{
uint8_t x_76; 
x_76 = lean_ctor_get_uint8(x_74, sizeof(void*)*4);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_4);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_4, 0);
lean_dec(x_78);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_76);
x_79 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_2);
lean_ctor_set(x_79, 2, x_3);
lean_ctor_set(x_79, 3, x_4);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_76);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_4, 1);
x_81 = lean_ctor_get(x_4, 2);
x_82 = lean_ctor_get(x_4, 3);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_4);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_80);
lean_ctor_set(x_83, 2, x_81);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_76);
x_84 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_84, 0, x_1);
lean_ctor_set(x_84, 1, x_2);
lean_ctor_set(x_84, 2, x_3);
lean_ctor_set(x_84, 3, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_76);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_1);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_4);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_87 = lean_ctor_get(x_1, 0);
x_88 = lean_ctor_get(x_1, 1);
x_89 = lean_ctor_get(x_1, 2);
x_90 = lean_ctor_get(x_1, 3);
x_91 = lean_ctor_get(x_4, 1);
x_92 = lean_ctor_get(x_4, 2);
x_93 = lean_ctor_get(x_4, 3);
x_94 = lean_ctor_get(x_4, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_74);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_74, 0);
x_97 = lean_ctor_get(x_74, 1);
x_98 = lean_ctor_get(x_74, 2);
x_99 = lean_ctor_get(x_74, 3);
lean_ctor_set(x_74, 3, x_90);
lean_ctor_set(x_74, 2, x_89);
lean_ctor_set(x_74, 1, x_88);
lean_ctor_set(x_74, 0, x_87);
lean_ctor_set(x_4, 3, x_96);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_76);
x_100 = l_RBNode_setRed___rarg(x_93);
x_101 = l_RBNode_balance_u2083___rarg(x_99, x_91, x_92, x_100);
lean_ctor_set(x_1, 3, x_101);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_73);
return x_1;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_74, 0);
x_103 = lean_ctor_get(x_74, 1);
x_104 = lean_ctor_get(x_74, 2);
x_105 = lean_ctor_get(x_74, 3);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_74);
x_106 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_106, 0, x_87);
lean_ctor_set(x_106, 1, x_88);
lean_ctor_set(x_106, 2, x_89);
lean_ctor_set(x_106, 3, x_90);
lean_ctor_set_uint8(x_106, sizeof(void*)*4, x_76);
lean_ctor_set(x_4, 3, x_102);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_106);
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_76);
x_107 = l_RBNode_setRed___rarg(x_93);
x_108 = l_RBNode_balance_u2083___rarg(x_105, x_91, x_92, x_107);
lean_ctor_set(x_1, 3, x_108);
lean_ctor_set(x_1, 2, x_104);
lean_ctor_set(x_1, 1, x_103);
lean_ctor_set(x_1, 0, x_4);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_73);
return x_1;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_109 = lean_ctor_get(x_1, 0);
x_110 = lean_ctor_get(x_1, 1);
x_111 = lean_ctor_get(x_1, 2);
x_112 = lean_ctor_get(x_1, 3);
x_113 = lean_ctor_get(x_4, 1);
x_114 = lean_ctor_get(x_4, 2);
x_115 = lean_ctor_get(x_4, 3);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_4);
x_116 = lean_ctor_get(x_74, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_74, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_74, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_74, 3);
lean_inc(x_119);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_120 = x_74;
} else {
 lean_dec_ref(x_74);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 4, 1);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_109);
lean_ctor_set(x_121, 1, x_110);
lean_ctor_set(x_121, 2, x_111);
lean_ctor_set(x_121, 3, x_112);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_76);
x_122 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_2);
lean_ctor_set(x_122, 2, x_3);
lean_ctor_set(x_122, 3, x_116);
lean_ctor_set_uint8(x_122, sizeof(void*)*4, x_76);
x_123 = l_RBNode_setRed___rarg(x_115);
x_124 = l_RBNode_balance_u2083___rarg(x_119, x_113, x_114, x_123);
lean_ctor_set(x_1, 3, x_124);
lean_ctor_set(x_1, 2, x_118);
lean_ctor_set(x_1, 1, x_117);
lean_ctor_set(x_1, 0, x_122);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_73);
return x_1;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_125 = lean_ctor_get(x_1, 0);
x_126 = lean_ctor_get(x_1, 1);
x_127 = lean_ctor_get(x_1, 2);
x_128 = lean_ctor_get(x_1, 3);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_1);
x_129 = lean_ctor_get(x_4, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_4, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_4, 3);
lean_inc(x_131);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_132 = x_4;
} else {
 lean_dec_ref(x_4);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_74, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_74, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_74, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_74, 3);
lean_inc(x_136);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_137 = x_74;
} else {
 lean_dec_ref(x_74);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 4, 1);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_125);
lean_ctor_set(x_138, 1, x_126);
lean_ctor_set(x_138, 2, x_127);
lean_ctor_set(x_138, 3, x_128);
lean_ctor_set_uint8(x_138, sizeof(void*)*4, x_76);
if (lean_is_scalar(x_132)) {
 x_139 = lean_alloc_ctor(1, 4, 1);
} else {
 x_139 = x_132;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_2);
lean_ctor_set(x_139, 2, x_3);
lean_ctor_set(x_139, 3, x_133);
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_76);
x_140 = l_RBNode_setRed___rarg(x_131);
x_141 = l_RBNode_balance_u2083___rarg(x_136, x_129, x_130, x_140);
x_142 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_134);
lean_ctor_set(x_142, 2, x_135);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*4, x_73);
return x_142;
}
}
}
}
else
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_1);
if (x_143 == 0)
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_4);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; 
x_145 = lean_ctor_get(x_1, 0);
x_146 = lean_ctor_get(x_1, 1);
x_147 = lean_ctor_get(x_1, 2);
x_148 = lean_ctor_get(x_1, 3);
x_149 = lean_ctor_get(x_4, 0);
x_150 = lean_ctor_get(x_4, 1);
x_151 = lean_ctor_get(x_4, 2);
x_152 = lean_ctor_get(x_4, 3);
lean_ctor_set(x_4, 3, x_148);
lean_ctor_set(x_4, 2, x_147);
lean_ctor_set(x_4, 1, x_146);
lean_ctor_set(x_4, 0, x_145);
x_153 = 0;
lean_ctor_set(x_1, 3, x_152);
lean_ctor_set(x_1, 2, x_151);
lean_ctor_set(x_1, 1, x_150);
lean_ctor_set(x_1, 0, x_149);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_153);
x_154 = l_RBNode_balance_u2083___rarg(x_4, x_2, x_3, x_1);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; 
x_155 = lean_ctor_get(x_1, 0);
x_156 = lean_ctor_get(x_1, 1);
x_157 = lean_ctor_get(x_1, 2);
x_158 = lean_ctor_get(x_1, 3);
x_159 = lean_ctor_get(x_4, 0);
x_160 = lean_ctor_get(x_4, 1);
x_161 = lean_ctor_get(x_4, 2);
x_162 = lean_ctor_get(x_4, 3);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_4);
x_163 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_163, 0, x_155);
lean_ctor_set(x_163, 1, x_156);
lean_ctor_set(x_163, 2, x_157);
lean_ctor_set(x_163, 3, x_158);
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_73);
x_164 = 0;
lean_ctor_set(x_1, 3, x_162);
lean_ctor_set(x_1, 2, x_161);
lean_ctor_set(x_1, 1, x_160);
lean_ctor_set(x_1, 0, x_159);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_164);
x_165 = l_RBNode_balance_u2083___rarg(x_163, x_2, x_3, x_1);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; 
x_166 = lean_ctor_get(x_1, 0);
x_167 = lean_ctor_get(x_1, 1);
x_168 = lean_ctor_get(x_1, 2);
x_169 = lean_ctor_get(x_1, 3);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_1);
x_170 = lean_ctor_get(x_4, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_4, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_4, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_4, 3);
lean_inc(x_173);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_174 = x_4;
} else {
 lean_dec_ref(x_4);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 4, 1);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_166);
lean_ctor_set(x_175, 1, x_167);
lean_ctor_set(x_175, 2, x_168);
lean_ctor_set(x_175, 3, x_169);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_73);
x_176 = 0;
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_170);
lean_ctor_set(x_177, 1, x_171);
lean_ctor_set(x_177, 2, x_172);
lean_ctor_set(x_177, 3, x_173);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_176);
x_178 = l_RBNode_balance_u2083___rarg(x_175, x_2, x_3, x_177);
return x_178;
}
}
}
}
}
}
}
lean_object* l_RBNode_balLeft(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_balLeft___rarg), 4, 0);
return x_3;
}
}
lean_object* l_RBNode_balLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_balLeft(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_balRight___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*4, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_8, sizeof(void*)*4);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_16; 
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_3);
lean_ctor_set(x_16, 3, x_4);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_10);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
x_25 = lean_ctor_get(x_8, 2);
x_26 = lean_ctor_get(x_8, 3);
x_27 = l_RBNode_setRed___rarg(x_18);
x_28 = l_RBNode_balance_u2083___rarg(x_27, x_19, x_20, x_23);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 0, x_26);
lean_ctor_set(x_1, 2, x_25);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_1, 0, x_28);
return x_1;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_8, 0);
x_30 = lean_ctor_get(x_8, 1);
x_31 = lean_ctor_get(x_8, 2);
x_32 = lean_ctor_get(x_8, 3);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_8);
x_33 = l_RBNode_setRed___rarg(x_18);
x_34 = l_RBNode_balance_u2083___rarg(x_33, x_19, x_20, x_29);
x_35 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_2);
lean_ctor_set(x_35, 2, x_3);
lean_ctor_set(x_35, 3, x_4);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_10);
lean_ctor_set(x_1, 3, x_35);
lean_ctor_set(x_1, 2, x_31);
lean_ctor_set(x_1, 1, x_30);
lean_ctor_set(x_1, 0, x_34);
return x_1;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_1, 1);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_1);
x_39 = lean_ctor_get(x_8, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_8, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_8, 3);
lean_inc(x_42);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_43 = x_8;
} else {
 lean_dec_ref(x_8);
 x_43 = lean_box(0);
}
x_44 = l_RBNode_setRed___rarg(x_36);
x_45 = l_RBNode_balance_u2083___rarg(x_44, x_37, x_38, x_39);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(1, 4, 1);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_2);
lean_ctor_set(x_46, 2, x_3);
lean_ctor_set(x_46, 3, x_4);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_10);
x_47 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_40);
lean_ctor_set(x_47, 2, x_41);
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_7);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
uint8_t x_49; lean_object* x_50; 
x_49 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
x_50 = l_RBNode_balance_u2083___rarg(x_1, x_2, x_3, x_4);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_1, 0);
x_52 = lean_ctor_get(x_1, 1);
x_53 = lean_ctor_get(x_1, 2);
x_54 = lean_ctor_get(x_1, 3);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_1);
x_55 = 0;
x_56 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_52);
lean_ctor_set(x_56, 2, x_53);
lean_ctor_set(x_56, 3, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_55);
x_57 = l_RBNode_balance_u2083___rarg(x_56, x_2, x_3, x_4);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
x_58 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_4);
if (x_59 == 0)
{
uint8_t x_60; lean_object* x_61; 
x_60 = 1;
lean_ctor_set_uint8(x_4, sizeof(void*)*4, x_60);
x_61 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_2);
lean_ctor_set(x_61, 2, x_3);
lean_ctor_set(x_61, 3, x_4);
lean_ctor_set_uint8(x_61, sizeof(void*)*4, x_58);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_4, 0);
x_63 = lean_ctor_get(x_4, 1);
x_64 = lean_ctor_get(x_4, 2);
x_65 = lean_ctor_get(x_4, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_4);
x_66 = 1;
x_67 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_63);
lean_ctor_set(x_67, 2, x_64);
lean_ctor_set(x_67, 3, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*4, x_66);
x_68 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_2);
lean_ctor_set(x_68, 2, x_3);
lean_ctor_set(x_68, 3, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_58);
return x_68;
}
}
else
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_69; lean_object* x_70; 
x_69 = 0;
x_70 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_2);
lean_ctor_set(x_70, 2, x_3);
lean_ctor_set(x_70, 3, x_4);
lean_ctor_set_uint8(x_70, sizeof(void*)*4, x_69);
return x_70;
}
else
{
uint8_t x_71; 
x_71 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_1, 3);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_2);
lean_ctor_set(x_73, 2, x_3);
lean_ctor_set(x_73, 3, x_4);
lean_ctor_set_uint8(x_73, sizeof(void*)*4, x_71);
return x_73;
}
else
{
uint8_t x_74; 
x_74 = lean_ctor_get_uint8(x_72, sizeof(void*)*4);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_72, 3);
lean_dec(x_76);
x_77 = lean_ctor_get(x_72, 2);
lean_dec(x_77);
x_78 = lean_ctor_get(x_72, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_72, 0);
lean_dec(x_79);
lean_ctor_set(x_72, 3, x_4);
lean_ctor_set(x_72, 2, x_3);
lean_ctor_set(x_72, 1, x_2);
lean_ctor_set(x_72, 0, x_1);
return x_72;
}
else
{
lean_object* x_80; 
lean_dec(x_72);
x_80 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_2);
lean_ctor_set(x_80, 2, x_3);
lean_ctor_set(x_80, 3, x_4);
lean_ctor_set_uint8(x_80, sizeof(void*)*4, x_74);
return x_80;
}
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_1);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_1, 0);
x_83 = lean_ctor_get(x_1, 1);
x_84 = lean_ctor_get(x_1, 2);
x_85 = lean_ctor_get(x_1, 3);
lean_dec(x_85);
x_86 = !lean_is_exclusive(x_72);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_72, 0);
x_88 = lean_ctor_get(x_72, 1);
x_89 = lean_ctor_get(x_72, 2);
x_90 = lean_ctor_get(x_72, 3);
x_91 = l_RBNode_setRed___rarg(x_82);
x_92 = l_RBNode_balance_u2083___rarg(x_91, x_83, x_84, x_87);
lean_ctor_set(x_72, 3, x_4);
lean_ctor_set(x_72, 2, x_3);
lean_ctor_set(x_72, 1, x_2);
lean_ctor_set(x_72, 0, x_90);
lean_ctor_set(x_1, 2, x_89);
lean_ctor_set(x_1, 1, x_88);
lean_ctor_set(x_1, 0, x_92);
return x_1;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_72, 0);
x_94 = lean_ctor_get(x_72, 1);
x_95 = lean_ctor_get(x_72, 2);
x_96 = lean_ctor_get(x_72, 3);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_72);
x_97 = l_RBNode_setRed___rarg(x_82);
x_98 = l_RBNode_balance_u2083___rarg(x_97, x_83, x_84, x_93);
x_99 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_2);
lean_ctor_set(x_99, 2, x_3);
lean_ctor_set(x_99, 3, x_4);
lean_ctor_set_uint8(x_99, sizeof(void*)*4, x_74);
lean_ctor_set(x_1, 3, x_99);
lean_ctor_set(x_1, 2, x_95);
lean_ctor_set(x_1, 1, x_94);
lean_ctor_set(x_1, 0, x_98);
return x_1;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_100 = lean_ctor_get(x_1, 0);
x_101 = lean_ctor_get(x_1, 1);
x_102 = lean_ctor_get(x_1, 2);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_1);
x_103 = lean_ctor_get(x_72, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_72, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_72, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_72, 3);
lean_inc(x_106);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 x_107 = x_72;
} else {
 lean_dec_ref(x_72);
 x_107 = lean_box(0);
}
x_108 = l_RBNode_setRed___rarg(x_100);
x_109 = l_RBNode_balance_u2083___rarg(x_108, x_101, x_102, x_103);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(1, 4, 1);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_2);
lean_ctor_set(x_110, 2, x_3);
lean_ctor_set(x_110, 3, x_4);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_74);
x_111 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_104);
lean_ctor_set(x_111, 2, x_105);
lean_ctor_set(x_111, 3, x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_71);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_1);
if (x_112 == 0)
{
uint8_t x_113; lean_object* x_114; 
x_113 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_113);
x_114 = l_RBNode_balance_u2083___rarg(x_1, x_2, x_3, x_4);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_1, 0);
x_116 = lean_ctor_get(x_1, 1);
x_117 = lean_ctor_get(x_1, 2);
x_118 = lean_ctor_get(x_1, 3);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_1);
x_119 = 0;
x_120 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_120, 0, x_115);
lean_ctor_set(x_120, 1, x_116);
lean_ctor_set(x_120, 2, x_117);
lean_ctor_set(x_120, 3, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_119);
x_121 = l_RBNode_balance_u2083___rarg(x_120, x_2, x_3, x_4);
return x_121;
}
}
}
}
}
}
}
lean_object* l_RBNode_balRight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_balRight___rarg), 4, 0);
return x_3;
}
}
lean_object* l_RBNode_balRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_balRight(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_appendTrees___main___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_3 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_2, 0);
x_12 = l_RBNode_appendTrees___main___rarg(x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_ctor_set(x_2, 0, x_12);
lean_ctor_set(x_1, 3, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_4);
return x_1;
}
else
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*4);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 2);
x_18 = lean_ctor_get(x_12, 3);
lean_ctor_set(x_12, 3, x_15);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_2, 0, x_18);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_13);
lean_ctor_set(x_1, 3, x_2);
lean_ctor_set(x_1, 2, x_17);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_12);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_13);
return x_1;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
x_21 = lean_ctor_get(x_12, 2);
x_22 = lean_ctor_get(x_12, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_8);
lean_ctor_set(x_23, 2, x_9);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*4, x_13);
lean_ctor_set(x_2, 0, x_22);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_13);
lean_ctor_set(x_1, 3, x_2);
lean_ctor_set(x_1, 2, x_21);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_23);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_13);
return x_1;
}
}
else
{
lean_ctor_set(x_2, 0, x_12);
lean_ctor_set(x_1, 3, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_4);
return x_1;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 2);
x_27 = lean_ctor_get(x_1, 3);
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = lean_ctor_get(x_2, 2);
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
x_32 = l_RBNode_appendTrees___main___rarg(x_27, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_4);
lean_ctor_set(x_1, 3, x_33);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_4);
return x_1;
}
else
{
uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_32, sizeof(void*)*4);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 3);
lean_inc(x_38);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 x_39 = x_32;
} else {
 lean_dec_ref(x_32);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 4, 1);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_24);
lean_ctor_set(x_40, 1, x_25);
lean_ctor_set(x_40, 2, x_26);
lean_ctor_set(x_40, 3, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_34);
x_41 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_29);
lean_ctor_set(x_41, 2, x_30);
lean_ctor_set(x_41, 3, x_31);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_34);
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_37);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_40);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_34);
return x_1;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_42, 0, x_32);
lean_ctor_set(x_42, 1, x_29);
lean_ctor_set(x_42, 2, x_30);
lean_ctor_set(x_42, 3, x_31);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_4);
lean_ctor_set(x_1, 3, x_42);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_4);
return x_1;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
x_45 = lean_ctor_get(x_1, 2);
x_46 = lean_ctor_get(x_1, 3);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_1);
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 3);
lean_inc(x_50);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_51 = x_2;
} else {
 lean_dec_ref(x_2);
 x_51 = lean_box(0);
}
x_52 = l_RBNode_appendTrees___main___rarg(x_46, x_47);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(1, 4, 1);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_4);
x_54 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_44);
lean_ctor_set(x_54, 2, x_45);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_4);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = lean_ctor_get_uint8(x_52, sizeof(void*)*4);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 3);
lean_inc(x_59);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 x_60 = x_52;
} else {
 lean_dec_ref(x_52);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 4, 1);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_43);
lean_ctor_set(x_61, 1, x_44);
lean_ctor_set(x_61, 2, x_45);
lean_ctor_set(x_61, 3, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*4, x_55);
if (lean_is_scalar(x_51)) {
 x_62 = lean_alloc_ctor(1, 4, 1);
} else {
 x_62 = x_51;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_48);
lean_ctor_set(x_62, 2, x_49);
lean_ctor_set(x_62, 3, x_50);
lean_ctor_set_uint8(x_62, sizeof(void*)*4, x_55);
x_63 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_57);
lean_ctor_set(x_63, 2, x_58);
lean_ctor_set(x_63, 3, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*4, x_55);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
if (lean_is_scalar(x_51)) {
 x_64 = lean_alloc_ctor(1, 4, 1);
} else {
 x_64 = x_51;
}
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_48);
lean_ctor_set(x_64, 2, x_49);
lean_ctor_set(x_64, 3, x_50);
lean_ctor_set_uint8(x_64, sizeof(void*)*4, x_4);
x_65 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_65, 0, x_43);
lean_ctor_set(x_65, 1, x_44);
lean_ctor_set(x_65, 2, x_45);
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*4, x_4);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 3);
lean_inc(x_69);
lean_dec(x_1);
lean_inc(x_2);
x_70 = l_RBNode_appendTrees___main___rarg(x_69, x_2);
x_71 = !lean_is_exclusive(x_2);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_2, 3);
lean_dec(x_72);
x_73 = lean_ctor_get(x_2, 2);
lean_dec(x_73);
x_74 = lean_ctor_get(x_2, 1);
lean_dec(x_74);
x_75 = lean_ctor_get(x_2, 0);
lean_dec(x_75);
lean_ctor_set(x_2, 3, x_70);
lean_ctor_set(x_2, 2, x_68);
lean_ctor_set(x_2, 1, x_67);
lean_ctor_set(x_2, 0, x_66);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_3);
return x_2;
}
else
{
lean_object* x_76; 
lean_dec(x_2);
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_66);
lean_ctor_set(x_76, 1, x_67);
lean_ctor_set(x_76, 2, x_68);
lean_ctor_set(x_76, 3, x_70);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_3);
return x_76;
}
}
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_77; 
x_77 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_2);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_2, 0);
x_80 = l_RBNode_appendTrees___main___rarg(x_1, x_79);
lean_ctor_set(x_2, 0, x_80);
return x_2;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_2, 0);
x_82 = lean_ctor_get(x_2, 1);
x_83 = lean_ctor_get(x_2, 2);
x_84 = lean_ctor_get(x_2, 3);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_2);
x_85 = l_RBNode_appendTrees___main___rarg(x_1, x_81);
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_82);
lean_ctor_set(x_86, 2, x_83);
lean_ctor_set(x_86, 3, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_77);
return x_86;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_1);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_2);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_1, 0);
x_90 = lean_ctor_get(x_1, 1);
x_91 = lean_ctor_get(x_1, 2);
x_92 = lean_ctor_get(x_1, 3);
x_93 = lean_ctor_get(x_2, 0);
x_94 = l_RBNode_appendTrees___main___rarg(x_92, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
lean_free_object(x_1);
lean_ctor_set(x_2, 0, x_94);
x_95 = l_RBNode_balLeft___rarg(x_89, x_90, x_91, x_2);
return x_95;
}
else
{
uint8_t x_96; 
x_96 = lean_ctor_get_uint8(x_94, sizeof(void*)*4);
if (x_96 == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_94);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_94, 0);
x_99 = lean_ctor_get(x_94, 1);
x_100 = lean_ctor_get(x_94, 2);
x_101 = lean_ctor_get(x_94, 3);
lean_ctor_set(x_94, 3, x_98);
lean_ctor_set(x_94, 2, x_91);
lean_ctor_set(x_94, 1, x_90);
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_77);
lean_ctor_set(x_2, 0, x_101);
lean_ctor_set(x_1, 3, x_2);
lean_ctor_set(x_1, 2, x_100);
lean_ctor_set(x_1, 1, x_99);
lean_ctor_set(x_1, 0, x_94);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_96);
return x_1;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_94, 0);
x_103 = lean_ctor_get(x_94, 1);
x_104 = lean_ctor_get(x_94, 2);
x_105 = lean_ctor_get(x_94, 3);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_94);
x_106 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_106, 0, x_89);
lean_ctor_set(x_106, 1, x_90);
lean_ctor_set(x_106, 2, x_91);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set_uint8(x_106, sizeof(void*)*4, x_77);
lean_ctor_set(x_2, 0, x_105);
lean_ctor_set(x_1, 3, x_2);
lean_ctor_set(x_1, 2, x_104);
lean_ctor_set(x_1, 1, x_103);
lean_ctor_set(x_1, 0, x_106);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_96);
return x_1;
}
}
else
{
lean_object* x_107; 
lean_free_object(x_1);
lean_ctor_set(x_2, 0, x_94);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_96);
x_107 = l_RBNode_balLeft___rarg(x_89, x_90, x_91, x_2);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_108 = lean_ctor_get(x_1, 0);
x_109 = lean_ctor_get(x_1, 1);
x_110 = lean_ctor_get(x_1, 2);
x_111 = lean_ctor_get(x_1, 3);
x_112 = lean_ctor_get(x_2, 0);
x_113 = lean_ctor_get(x_2, 1);
x_114 = lean_ctor_get(x_2, 2);
x_115 = lean_ctor_get(x_2, 3);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_2);
x_116 = l_RBNode_appendTrees___main___rarg(x_111, x_112);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_free_object(x_1);
x_117 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_113);
lean_ctor_set(x_117, 2, x_114);
lean_ctor_set(x_117, 3, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_77);
x_118 = l_RBNode_balLeft___rarg(x_108, x_109, x_110, x_117);
return x_118;
}
else
{
uint8_t x_119; 
x_119 = lean_ctor_get_uint8(x_116, sizeof(void*)*4);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_116, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_116, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_116, 3);
lean_inc(x_123);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 lean_ctor_release(x_116, 3);
 x_124 = x_116;
} else {
 lean_dec_ref(x_116);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 4, 1);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_108);
lean_ctor_set(x_125, 1, x_109);
lean_ctor_set(x_125, 2, x_110);
lean_ctor_set(x_125, 3, x_120);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_77);
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_113);
lean_ctor_set(x_126, 2, x_114);
lean_ctor_set(x_126, 3, x_115);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_77);
lean_ctor_set(x_1, 3, x_126);
lean_ctor_set(x_1, 2, x_122);
lean_ctor_set(x_1, 1, x_121);
lean_ctor_set(x_1, 0, x_125);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_119);
return x_1;
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_free_object(x_1);
x_127 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_127, 0, x_116);
lean_ctor_set(x_127, 1, x_113);
lean_ctor_set(x_127, 2, x_114);
lean_ctor_set(x_127, 3, x_115);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_119);
x_128 = l_RBNode_balLeft___rarg(x_108, x_109, x_110, x_127);
return x_128;
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_129 = lean_ctor_get(x_1, 0);
x_130 = lean_ctor_get(x_1, 1);
x_131 = lean_ctor_get(x_1, 2);
x_132 = lean_ctor_get(x_1, 3);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_1);
x_133 = lean_ctor_get(x_2, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_2, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_2, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_2, 3);
lean_inc(x_136);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_137 = x_2;
} else {
 lean_dec_ref(x_2);
 x_137 = lean_box(0);
}
x_138 = l_RBNode_appendTrees___main___rarg(x_132, x_133);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; 
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(1, 4, 1);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_134);
lean_ctor_set(x_139, 2, x_135);
lean_ctor_set(x_139, 3, x_136);
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_77);
x_140 = l_RBNode_balLeft___rarg(x_129, x_130, x_131, x_139);
return x_140;
}
else
{
uint8_t x_141; 
x_141 = lean_ctor_get_uint8(x_138, sizeof(void*)*4);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_138, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_138, 2);
lean_inc(x_144);
x_145 = lean_ctor_get(x_138, 3);
lean_inc(x_145);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 lean_ctor_release(x_138, 2);
 lean_ctor_release(x_138, 3);
 x_146 = x_138;
} else {
 lean_dec_ref(x_138);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 4, 1);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_129);
lean_ctor_set(x_147, 1, x_130);
lean_ctor_set(x_147, 2, x_131);
lean_ctor_set(x_147, 3, x_142);
lean_ctor_set_uint8(x_147, sizeof(void*)*4, x_77);
if (lean_is_scalar(x_137)) {
 x_148 = lean_alloc_ctor(1, 4, 1);
} else {
 x_148 = x_137;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_134);
lean_ctor_set(x_148, 2, x_135);
lean_ctor_set(x_148, 3, x_136);
lean_ctor_set_uint8(x_148, sizeof(void*)*4, x_77);
x_149 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_143);
lean_ctor_set(x_149, 2, x_144);
lean_ctor_set(x_149, 3, x_148);
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_141);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; 
if (lean_is_scalar(x_137)) {
 x_150 = lean_alloc_ctor(1, 4, 1);
} else {
 x_150 = x_137;
}
lean_ctor_set(x_150, 0, x_138);
lean_ctor_set(x_150, 1, x_134);
lean_ctor_set(x_150, 2, x_135);
lean_ctor_set(x_150, 3, x_136);
lean_ctor_set_uint8(x_150, sizeof(void*)*4, x_141);
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
lean_object* l_RBNode_appendTrees___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_appendTrees___main___rarg), 2, 0);
return x_3;
}
}
lean_object* l_RBNode_appendTrees___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_appendTrees___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_appendTrees___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_appendTrees___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_RBNode_appendTrees(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_appendTrees___rarg), 2, 0);
return x_3;
}
}
lean_object* l_RBNode_appendTrees___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_appendTrees(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_del___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_6);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_6);
x_11 = lean_apply_2(x_1, x_6, x_2);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_free_object(x_3);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_RBNode_appendTrees___main___rarg(x_5, x_8);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = l_RBNode_isBlack___rarg(x_8);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_RBNode_del___main___rarg(x_1, x_2, x_8);
x_16 = 0;
lean_ctor_set(x_3, 3, x_15);
lean_ctor_set_uint8(x_3, sizeof(void*)*4, x_16);
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_3);
x_17 = l_RBNode_del___main___rarg(x_1, x_2, x_8);
x_18 = l_RBNode_balRight___rarg(x_5, x_6, x_7, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = l_RBNode_isBlack___rarg(x_5);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_RBNode_del___main___rarg(x_1, x_2, x_5);
x_21 = 0;
lean_ctor_set(x_3, 0, x_20);
lean_ctor_set_uint8(x_3, sizeof(void*)*4, x_21);
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_3);
x_22 = l_RBNode_del___main___rarg(x_1, x_2, x_5);
x_23 = l_RBNode_balLeft___rarg(x_22, x_6, x_7, x_8);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
x_27 = lean_ctor_get(x_3, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_25);
lean_inc(x_2);
x_28 = lean_apply_2(x_1, x_2, x_25);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_25);
x_30 = lean_apply_2(x_1, x_25, x_2);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_32 = l_RBNode_appendTrees___main___rarg(x_24, x_27);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = l_RBNode_isBlack___rarg(x_27);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = l_RBNode_del___main___rarg(x_1, x_2, x_27);
x_35 = 0;
x_36 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_26);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_RBNode_del___main___rarg(x_1, x_2, x_27);
x_38 = l_RBNode_balRight___rarg(x_24, x_25, x_26, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
x_39 = l_RBNode_isBlack___rarg(x_24);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_40 = l_RBNode_del___main___rarg(x_1, x_2, x_24);
x_41 = 0;
x_42 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_26);
lean_ctor_set(x_42, 3, x_27);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_RBNode_del___main___rarg(x_1, x_2, x_24);
x_44 = l_RBNode_balLeft___rarg(x_43, x_25, x_26, x_27);
return x_44;
}
}
}
}
}
}
lean_object* l_RBNode_del___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_del___main___rarg), 3, 0);
return x_3;
}
}
lean_object* l_RBNode_del___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_del___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_del___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_del___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_RBNode_del(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_del___rarg), 3, 0);
return x_3;
}
}
lean_object* l_RBNode_del___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_del(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_RBNode_del___main___rarg(x_1, x_2, x_3);
x_5 = l_RBNode_setBlack___rarg(x_4);
return x_5;
}
}
lean_object* l_RBNode_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_erase___rarg), 3, 0);
return x_3;
}
}
lean_object* l_RBNode_erase___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_erase(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_findCore___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_6);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_6);
x_11 = lean_apply_2(x_1, x_6, x_3);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_8;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_5;
goto _start;
}
}
}
}
lean_object* l_RBNode_findCore___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_findCore___main___rarg), 3, 0);
return x_3;
}
}
lean_object* l_RBNode_findCore___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_findCore___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_findCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_findCore___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_RBNode_findCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_findCore___rarg), 3, 0);
return x_3;
}
}
lean_object* l_RBNode_findCore___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_findCore(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_find___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 3);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_4);
x_10 = lean_apply_2(x_1, x_4, x_7);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_6);
lean_inc(x_1);
lean_inc(x_4);
x_12 = lean_apply_2(x_1, x_7, x_4);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_8);
return x_14;
}
else
{
lean_dec(x_8);
x_2 = lean_box(0);
x_3 = x_9;
goto _start;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_2 = lean_box(0);
x_3 = x_6;
goto _start;
}
}
}
}
lean_object* l_RBNode_find___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_find___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l_RBNode_find___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_find___main___rarg(x_1, lean_box(0), x_3, x_4);
return x_5;
}
}
lean_object* l_RBNode_find(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_RBNode_find___rarg), 4, 0);
return x_2;
}
}
lean_object* l_RBNode_lowerBound___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_3);
x_9 = lean_apply_2(x_1, x_3, x_6);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_6);
x_11 = lean_apply_2(x_1, x_6, x_3);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_7);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_2 = x_8;
x_4 = x_16;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_5;
goto _start;
}
}
}
}
lean_object* l_RBNode_lowerBound___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_lowerBound___main___rarg), 4, 0);
return x_3;
}
}
lean_object* l_RBNode_lowerBound___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_lowerBound___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_lowerBound___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_lowerBound___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_RBNode_lowerBound(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_lowerBound___rarg), 4, 0);
return x_3;
}
}
lean_object* l_RBNode_lowerBound___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_lowerBound(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_mkRBMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
lean_object* l_mkRBMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_mkRBMap(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBMap_empty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
lean_object* l_RBMap_empty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_empty(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBMap_HasEmptyc(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
lean_object* l_RBMap_HasEmptyc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_HasEmptyc(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBMap_depth___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_depth___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_RBMap_depth(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBMap_depth___rarg___boxed), 2, 0);
return x_4;
}
}
lean_object* l_RBMap_depth___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBMap_depth___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBMap_depth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_depth(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBMap_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_fold___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_RBMap_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_RBMap_fold___rarg), 3, 0);
return x_5;
}
}
lean_object* l_RBMap_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBMap_fold(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_RBMap_revFold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_revFold___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_RBMap_revFold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_RBMap_revFold___rarg), 3, 0);
return x_5;
}
}
lean_object* l_RBMap_revFold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBMap_revFold(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_RBMap_mfold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_mfold___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_RBMap_mfold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_RBMap_mfold___rarg), 4, 0);
return x_6;
}
}
lean_object* l_RBMap_mfold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_RBMap_mfold(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
lean_inc(x_2);
x_10 = lean_apply_2(x_2, x_3, x_4);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_13);
x_15 = lean_alloc_closure((void*)(l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__1), 4, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_5);
x_16 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
lean_object* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(x_1, x_2, x_3, x_8);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_9);
lean_closure_set(x_14, 3, x_10);
lean_closure_set(x_14, 4, x_11);
lean_closure_set(x_14, 5, x_12);
x_15 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
}
lean_object* l_RBNode_mfold___main___at_RBMap_mfor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg), 4, 0);
return x_5;
}
}
lean_object* l_RBMap_mfor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_RBMap_mfor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_RBMap_mfor___rarg), 3, 0);
return x_6;
}
}
lean_object* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_mfold___main___at_RBMap_mfor___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_RBMap_mfor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_RBMap_mfor(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
uint8_t l_RBMap_isEmpty___rarg(lean_object* x_1) {
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
lean_object* l_RBMap_isEmpty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBMap_isEmpty___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_RBMap_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_RBMap_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_RBMap_isEmpty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_isEmpty(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBMap_toList___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
lean_object* _init_l_RBMap_toList___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_RBMap_toList___rarg___lambda__1), 3, 0);
return x_1;
}
}
lean_object* l_RBMap_toList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_RBMap_toList___rarg___closed__1;
x_4 = l_RBNode_revFold___main___rarg(x_3, x_2, x_1);
return x_4;
}
}
lean_object* l_RBMap_toList(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBMap_toList___rarg), 1, 0);
return x_4;
}
}
lean_object* l_RBMap_toList___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_toList(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBMap_min___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBNode_min___main___rarg(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
lean_object* l_RBMap_min(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBMap_min___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_RBMap_min___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBMap_min___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_RBMap_min___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_min(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBMap_max___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBNode_max___main___rarg(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
lean_object* l_RBMap_max(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBMap_max___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_RBMap_max___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBMap_max___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_RBMap_max___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_max(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (x_3 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = l_String_splitAux___main___closed__1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_1, x_2, x_3, x_7);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_apply_1(x_1, x_9);
x_12 = l_Prod_HasRepr___rarg___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_List_reprAux___main___rarg___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_apply_1(x_2, x_10);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = l_Option_HasRepr___rarg___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_14, x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_20, x_8);
lean_dec(x_8);
return x_21;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_String_splitAux___main___closed__1;
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_25 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_26 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_1, x_2, x_25, x_24);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_apply_1(x_1, x_27);
x_30 = l_Prod_HasRepr___rarg___closed__1;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_List_reprAux___main___rarg___closed__1;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_apply_1(x_2, x_28);
x_35 = lean_string_append(x_33, x_34);
lean_dec(x_34);
x_36 = l_Option_HasRepr___rarg___closed__3;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_26);
lean_dec(x_26);
return x_38;
}
}
}
}
lean_object* l_List_reprAux___main___at_RBMap_HasRepr___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_List_repr___at_RBMap_HasRepr___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = l_List_repr___rarg___closed__1;
return x_4;
}
else
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = 1;
x_6 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_1, x_2, x_5, x_3);
x_7 = l_List_repr___rarg___closed__2;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_List_repr___rarg___closed__3;
x_10 = lean_string_append(x_8, x_9);
return x_10;
}
}
}
lean_object* l_List_repr___at_RBMap_HasRepr___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_repr___at_RBMap_HasRepr___spec__1___rarg), 3, 0);
return x_3;
}
}
lean_object* _init_l_RBMap_HasRepr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rbmapOf ");
return x_1;
}
}
lean_object* l_RBMap_HasRepr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_RBMap_toList___rarg(x_3);
x_5 = l_List_repr___at_RBMap_HasRepr___spec__1___rarg(x_1, x_2, x_4);
x_6 = l_RBMap_HasRepr___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_RBMap_HasRepr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBMap_HasRepr___rarg), 3, 0);
return x_4;
}
}
lean_object* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_RBMap_HasRepr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_HasRepr(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBMap_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_insert___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_RBMap_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBMap_insert___rarg), 4, 0);
return x_3;
}
}
lean_object* l_RBMap_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_erase___rarg(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_RBMap_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBMap_erase___rarg), 3, 0);
return x_3;
}
}
lean_object* l_RBMap_ofList___main___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
x_8 = l_RBMap_ofList___main___rarg(x_1, x_5);
x_9 = l_RBNode_insert___rarg(x_1, x_8, x_6, x_7);
return x_9;
}
}
}
lean_object* l_RBMap_ofList___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBMap_ofList___main___rarg), 2, 0);
return x_3;
}
}
lean_object* l_RBMap_ofList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBMap_ofList___main___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_RBMap_ofList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBMap_ofList___rarg), 2, 0);
return x_3;
}
}
lean_object* l_RBMap_findCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_findCore___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_RBMap_findCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBMap_findCore___rarg), 3, 0);
return x_3;
}
}
lean_object* l_RBMap_find___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_find___main___rarg(x_1, lean_box(0), x_2, x_3);
return x_4;
}
}
lean_object* l_RBMap_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBMap_find___rarg), 3, 0);
return x_3;
}
}
lean_object* l_RBMap_findD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBNode_find___main___rarg(x_1, lean_box(0), x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
}
lean_object* l_RBMap_findD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBMap_findD___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_RBMap_findD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_RBMap_findD___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_RBMap_lowerBound___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_RBNode_lowerBound___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_RBMap_lowerBound(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBMap_lowerBound___rarg), 3, 0);
return x_3;
}
}
uint8_t l_RBMap_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_find___main___rarg(x_1, lean_box(0), x_2, x_3);
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
lean_object* l_RBMap_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBMap_contains___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_RBMap_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_RBMap_contains___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_List_foldl___main___at_RBMap_fromList___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
x_8 = l_RBNode_insert___rarg(x_1, x_2, x_6, x_7);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
lean_object* l_List_foldl___main___at_RBMap_fromList___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldl___main___at_RBMap_fromList___spec__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_RBMap_fromList___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_foldl___main___at_RBMap_fromList___spec__1___rarg(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_RBMap_fromList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBMap_fromList___rarg), 2, 0);
return x_3;
}
}
uint8_t l_RBMap_all___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_RBNode_all___main___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_RBMap_all(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBMap_all___rarg___boxed), 2, 0);
return x_4;
}
}
lean_object* l_RBMap_all___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_RBMap_all___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_RBMap_all___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_all(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
uint8_t l_RBMap_any___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_RBNode_any___main___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_RBMap_any(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBMap_any___rarg___boxed), 2, 0);
return x_4;
}
}
lean_object* l_RBMap_any___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_RBMap_any___rarg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_RBMap_any___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_any(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_2, 3);
x_5 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_1, x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_RBNode_fold___main___at_RBMap_size___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_RBNode_fold___main___at_RBMap_size___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_RBMap_size___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_RBMap_size(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBMap_size___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBMap_size___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBMap_size___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_RBMap_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_size(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* _init_l_RBMap_maxDepth___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_max___boxed), 2, 0);
return x_1;
}
}
lean_object* l_RBMap_maxDepth___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_RBMap_maxDepth___rarg___closed__1;
x_3 = l_RBNode_depth___main___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_RBMap_maxDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_RBMap_maxDepth___rarg___boxed), 1, 0);
return x_4;
}
}
lean_object* l_RBMap_maxDepth___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RBMap_maxDepth___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_RBMap_maxDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBMap_maxDepth(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_List_foldl___main___at_rbmapOf___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
x_8 = l_RBNode_insert___rarg(x_1, x_2, x_6, x_7);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
lean_object* l_List_foldl___main___at_rbmapOf___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldl___main___at_rbmapOf___spec__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_rbmapOf___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_foldl___main___at_rbmapOf___spec__1___rarg(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_rbmapOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_rbmapOf___rarg), 2, 0);
return x_3;
}
}
lean_object* initialize_Init_Data_Repr(lean_object*);
lean_object* initialize_Init_Data_Option_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_RBMap_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Repr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_RBMap_toList___rarg___closed__1 = _init_l_RBMap_toList___rarg___closed__1();
lean_mark_persistent(l_RBMap_toList___rarg___closed__1);
l_RBMap_HasRepr___rarg___closed__1 = _init_l_RBMap_HasRepr___rarg___closed__1();
lean_mark_persistent(l_RBMap_HasRepr___rarg___closed__1);
l_RBMap_maxDepth___rarg___closed__1 = _init_l_RBMap_maxDepth___rarg___closed__1();
lean_mark_persistent(l_RBMap_maxDepth___rarg___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
