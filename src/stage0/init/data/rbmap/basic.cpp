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
obj* l_RBNode_del___main___rarg(obj*, obj*, obj*);
obj* l_RBNode_find(obj*);
obj* l_RBNode_depth___main___rarg___boxed(obj*, obj*);
obj* l_List_repr___main___at_RBMap_HasRepr___spec__1___boxed(obj*, obj*);
obj* l_RBNode_appendTrees___main___boxed(obj*, obj*);
obj* l_RBNode_ins___main___boxed(obj*, obj*);
obj* l_RBMap_fold___main___rarg(obj*, obj*, obj*);
obj* l_RBMap_contains(obj*, obj*);
obj* l_RBNode_findCore(obj*, obj*);
obj* l_RBNode_balRight___boxed(obj*, obj*);
obj* l_RBMap_revFold___rarg(obj*, obj*, obj*);
obj* l_RBNode_lowerBound(obj*, obj*);
obj* l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___rarg(obj*, obj*);
obj* l_RBNode_revFold___rarg(obj*, obj*, obj*);
obj* l_RBNode_findCore___main___rarg(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_appendTrees___rarg(obj*, obj*);
obj* l_RBNode_findCore___main___boxed(obj*, obj*);
obj* l_RBMap_find___rarg(obj*, obj*, obj*);
obj* l_RBNode_insert___boxed(obj*, obj*);
obj* l_RBMap_any___main(obj*, obj*, obj*);
obj* l_RBMap_contains___boxed(obj*, obj*);
obj* l_RBMap_any___main___rarg___boxed(obj*, obj*);
obj* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBNode_setBlack(obj*, obj*);
obj* l_List_foldl___main___at_rbmapOf___spec__1(obj*, obj*);
obj* l_RBNode_isRed___boxed(obj*, obj*);
obj* l_RBNode_balRight___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main(obj*, obj*);
obj* l_RBNode_balance2___main___boxed(obj*, obj*);
obj* l_RBMap_ofList(obj*, obj*);
obj* l_RBMap_insert___boxed(obj*, obj*);
obj* l_RBNode_balance_u_2083___main(obj*, obj*);
obj* l_RBNode_find___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_toList___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_isBlack___main___boxed(obj*, obj*);
obj* l_RBMap_min(obj*, obj*, obj*);
obj* l_RBMap_toList___rarg(obj*);
obj* l_RBNode_appendTrees___boxed(obj*, obj*);
obj* l_RBMap_depth___rarg___boxed(obj*, obj*);
obj* l_RBNode_isRed___rarg___boxed(obj*);
uint8 l_RBNode_all___rarg(obj*, obj*);
obj* l_RBNode_balance2(obj*, obj*);
obj* l_RBMap_findCore___rarg(obj*, obj*, obj*);
obj* l_RBNode_lowerBound___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_all___main(obj*, obj*, obj*);
obj* l_RBMap_min___main___rarg(obj*);
obj* l_RBMap_erase___main___rarg(obj*, obj*, obj*);
obj* l_RBMap_min___rarg(obj*);
obj* l_RBNode_del___main___boxed(obj*, obj*);
obj* l_RBMap_erase___boxed(obj*, obj*);
uint8 l_RBNode_any___main___rarg(obj*, obj*);
obj* l_RBMap_findCore(obj*, obj*);
obj* l_RBNode_isRed___main___rarg___boxed(obj*);
obj* l_RBNode_lowerBound___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmapOf___rarg(obj*, obj*);
obj* l_RBNode_any___main(obj*, obj*);
obj* l_RBNode_mfold___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_revFold___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_erase___rarg(obj*, obj*, obj*);
obj* l_RBMap_findCore___main___boxed(obj*, obj*);
obj* l_List_foldl___main___at_rbmapOf___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbmapOf(obj*, obj*);
obj* l_RBMap_erase___rarg(obj*, obj*, obj*);
obj* l_RBNode_insert___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_toList___boxed(obj*, obj*, obj*);
obj* l_RBNode_min___main___rarg(obj*);
obj* l_RBMap_mfold(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___boxed(obj*, obj*);
obj* l_RBMap_size(obj*, obj*, obj*);
obj* l_RBMap_mfor(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_lowerBound___main(obj*, obj*);
obj* l_RBNode_max___main___rarg(obj*);
obj* l_RBNode_isBlack___boxed(obj*, obj*);
obj* l_RBMap_lowerBound___main(obj*, obj*);
obj* l_RBMap_mfold___main(obj*, obj*, obj*, obj*, obj*);
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
obj* l_RBMap_toList___main(obj*, obj*, obj*);
uint8 l_RBMap_any___main___rarg(obj*, obj*);
obj* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(obj*, obj*);
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
obj* l_RBNode_del___main(obj*, obj*);
obj* l_RBMap_isEmpty(obj*, obj*, obj*);
obj* l_RBNode_setBlack___boxed(obj*, obj*);
obj* l_RBNode_setRed___main___boxed(obj*, obj*);
obj* l_RBNode_balance2___main___rarg(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_RBMap_fromList___spec__1___boxed(obj*, obj*);
obj* l_RBMap_mfor___rarg(obj*, obj*, obj*);
obj* l_mkRBMap___boxed(obj*, obj*, obj*);
obj* l_RBMap_isEmpty___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_appendTrees(obj*, obj*);
obj* l_RBMap_toList___main___rarg(obj*);
obj* l_RBNode_balRight(obj*, obj*);
obj* l_RBMap_ofList___main___rarg(obj*, obj*);
obj* l_RBNode_balance2___main(obj*, obj*);
obj* l_RBNode_all___main___rarg___boxed(obj*, obj*);
obj* l_RBMap_revFold___main___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBMap_mfor___spec__1___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_List_repr___main___rarg___closed__3;
obj* l_RBNode_balance_u_2083___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_singleton(obj*, obj*);
obj* l_RBMap_ofList___rarg(obj*, obj*);
obj* l_RBNode_find___main___boxed(obj*);
obj* l_RBNode_balance_u_2083___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_fold___main___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_findCore___boxed(obj*, obj*);
obj* l_RBNode_balance2___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_lowerBound___boxed(obj*, obj*);
obj* l_RBNode_find___boxed(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_RBNode_balLeft___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_revFold___main___rarg(obj*, obj*, obj*);
obj* l_RBMap_contains___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_fold___rarg(obj*, obj*, obj*);
obj* l_RBNode_appendTrees___main(obj*, obj*);
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
obj* l_RBNode_del___rarg(obj*, obj*, obj*);
obj* l_RBMap_insert___main___boxed(obj*, obj*);
obj* l_RBNode_singleton___rarg(obj*, obj*);
obj* l_RBNode_revFold___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_appendTrees___main___rarg(obj*, obj*);
obj* l_RBNode_max___boxed(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_RBNode_del___boxed(obj*, obj*);
obj* l_RBMap_HasEmptyc___boxed(obj*, obj*, obj*);
obj* l_RBNode_isRed___main___boxed(obj*, obj*);
obj* l_RBMap_HasRepr___rarg(obj*, obj*, obj*);
obj* l_RBNode_balLeft___main___boxed(obj*, obj*);
obj* l_RBNode_setBlack___main___boxed(obj*, obj*);
extern obj* l_Prod_HasRepr___rarg___closed__1;
obj* l_RBNode_balLeft(obj*, obj*);
obj* l_RBMap_find(obj*, obj*);
obj* l_RBMap_max___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_fold___main___rarg(obj*, obj*, obj*);
obj* l_RBNode_isRed___main(obj*, obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_RBMap_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins(obj*, obj*);
obj* l_RBNode_erase___boxed(obj*, obj*);
obj* l_RBMap_erase___main___boxed(obj*, obj*);
obj* l_RBMap_depth___rarg(obj*, obj*);
uint8 l_RBNode_all___main___rarg(obj*, obj*);
uint8 l_RBNode_any___rarg(obj*, obj*);
obj* l_RBMap_toList(obj*, obj*, obj*);
obj* l_RBMap_mfold___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_revFold___main___at_RBMap_toList___main___spec__1___boxed(obj*, obj*);
obj* l_RBNode_all(obj*, obj*);
obj* l_RBNode_mfold___main(obj*, obj*, obj*, obj*);
obj* l_RBNode_balLeft___main(obj*, obj*);
obj* l_RBMap_findCore___main(obj*, obj*);
uint8 l_RBNode_isBlack___rarg(obj*);
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
uint8 l_RBNode_isBlack___main___rarg(obj*);
obj* l_RBNode_all___rarg___boxed(obj*, obj*);
obj* l_rbmapOf___boxed(obj*, obj*);
obj* l_RBNode_depth___main(obj*, obj*);
obj* l_RBNode_mfold___main___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_isEmpty___main(obj*, obj*, obj*);
obj* l_RBNode_balLeft___boxed(obj*, obj*);
obj* l_RBNode_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main(obj*, obj*);
obj* l_RBMap_lowerBound___main___boxed(obj*, obj*);
obj* l_RBNode_min(obj*, obj*);
obj* l_RBNode_min___main(obj*, obj*);
obj* l_RBMap_mfold___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_any___main___boxed(obj*, obj*);
obj* l_RBNode_isBlack___main___rarg___boxed(obj*);
obj* l_RBMap_fold(obj*, obj*, obj*, obj*);
obj* l_List_reprAux___main___at_RBMap_HasRepr___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_singleton___boxed(obj*, obj*);
obj* l_RBNode_balance1___main(obj*, obj*);
obj* l_RBNode_any___boxed(obj*, obj*);
obj* l_RBMap_erase___main(obj*, obj*);
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
obj* l_RBNode_erase(obj*, obj*);
obj* l_RBMap_lowerBound___main___rarg(obj*, obj*, obj*);
obj* l_RBMap_isEmpty___boxed(obj*, obj*, obj*);
uint8 l_RBMap_all___main___rarg(obj*, obj*);
obj* l_RBNode_balance1___boxed(obj*, obj*);
obj* l_RBNode_depth___main___boxed(obj*, obj*);
obj* l_RBNode_isBlack(obj*, obj*);
obj* l_RBMap_revFold___main(obj*, obj*, obj*, obj*);
obj* l_RBMap_size___rarg___boxed(obj*);
obj* l_RBMap_all___main___rarg___boxed(obj*, obj*);
obj* l_RBNode_find___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_balance_u_2083___main___boxed(obj*, obj*);
obj* l_RBNode_fold___main___at_RBMap_size___spec__1___boxed(obj*, obj*);
obj* l_RBMap_fromList(obj*, obj*);
obj* l_RBNode_any___rarg___boxed(obj*, obj*);
obj* l_RBNode_max___main(obj*, obj*);
obj* l_RBNode_setBlack___rarg(obj*);
obj* l_RBMap_lowerBound___rarg(obj*, obj*, obj*);
obj* l_RBMap_HasEmptyc(obj*, obj*, obj*);
obj* l_RBNode_balLeft___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_min___main___boxed(obj*, obj*);
obj* l_RBNode_balance_u_2083___boxed(obj*, obj*);
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
obj* l_RBNode_setRed___rarg(obj*);
obj* l_RBNode_fold___boxed(obj*, obj*, obj*);
obj* l_RBMap_size___rarg(obj*);
obj* l_RBNode_fold___main(obj*, obj*, obj*);
obj* l_List_foldl___main___at_rbmapOf___spec__1___boxed(obj*, obj*);
obj* l_RBNode_fold(obj*, obj*, obj*);
obj* l_RBNode_depth(obj*, obj*);
obj* l_RBMap_min___main___boxed(obj*, obj*, obj*);
obj* l_RBNode_all___main___boxed(obj*, obj*);
obj* l_RBNode_mfold(obj*, obj*, obj*, obj*);
obj* l_RBMap_isEmpty___main___rarg___boxed(obj*);
obj* l_RBNode_balance1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_del(obj*, obj*);
obj* l_RBMap_find___main(obj*, obj*);
extern obj* l_List_repr___main___rarg___closed__2;
obj* l_RBNode_setRed___boxed(obj*, obj*);
obj* l_RBNode_find___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main___rarg(obj*, obj*, obj*, obj*);
uint8 l_RBMap_any___rarg(obj*, obj*);
obj* l_RBMap_size___boxed(obj*, obj*, obj*);
obj* l_RBMap_any(obj*, obj*, obj*);
obj* l_RBNode_setRed(obj*, obj*);
obj* l_RBNode_balance_u_2083(obj*, obj*);
obj* l_RBMap_HasRepr___boxed(obj*, obj*, obj*);
obj* l_RBNode_findCore___rarg(obj*, obj*, obj*);
obj* l_RBNode_isBlack___main(obj*, obj*);
obj* l_RBMap_max___rarg(obj*);
obj* l_RBMap_max___main___rarg(obj*);
uint8 l_RBMap_isEmpty___rarg(obj*);
obj* l_List_foldl___main___at_RBMap_fromList___spec__1(obj*, obj*);
obj* l_List_repr___main___at_RBMap_HasRepr___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_RBNode_revFold(obj*, obj*, obj*);
obj* l_RBNode_setRed___main(obj*, obj*);
obj* l_RBNode_setRed___main___rarg(obj*);
uint8 l_RBMap_contains___rarg(obj*, obj*, obj*);
obj* l_RBNode_revFold___boxed(obj*, obj*, obj*);
obj* l_RBMap_mfold___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_RBMap_max___boxed(obj*, obj*, obj*);
obj* l_RBMap_erase(obj*, obj*);
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
uint8 l_RBNode_isBlack___main___rarg(obj* x_0) {
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
x_3 = 0;
return x_3;
}
else
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
}
obj* l_RBNode_isBlack___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_isBlack___main___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_RBNode_isBlack___main___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_RBNode_isBlack___main___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBNode_isBlack___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_isBlack___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_RBNode_isBlack___rarg(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_RBNode_isBlack___main___rarg(x_0);
return x_1;
}
}
obj* l_RBNode_isBlack(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_isBlack___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_RBNode_isBlack___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_RBNode_isBlack___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBNode_isBlack___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_isBlack(x_0, x_1);
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
obj* l_RBNode_balance_u_2083___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 1;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 2, x_2);
lean::cnstr_set(x_5, 3, x_3);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; 
x_10 = lean::cnstr_get(x_3, 3);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; 
x_12 = lean::cnstr_get(x_3, 1);
x_14 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_16 = x_3;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_3);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_12);
lean::cnstr_set(x_17, 2, x_14);
lean::cnstr_set(x_17, 3, x_10);
lean::cnstr_set_scalar(x_17, sizeof(void*)*4, x_7);
x_18 = x_17;
x_19 = 1;
x_20 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_20, 0, x_10);
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
x_22 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*4);
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
x_28 = lean::cnstr_get(x_10, 0);
x_30 = lean::cnstr_get(x_10, 1);
x_32 = lean::cnstr_get(x_10, 2);
x_34 = lean::cnstr_get(x_10, 3);
if (lean::is_exclusive(x_10)) {
 x_36 = x_10;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_10);
 x_36 = lean::box(0);
}
x_37 = 1;
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_8);
lean::cnstr_set(x_38, 1, x_1);
lean::cnstr_set(x_38, 2, x_2);
lean::cnstr_set(x_38, 3, x_8);
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
obj* x_44; obj* x_45; obj* x_46; 
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 lean::cnstr_release(x_10, 2);
 lean::cnstr_release(x_10, 3);
 x_44 = x_10;
} else {
 lean::dec(x_10);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_8);
lean::cnstr_set(x_45, 1, x_1);
lean::cnstr_set(x_45, 2, x_2);
lean::cnstr_set(x_45, 3, x_3);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_22);
x_46 = x_45;
return x_46;
}
}
}
else
{
uint8 x_47; 
x_47 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*4);
if (x_47 == 0)
{
obj* x_48; 
x_48 = lean::cnstr_get(x_3, 3);
lean::inc(x_48);
if (lean::obj_tag(x_48) == 0)
{
obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_61; obj* x_63; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_50 = lean::cnstr_get(x_3, 1);
x_52 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_54 = x_3;
} else {
 lean::inc(x_50);
 lean::inc(x_52);
 lean::dec(x_3);
 x_54 = lean::box(0);
}
x_55 = lean::cnstr_get(x_8, 0);
x_57 = lean::cnstr_get(x_8, 1);
x_59 = lean::cnstr_get(x_8, 2);
x_61 = lean::cnstr_get(x_8, 3);
if (lean::is_exclusive(x_8)) {
 x_63 = x_8;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::inc(x_59);
 lean::inc(x_61);
 lean::dec(x_8);
 x_63 = lean::box(0);
}
x_64 = 1;
if (lean::is_scalar(x_63)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_63;
}
lean::cnstr_set(x_65, 0, x_48);
lean::cnstr_set(x_65, 1, x_1);
lean::cnstr_set(x_65, 2, x_2);
lean::cnstr_set(x_65, 3, x_55);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_64);
x_66 = x_65;
if (lean::is_scalar(x_54)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_54;
}
lean::cnstr_set(x_67, 0, x_61);
lean::cnstr_set(x_67, 1, x_50);
lean::cnstr_set(x_67, 2, x_52);
lean::cnstr_set(x_67, 3, x_48);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_64);
x_68 = x_67;
x_69 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_69, 0, x_66);
lean::cnstr_set(x_69, 1, x_57);
lean::cnstr_set(x_69, 2, x_59);
lean::cnstr_set(x_69, 3, x_68);
lean::cnstr_set_scalar(x_69, sizeof(void*)*4, x_47);
x_70 = x_69;
return x_70;
}
else
{
uint8 x_71; 
x_71 = lean::cnstr_get_scalar<uint8>(x_48, sizeof(void*)*4);
if (x_71 == 0)
{
obj* x_72; obj* x_74; obj* x_76; obj* x_77; obj* x_79; obj* x_81; obj* x_83; obj* x_85; obj* x_86; obj* x_88; obj* x_90; obj* x_92; obj* x_94; obj* x_95; obj* x_96; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
x_72 = lean::cnstr_get(x_3, 1);
x_74 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_76 = x_3;
} else {
 lean::inc(x_72);
 lean::inc(x_74);
 lean::dec(x_3);
 x_76 = lean::box(0);
}
x_77 = lean::cnstr_get(x_8, 0);
x_79 = lean::cnstr_get(x_8, 1);
x_81 = lean::cnstr_get(x_8, 2);
x_83 = lean::cnstr_get(x_8, 3);
if (lean::is_exclusive(x_8)) {
 x_85 = x_8;
} else {
 lean::inc(x_77);
 lean::inc(x_79);
 lean::inc(x_81);
 lean::inc(x_83);
 lean::dec(x_8);
 x_85 = lean::box(0);
}
x_86 = lean::cnstr_get(x_48, 0);
x_88 = lean::cnstr_get(x_48, 1);
x_90 = lean::cnstr_get(x_48, 2);
x_92 = lean::cnstr_get(x_48, 3);
if (lean::is_exclusive(x_48)) {
 x_94 = x_48;
} else {
 lean::inc(x_86);
 lean::inc(x_88);
 lean::inc(x_90);
 lean::inc(x_92);
 lean::dec(x_48);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_77);
lean::cnstr_set(x_95, 1, x_79);
lean::cnstr_set(x_95, 2, x_81);
lean::cnstr_set(x_95, 3, x_83);
lean::cnstr_set_scalar(x_95, sizeof(void*)*4, x_71);
x_96 = x_95;
x_97 = 1;
if (lean::is_scalar(x_85)) {
 x_98 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_98 = x_85;
}
lean::cnstr_set(x_98, 0, x_0);
lean::cnstr_set(x_98, 1, x_1);
lean::cnstr_set(x_98, 2, x_2);
lean::cnstr_set(x_98, 3, x_96);
lean::cnstr_set_scalar(x_98, sizeof(void*)*4, x_97);
x_99 = x_98;
if (lean::is_scalar(x_76)) {
 x_100 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_100 = x_76;
}
lean::cnstr_set(x_100, 0, x_86);
lean::cnstr_set(x_100, 1, x_88);
lean::cnstr_set(x_100, 2, x_90);
lean::cnstr_set(x_100, 3, x_92);
lean::cnstr_set_scalar(x_100, sizeof(void*)*4, x_97);
x_101 = x_100;
x_102 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_102, 0, x_99);
lean::cnstr_set(x_102, 1, x_72);
lean::cnstr_set(x_102, 2, x_74);
lean::cnstr_set(x_102, 3, x_101);
lean::cnstr_set_scalar(x_102, sizeof(void*)*4, x_71);
x_103 = x_102;
return x_103;
}
else
{
obj* x_104; obj* x_106; obj* x_108; obj* x_109; obj* x_111; obj* x_113; obj* x_115; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; 
x_104 = lean::cnstr_get(x_3, 1);
x_106 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_108 = x_3;
} else {
 lean::inc(x_104);
 lean::inc(x_106);
 lean::dec(x_3);
 x_108 = lean::box(0);
}
x_109 = lean::cnstr_get(x_8, 0);
x_111 = lean::cnstr_get(x_8, 1);
x_113 = lean::cnstr_get(x_8, 2);
x_115 = lean::cnstr_get(x_8, 3);
if (lean::is_exclusive(x_8)) {
 x_117 = x_8;
} else {
 lean::inc(x_109);
 lean::inc(x_111);
 lean::inc(x_113);
 lean::inc(x_115);
 lean::dec(x_8);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_0);
lean::cnstr_set(x_118, 1, x_1);
lean::cnstr_set(x_118, 2, x_2);
lean::cnstr_set(x_118, 3, x_109);
lean::cnstr_set_scalar(x_118, sizeof(void*)*4, x_71);
x_119 = x_118;
if (lean::is_scalar(x_108)) {
 x_120 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_120 = x_108;
}
lean::cnstr_set(x_120, 0, x_115);
lean::cnstr_set(x_120, 1, x_104);
lean::cnstr_set(x_120, 2, x_106);
lean::cnstr_set(x_120, 3, x_48);
lean::cnstr_set_scalar(x_120, sizeof(void*)*4, x_71);
x_121 = x_120;
x_122 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_122, 0, x_119);
lean::cnstr_set(x_122, 1, x_111);
lean::cnstr_set(x_122, 2, x_113);
lean::cnstr_set(x_122, 3, x_121);
lean::cnstr_set_scalar(x_122, sizeof(void*)*4, x_47);
x_123 = x_122;
return x_123;
}
}
}
else
{
obj* x_124; 
x_124 = lean::cnstr_get(x_3, 3);
lean::inc(x_124);
if (lean::obj_tag(x_124) == 0)
{
obj* x_126; obj* x_127; obj* x_128; 
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 lean::cnstr_release(x_8, 3);
 x_126 = x_8;
} else {
 lean::dec(x_8);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_124);
lean::cnstr_set(x_127, 1, x_1);
lean::cnstr_set(x_127, 2, x_2);
lean::cnstr_set(x_127, 3, x_3);
lean::cnstr_set_scalar(x_127, sizeof(void*)*4, x_47);
x_128 = x_127;
return x_128;
}
else
{
uint8 x_129; 
x_129 = lean::cnstr_get_scalar<uint8>(x_124, sizeof(void*)*4);
if (x_129 == 0)
{
obj* x_130; obj* x_132; obj* x_134; obj* x_135; obj* x_137; obj* x_139; obj* x_141; obj* x_143; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
x_130 = lean::cnstr_get(x_3, 1);
x_132 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_134 = x_3;
} else {
 lean::inc(x_130);
 lean::inc(x_132);
 lean::dec(x_3);
 x_134 = lean::box(0);
}
x_135 = lean::cnstr_get(x_124, 0);
x_137 = lean::cnstr_get(x_124, 1);
x_139 = lean::cnstr_get(x_124, 2);
x_141 = lean::cnstr_get(x_124, 3);
if (lean::is_exclusive(x_124)) {
 x_143 = x_124;
} else {
 lean::inc(x_135);
 lean::inc(x_137);
 lean::inc(x_139);
 lean::inc(x_141);
 lean::dec(x_124);
 x_143 = lean::box(0);
}
lean::inc(x_8);
if (lean::is_scalar(x_143)) {
 x_145 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_145 = x_143;
}
lean::cnstr_set(x_145, 0, x_0);
lean::cnstr_set(x_145, 1, x_1);
lean::cnstr_set(x_145, 2, x_2);
lean::cnstr_set(x_145, 3, x_8);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 lean::cnstr_release(x_8, 3);
 x_146 = x_8;
} else {
 lean::dec(x_8);
 x_146 = lean::box(0);
}
lean::cnstr_set_scalar(x_145, sizeof(void*)*4, x_47);
x_147 = x_145;
if (lean::is_scalar(x_146)) {
 x_148 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_148 = x_146;
}
lean::cnstr_set(x_148, 0, x_135);
lean::cnstr_set(x_148, 1, x_137);
lean::cnstr_set(x_148, 2, x_139);
lean::cnstr_set(x_148, 3, x_141);
lean::cnstr_set_scalar(x_148, sizeof(void*)*4, x_47);
x_149 = x_148;
if (lean::is_scalar(x_134)) {
 x_150 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_150 = x_134;
}
lean::cnstr_set(x_150, 0, x_147);
lean::cnstr_set(x_150, 1, x_130);
lean::cnstr_set(x_150, 2, x_132);
lean::cnstr_set(x_150, 3, x_149);
lean::cnstr_set_scalar(x_150, sizeof(void*)*4, x_129);
x_151 = x_150;
return x_151;
}
else
{
obj* x_152; obj* x_154; obj* x_156; obj* x_157; obj* x_159; obj* x_161; obj* x_163; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
x_152 = lean::cnstr_get(x_3, 1);
x_154 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_156 = x_3;
} else {
 lean::inc(x_152);
 lean::inc(x_154);
 lean::dec(x_3);
 x_156 = lean::box(0);
}
x_157 = lean::cnstr_get(x_8, 0);
x_159 = lean::cnstr_get(x_8, 1);
x_161 = lean::cnstr_get(x_8, 2);
x_163 = lean::cnstr_get(x_8, 3);
if (lean::is_exclusive(x_8)) {
 x_165 = x_8;
} else {
 lean::inc(x_157);
 lean::inc(x_159);
 lean::inc(x_161);
 lean::inc(x_163);
 lean::dec(x_8);
 x_165 = lean::box(0);
}
if (lean::is_scalar(x_165)) {
 x_166 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_166 = x_165;
}
lean::cnstr_set(x_166, 0, x_157);
lean::cnstr_set(x_166, 1, x_159);
lean::cnstr_set(x_166, 2, x_161);
lean::cnstr_set(x_166, 3, x_163);
lean::cnstr_set_scalar(x_166, sizeof(void*)*4, x_129);
x_167 = x_166;
if (lean::is_scalar(x_156)) {
 x_168 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_168 = x_156;
}
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_152);
lean::cnstr_set(x_168, 2, x_154);
lean::cnstr_set(x_168, 3, x_124);
lean::cnstr_set_scalar(x_168, sizeof(void*)*4, x_7);
x_169 = x_168;
x_170 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_170, 0, x_0);
lean::cnstr_set(x_170, 1, x_1);
lean::cnstr_set(x_170, 2, x_2);
lean::cnstr_set(x_170, 3, x_169);
lean::cnstr_set_scalar(x_170, sizeof(void*)*4, x_129);
x_171 = x_170;
return x_171;
}
}
}
}
}
else
{
obj* x_172; obj* x_173; 
x_172 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_172, 0, x_0);
lean::cnstr_set(x_172, 1, x_1);
lean::cnstr_set(x_172, 2, x_2);
lean::cnstr_set(x_172, 3, x_3);
lean::cnstr_set_scalar(x_172, sizeof(void*)*4, x_7);
x_173 = x_172;
return x_173;
}
}
}
else
{
uint8 x_174; 
x_174 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_174 == 0)
{
obj* x_175; 
x_175 = lean::cnstr_get(x_0, 0);
lean::inc(x_175);
if (lean::obj_tag(x_175) == 0)
{
obj* x_177; 
x_177 = lean::cnstr_get(x_0, 3);
lean::inc(x_177);
if (lean::obj_tag(x_177) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_179; obj* x_181; obj* x_183; obj* x_184; obj* x_185; uint8 x_186; obj* x_187; obj* x_188; 
x_179 = lean::cnstr_get(x_0, 1);
x_181 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_183 = x_0;
} else {
 lean::inc(x_179);
 lean::inc(x_181);
 lean::dec(x_0);
 x_183 = lean::box(0);
}
if (lean::is_scalar(x_183)) {
 x_184 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_184 = x_183;
}
lean::cnstr_set(x_184, 0, x_3);
lean::cnstr_set(x_184, 1, x_179);
lean::cnstr_set(x_184, 2, x_181);
lean::cnstr_set(x_184, 3, x_3);
lean::cnstr_set_scalar(x_184, sizeof(void*)*4, x_174);
x_185 = x_184;
x_186 = 1;
x_187 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_187, 0, x_185);
lean::cnstr_set(x_187, 1, x_1);
lean::cnstr_set(x_187, 2, x_2);
lean::cnstr_set(x_187, 3, x_3);
lean::cnstr_set_scalar(x_187, sizeof(void*)*4, x_186);
x_188 = x_187;
return x_188;
}
else
{
uint8 x_189; 
x_189 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*4);
if (x_189 == 0)
{
obj* x_190; 
x_190 = lean::cnstr_get(x_3, 0);
lean::inc(x_190);
if (lean::obj_tag(x_190) == 0)
{
obj* x_192; 
x_192 = lean::cnstr_get(x_3, 3);
lean::inc(x_192);
if (lean::obj_tag(x_192) == 0)
{
obj* x_194; obj* x_196; obj* x_198; obj* x_199; obj* x_201; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; uint8 x_208; obj* x_209; obj* x_210; 
x_194 = lean::cnstr_get(x_0, 1);
x_196 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_198 = x_0;
} else {
 lean::inc(x_194);
 lean::inc(x_196);
 lean::dec(x_0);
 x_198 = lean::box(0);
}
x_199 = lean::cnstr_get(x_3, 1);
x_201 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_203 = x_3;
} else {
 lean::inc(x_199);
 lean::inc(x_201);
 lean::dec(x_3);
 x_203 = lean::box(0);
}
if (lean::is_scalar(x_203)) {
 x_204 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_204 = x_203;
}
lean::cnstr_set(x_204, 0, x_192);
lean::cnstr_set(x_204, 1, x_194);
lean::cnstr_set(x_204, 2, x_196);
lean::cnstr_set(x_204, 3, x_192);
lean::cnstr_set_scalar(x_204, sizeof(void*)*4, x_189);
x_205 = x_204;
if (lean::is_scalar(x_198)) {
 x_206 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_206 = x_198;
}
lean::cnstr_set(x_206, 0, x_192);
lean::cnstr_set(x_206, 1, x_199);
lean::cnstr_set(x_206, 2, x_201);
lean::cnstr_set(x_206, 3, x_192);
lean::cnstr_set_scalar(x_206, sizeof(void*)*4, x_189);
x_207 = x_206;
x_208 = 1;
x_209 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_209, 0, x_205);
lean::cnstr_set(x_209, 1, x_1);
lean::cnstr_set(x_209, 2, x_2);
lean::cnstr_set(x_209, 3, x_207);
lean::cnstr_set_scalar(x_209, sizeof(void*)*4, x_208);
x_210 = x_209;
return x_210;
}
else
{
uint8 x_211; 
x_211 = lean::cnstr_get_scalar<uint8>(x_192, sizeof(void*)*4);
if (x_211 == 0)
{
obj* x_212; obj* x_214; obj* x_216; obj* x_217; obj* x_219; obj* x_221; obj* x_222; obj* x_224; obj* x_226; obj* x_228; obj* x_230; obj* x_231; obj* x_232; uint8 x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
x_212 = lean::cnstr_get(x_0, 1);
x_214 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_216 = x_0;
} else {
 lean::inc(x_212);
 lean::inc(x_214);
 lean::dec(x_0);
 x_216 = lean::box(0);
}
x_217 = lean::cnstr_get(x_3, 1);
x_219 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_221 = x_3;
} else {
 lean::inc(x_217);
 lean::inc(x_219);
 lean::dec(x_3);
 x_221 = lean::box(0);
}
x_222 = lean::cnstr_get(x_192, 0);
x_224 = lean::cnstr_get(x_192, 1);
x_226 = lean::cnstr_get(x_192, 2);
x_228 = lean::cnstr_get(x_192, 3);
if (lean::is_exclusive(x_192)) {
 x_230 = x_192;
} else {
 lean::inc(x_222);
 lean::inc(x_224);
 lean::inc(x_226);
 lean::inc(x_228);
 lean::dec(x_192);
 x_230 = lean::box(0);
}
if (lean::is_scalar(x_230)) {
 x_231 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_231 = x_230;
}
lean::cnstr_set(x_231, 0, x_190);
lean::cnstr_set(x_231, 1, x_212);
lean::cnstr_set(x_231, 2, x_214);
lean::cnstr_set(x_231, 3, x_190);
lean::cnstr_set_scalar(x_231, sizeof(void*)*4, x_211);
x_232 = x_231;
x_233 = 1;
if (lean::is_scalar(x_221)) {
 x_234 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_234 = x_221;
}
lean::cnstr_set(x_234, 0, x_232);
lean::cnstr_set(x_234, 1, x_1);
lean::cnstr_set(x_234, 2, x_2);
lean::cnstr_set(x_234, 3, x_190);
lean::cnstr_set_scalar(x_234, sizeof(void*)*4, x_233);
x_235 = x_234;
if (lean::is_scalar(x_216)) {
 x_236 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_236 = x_216;
}
lean::cnstr_set(x_236, 0, x_222);
lean::cnstr_set(x_236, 1, x_224);
lean::cnstr_set(x_236, 2, x_226);
lean::cnstr_set(x_236, 3, x_228);
lean::cnstr_set_scalar(x_236, sizeof(void*)*4, x_233);
x_237 = x_236;
x_238 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_238, 0, x_235);
lean::cnstr_set(x_238, 1, x_217);
lean::cnstr_set(x_238, 2, x_219);
lean::cnstr_set(x_238, 3, x_237);
lean::cnstr_set_scalar(x_238, sizeof(void*)*4, x_211);
x_239 = x_238;
return x_239;
}
else
{
obj* x_240; obj* x_241; obj* x_243; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; 
if (lean::is_exclusive(x_192)) {
 lean::cnstr_release(x_192, 0);
 lean::cnstr_release(x_192, 1);
 lean::cnstr_release(x_192, 2);
 lean::cnstr_release(x_192, 3);
 x_240 = x_192;
} else {
 lean::dec(x_192);
 x_240 = lean::box(0);
}
x_241 = lean::cnstr_get(x_0, 1);
x_243 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_245 = x_0;
} else {
 lean::inc(x_241);
 lean::inc(x_243);
 lean::dec(x_0);
 x_245 = lean::box(0);
}
if (lean::is_scalar(x_240)) {
 x_246 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_246 = x_240;
}
lean::cnstr_set(x_246, 0, x_190);
lean::cnstr_set(x_246, 1, x_241);
lean::cnstr_set(x_246, 2, x_243);
lean::cnstr_set(x_246, 3, x_190);
lean::cnstr_set_scalar(x_246, sizeof(void*)*4, x_189);
x_247 = x_246;
if (lean::is_scalar(x_245)) {
 x_248 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_248 = x_245;
}
lean::cnstr_set(x_248, 0, x_247);
lean::cnstr_set(x_248, 1, x_1);
lean::cnstr_set(x_248, 2, x_2);
lean::cnstr_set(x_248, 3, x_3);
lean::cnstr_set_scalar(x_248, sizeof(void*)*4, x_211);
x_249 = x_248;
return x_249;
}
}
}
else
{
uint8 x_250; 
x_250 = lean::cnstr_get_scalar<uint8>(x_190, sizeof(void*)*4);
if (x_250 == 0)
{
obj* x_251; 
x_251 = lean::cnstr_get(x_3, 3);
lean::inc(x_251);
if (lean::obj_tag(x_251) == 0)
{
obj* x_253; obj* x_255; obj* x_257; obj* x_258; obj* x_260; obj* x_262; obj* x_263; obj* x_265; obj* x_267; obj* x_269; obj* x_271; obj* x_272; obj* x_273; uint8 x_274; obj* x_275; obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; 
x_253 = lean::cnstr_get(x_0, 1);
x_255 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_257 = x_0;
} else {
 lean::inc(x_253);
 lean::inc(x_255);
 lean::dec(x_0);
 x_257 = lean::box(0);
}
x_258 = lean::cnstr_get(x_3, 1);
x_260 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_262 = x_3;
} else {
 lean::inc(x_258);
 lean::inc(x_260);
 lean::dec(x_3);
 x_262 = lean::box(0);
}
x_263 = lean::cnstr_get(x_190, 0);
x_265 = lean::cnstr_get(x_190, 1);
x_267 = lean::cnstr_get(x_190, 2);
x_269 = lean::cnstr_get(x_190, 3);
if (lean::is_exclusive(x_190)) {
 x_271 = x_190;
} else {
 lean::inc(x_263);
 lean::inc(x_265);
 lean::inc(x_267);
 lean::inc(x_269);
 lean::dec(x_190);
 x_271 = lean::box(0);
}
if (lean::is_scalar(x_271)) {
 x_272 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_272 = x_271;
}
lean::cnstr_set(x_272, 0, x_251);
lean::cnstr_set(x_272, 1, x_253);
lean::cnstr_set(x_272, 2, x_255);
lean::cnstr_set(x_272, 3, x_251);
lean::cnstr_set_scalar(x_272, sizeof(void*)*4, x_250);
x_273 = x_272;
x_274 = 1;
if (lean::is_scalar(x_262)) {
 x_275 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_275 = x_262;
}
lean::cnstr_set(x_275, 0, x_273);
lean::cnstr_set(x_275, 1, x_1);
lean::cnstr_set(x_275, 2, x_2);
lean::cnstr_set(x_275, 3, x_263);
lean::cnstr_set_scalar(x_275, sizeof(void*)*4, x_274);
x_276 = x_275;
if (lean::is_scalar(x_257)) {
 x_277 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_277 = x_257;
}
lean::cnstr_set(x_277, 0, x_269);
lean::cnstr_set(x_277, 1, x_258);
lean::cnstr_set(x_277, 2, x_260);
lean::cnstr_set(x_277, 3, x_251);
lean::cnstr_set_scalar(x_277, sizeof(void*)*4, x_274);
x_278 = x_277;
x_279 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_279, 0, x_276);
lean::cnstr_set(x_279, 1, x_265);
lean::cnstr_set(x_279, 2, x_267);
lean::cnstr_set(x_279, 3, x_278);
lean::cnstr_set_scalar(x_279, sizeof(void*)*4, x_250);
x_280 = x_279;
return x_280;
}
else
{
uint8 x_281; 
x_281 = lean::cnstr_get_scalar<uint8>(x_251, sizeof(void*)*4);
if (x_281 == 0)
{
obj* x_282; obj* x_284; obj* x_286; obj* x_287; obj* x_289; obj* x_291; obj* x_292; obj* x_294; obj* x_296; obj* x_298; obj* x_300; obj* x_301; obj* x_303; obj* x_305; obj* x_307; obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; uint8 x_314; obj* x_315; obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; 
x_282 = lean::cnstr_get(x_0, 1);
x_284 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_286 = x_0;
} else {
 lean::inc(x_282);
 lean::inc(x_284);
 lean::dec(x_0);
 x_286 = lean::box(0);
}
x_287 = lean::cnstr_get(x_3, 1);
x_289 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_291 = x_3;
} else {
 lean::inc(x_287);
 lean::inc(x_289);
 lean::dec(x_3);
 x_291 = lean::box(0);
}
x_292 = lean::cnstr_get(x_190, 0);
x_294 = lean::cnstr_get(x_190, 1);
x_296 = lean::cnstr_get(x_190, 2);
x_298 = lean::cnstr_get(x_190, 3);
if (lean::is_exclusive(x_190)) {
 x_300 = x_190;
} else {
 lean::inc(x_292);
 lean::inc(x_294);
 lean::inc(x_296);
 lean::inc(x_298);
 lean::dec(x_190);
 x_300 = lean::box(0);
}
x_301 = lean::cnstr_get(x_251, 0);
x_303 = lean::cnstr_get(x_251, 1);
x_305 = lean::cnstr_get(x_251, 2);
x_307 = lean::cnstr_get(x_251, 3);
if (lean::is_exclusive(x_251)) {
 x_309 = x_251;
} else {
 lean::inc(x_301);
 lean::inc(x_303);
 lean::inc(x_305);
 lean::inc(x_307);
 lean::dec(x_251);
 x_309 = lean::box(0);
}
if (lean::is_scalar(x_309)) {
 x_310 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_310 = x_309;
}
lean::cnstr_set(x_310, 0, x_177);
lean::cnstr_set(x_310, 1, x_282);
lean::cnstr_set(x_310, 2, x_284);
lean::cnstr_set(x_310, 3, x_177);
lean::cnstr_set_scalar(x_310, sizeof(void*)*4, x_281);
x_311 = x_310;
if (lean::is_scalar(x_300)) {
 x_312 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_312 = x_300;
}
lean::cnstr_set(x_312, 0, x_292);
lean::cnstr_set(x_312, 1, x_294);
lean::cnstr_set(x_312, 2, x_296);
lean::cnstr_set(x_312, 3, x_298);
lean::cnstr_set_scalar(x_312, sizeof(void*)*4, x_281);
x_313 = x_312;
x_314 = 1;
if (lean::is_scalar(x_291)) {
 x_315 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_315 = x_291;
}
lean::cnstr_set(x_315, 0, x_311);
lean::cnstr_set(x_315, 1, x_1);
lean::cnstr_set(x_315, 2, x_2);
lean::cnstr_set(x_315, 3, x_313);
lean::cnstr_set_scalar(x_315, sizeof(void*)*4, x_314);
x_316 = x_315;
if (lean::is_scalar(x_286)) {
 x_317 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_317 = x_286;
}
lean::cnstr_set(x_317, 0, x_301);
lean::cnstr_set(x_317, 1, x_303);
lean::cnstr_set(x_317, 2, x_305);
lean::cnstr_set(x_317, 3, x_307);
lean::cnstr_set_scalar(x_317, sizeof(void*)*4, x_314);
x_318 = x_317;
x_319 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_319, 0, x_316);
lean::cnstr_set(x_319, 1, x_287);
lean::cnstr_set(x_319, 2, x_289);
lean::cnstr_set(x_319, 3, x_318);
lean::cnstr_set_scalar(x_319, sizeof(void*)*4, x_281);
x_320 = x_319;
return x_320;
}
else
{
obj* x_321; obj* x_323; obj* x_325; obj* x_326; obj* x_328; obj* x_330; obj* x_331; obj* x_333; obj* x_335; obj* x_337; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_344; obj* x_345; obj* x_346; obj* x_347; 
x_321 = lean::cnstr_get(x_0, 1);
x_323 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_325 = x_0;
} else {
 lean::inc(x_321);
 lean::inc(x_323);
 lean::dec(x_0);
 x_325 = lean::box(0);
}
x_326 = lean::cnstr_get(x_3, 1);
x_328 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_330 = x_3;
} else {
 lean::inc(x_326);
 lean::inc(x_328);
 lean::dec(x_3);
 x_330 = lean::box(0);
}
x_331 = lean::cnstr_get(x_190, 0);
x_333 = lean::cnstr_get(x_190, 1);
x_335 = lean::cnstr_get(x_190, 2);
x_337 = lean::cnstr_get(x_190, 3);
if (lean::is_exclusive(x_190)) {
 x_339 = x_190;
} else {
 lean::inc(x_331);
 lean::inc(x_333);
 lean::inc(x_335);
 lean::inc(x_337);
 lean::dec(x_190);
 x_339 = lean::box(0);
}
if (lean::is_scalar(x_339)) {
 x_340 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_340 = x_339;
}
lean::cnstr_set(x_340, 0, x_177);
lean::cnstr_set(x_340, 1, x_321);
lean::cnstr_set(x_340, 2, x_323);
lean::cnstr_set(x_340, 3, x_177);
lean::cnstr_set_scalar(x_340, sizeof(void*)*4, x_250);
x_341 = x_340;
if (lean::is_scalar(x_330)) {
 x_342 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_342 = x_330;
}
lean::cnstr_set(x_342, 0, x_341);
lean::cnstr_set(x_342, 1, x_1);
lean::cnstr_set(x_342, 2, x_2);
lean::cnstr_set(x_342, 3, x_331);
lean::cnstr_set_scalar(x_342, sizeof(void*)*4, x_281);
x_343 = x_342;
if (lean::is_scalar(x_325)) {
 x_344 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_344 = x_325;
}
lean::cnstr_set(x_344, 0, x_337);
lean::cnstr_set(x_344, 1, x_326);
lean::cnstr_set(x_344, 2, x_328);
lean::cnstr_set(x_344, 3, x_251);
lean::cnstr_set_scalar(x_344, sizeof(void*)*4, x_281);
x_345 = x_344;
x_346 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_346, 0, x_343);
lean::cnstr_set(x_346, 1, x_333);
lean::cnstr_set(x_346, 2, x_335);
lean::cnstr_set(x_346, 3, x_345);
lean::cnstr_set_scalar(x_346, sizeof(void*)*4, x_250);
x_347 = x_346;
return x_347;
}
}
}
else
{
obj* x_348; 
x_348 = lean::cnstr_get(x_3, 3);
lean::inc(x_348);
if (lean::obj_tag(x_348) == 0)
{
obj* x_350; obj* x_351; obj* x_353; obj* x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; 
if (lean::is_exclusive(x_190)) {
 lean::cnstr_release(x_190, 0);
 lean::cnstr_release(x_190, 1);
 lean::cnstr_release(x_190, 2);
 lean::cnstr_release(x_190, 3);
 x_350 = x_190;
} else {
 lean::dec(x_190);
 x_350 = lean::box(0);
}
x_351 = lean::cnstr_get(x_0, 1);
x_353 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_355 = x_0;
} else {
 lean::inc(x_351);
 lean::inc(x_353);
 lean::dec(x_0);
 x_355 = lean::box(0);
}
if (lean::is_scalar(x_350)) {
 x_356 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_356 = x_350;
}
lean::cnstr_set(x_356, 0, x_348);
lean::cnstr_set(x_356, 1, x_351);
lean::cnstr_set(x_356, 2, x_353);
lean::cnstr_set(x_356, 3, x_348);
lean::cnstr_set_scalar(x_356, sizeof(void*)*4, x_189);
x_357 = x_356;
if (lean::is_scalar(x_355)) {
 x_358 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_358 = x_355;
}
lean::cnstr_set(x_358, 0, x_357);
lean::cnstr_set(x_358, 1, x_1);
lean::cnstr_set(x_358, 2, x_2);
lean::cnstr_set(x_358, 3, x_3);
lean::cnstr_set_scalar(x_358, sizeof(void*)*4, x_250);
x_359 = x_358;
return x_359;
}
else
{
uint8 x_360; 
x_360 = lean::cnstr_get_scalar<uint8>(x_348, sizeof(void*)*4);
if (x_360 == 0)
{
obj* x_361; obj* x_363; obj* x_365; obj* x_366; obj* x_368; obj* x_370; obj* x_371; obj* x_373; obj* x_375; obj* x_377; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; 
x_361 = lean::cnstr_get(x_0, 1);
x_363 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_365 = x_0;
} else {
 lean::inc(x_361);
 lean::inc(x_363);
 lean::dec(x_0);
 x_365 = lean::box(0);
}
x_366 = lean::cnstr_get(x_3, 1);
x_368 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_370 = x_3;
} else {
 lean::inc(x_366);
 lean::inc(x_368);
 lean::dec(x_3);
 x_370 = lean::box(0);
}
x_371 = lean::cnstr_get(x_348, 0);
x_373 = lean::cnstr_get(x_348, 1);
x_375 = lean::cnstr_get(x_348, 2);
x_377 = lean::cnstr_get(x_348, 3);
if (lean::is_exclusive(x_348)) {
 x_379 = x_348;
} else {
 lean::inc(x_371);
 lean::inc(x_373);
 lean::inc(x_375);
 lean::inc(x_377);
 lean::dec(x_348);
 x_379 = lean::box(0);
}
if (lean::is_scalar(x_379)) {
 x_380 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_380 = x_379;
}
lean::cnstr_set(x_380, 0, x_177);
lean::cnstr_set(x_380, 1, x_361);
lean::cnstr_set(x_380, 2, x_363);
lean::cnstr_set(x_380, 3, x_177);
lean::cnstr_set_scalar(x_380, sizeof(void*)*4, x_360);
x_381 = x_380;
if (lean::is_scalar(x_370)) {
 x_382 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_382 = x_370;
}
lean::cnstr_set(x_382, 0, x_381);
lean::cnstr_set(x_382, 1, x_1);
lean::cnstr_set(x_382, 2, x_2);
lean::cnstr_set(x_382, 3, x_190);
lean::cnstr_set_scalar(x_382, sizeof(void*)*4, x_250);
x_383 = x_382;
if (lean::is_scalar(x_365)) {
 x_384 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_384 = x_365;
}
lean::cnstr_set(x_384, 0, x_371);
lean::cnstr_set(x_384, 1, x_373);
lean::cnstr_set(x_384, 2, x_375);
lean::cnstr_set(x_384, 3, x_377);
lean::cnstr_set_scalar(x_384, sizeof(void*)*4, x_250);
x_385 = x_384;
x_386 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_386, 0, x_383);
lean::cnstr_set(x_386, 1, x_366);
lean::cnstr_set(x_386, 2, x_368);
lean::cnstr_set(x_386, 3, x_385);
lean::cnstr_set_scalar(x_386, sizeof(void*)*4, x_360);
x_387 = x_386;
return x_387;
}
else
{
obj* x_388; obj* x_390; obj* x_392; obj* x_393; obj* x_395; obj* x_397; obj* x_398; obj* x_400; obj* x_402; obj* x_404; obj* x_406; obj* x_407; obj* x_408; obj* x_409; obj* x_410; obj* x_411; obj* x_412; obj* x_413; obj* x_414; 
x_388 = lean::cnstr_get(x_0, 1);
x_390 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_392 = x_0;
} else {
 lean::inc(x_388);
 lean::inc(x_390);
 lean::dec(x_0);
 x_392 = lean::box(0);
}
x_393 = lean::cnstr_get(x_3, 1);
x_395 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_397 = x_3;
} else {
 lean::inc(x_393);
 lean::inc(x_395);
 lean::dec(x_3);
 x_397 = lean::box(0);
}
x_398 = lean::cnstr_get(x_190, 0);
x_400 = lean::cnstr_get(x_190, 1);
x_402 = lean::cnstr_get(x_190, 2);
x_404 = lean::cnstr_get(x_190, 3);
if (lean::is_exclusive(x_190)) {
 x_406 = x_190;
} else {
 lean::inc(x_398);
 lean::inc(x_400);
 lean::inc(x_402);
 lean::inc(x_404);
 lean::dec(x_190);
 x_406 = lean::box(0);
}
if (lean::is_scalar(x_406)) {
 x_407 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_407 = x_406;
}
lean::cnstr_set(x_407, 0, x_177);
lean::cnstr_set(x_407, 1, x_388);
lean::cnstr_set(x_407, 2, x_390);
lean::cnstr_set(x_407, 3, x_177);
lean::cnstr_set_scalar(x_407, sizeof(void*)*4, x_189);
x_408 = x_407;
if (lean::is_scalar(x_397)) {
 x_409 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_409 = x_397;
}
lean::cnstr_set(x_409, 0, x_398);
lean::cnstr_set(x_409, 1, x_400);
lean::cnstr_set(x_409, 2, x_402);
lean::cnstr_set(x_409, 3, x_404);
lean::cnstr_set_scalar(x_409, sizeof(void*)*4, x_360);
x_410 = x_409;
if (lean::is_scalar(x_392)) {
 x_411 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_411 = x_392;
}
lean::cnstr_set(x_411, 0, x_410);
lean::cnstr_set(x_411, 1, x_393);
lean::cnstr_set(x_411, 2, x_395);
lean::cnstr_set(x_411, 3, x_348);
lean::cnstr_set_scalar(x_411, sizeof(void*)*4, x_189);
x_412 = x_411;
x_413 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_413, 0, x_408);
lean::cnstr_set(x_413, 1, x_1);
lean::cnstr_set(x_413, 2, x_2);
lean::cnstr_set(x_413, 3, x_412);
lean::cnstr_set_scalar(x_413, sizeof(void*)*4, x_360);
x_414 = x_413;
return x_414;
}
}
}
}
}
else
{
obj* x_415; obj* x_417; obj* x_419; obj* x_420; obj* x_421; obj* x_422; obj* x_423; 
x_415 = lean::cnstr_get(x_0, 1);
x_417 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_419 = x_0;
} else {
 lean::inc(x_415);
 lean::inc(x_417);
 lean::dec(x_0);
 x_419 = lean::box(0);
}
if (lean::is_scalar(x_419)) {
 x_420 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_420 = x_419;
}
lean::cnstr_set(x_420, 0, x_177);
lean::cnstr_set(x_420, 1, x_415);
lean::cnstr_set(x_420, 2, x_417);
lean::cnstr_set(x_420, 3, x_177);
lean::cnstr_set_scalar(x_420, sizeof(void*)*4, x_174);
x_421 = x_420;
x_422 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_422, 0, x_421);
lean::cnstr_set(x_422, 1, x_1);
lean::cnstr_set(x_422, 2, x_2);
lean::cnstr_set(x_422, 3, x_3);
lean::cnstr_set_scalar(x_422, sizeof(void*)*4, x_189);
x_423 = x_422;
return x_423;
}
}
}
else
{
uint8 x_424; 
x_424 = lean::cnstr_get_scalar<uint8>(x_177, sizeof(void*)*4);
if (x_424 == 0)
{
obj* x_425; obj* x_427; obj* x_429; obj* x_430; obj* x_432; obj* x_434; obj* x_436; obj* x_438; uint8 x_439; obj* x_440; obj* x_441; obj* x_442; obj* x_443; obj* x_444; obj* x_445; 
x_425 = lean::cnstr_get(x_0, 1);
x_427 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_429 = x_0;
} else {
 lean::inc(x_425);
 lean::inc(x_427);
 lean::dec(x_0);
 x_429 = lean::box(0);
}
x_430 = lean::cnstr_get(x_177, 0);
x_432 = lean::cnstr_get(x_177, 1);
x_434 = lean::cnstr_get(x_177, 2);
x_436 = lean::cnstr_get(x_177, 3);
if (lean::is_exclusive(x_177)) {
 x_438 = x_177;
} else {
 lean::inc(x_430);
 lean::inc(x_432);
 lean::inc(x_434);
 lean::inc(x_436);
 lean::dec(x_177);
 x_438 = lean::box(0);
}
x_439 = 1;
if (lean::is_scalar(x_438)) {
 x_440 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_440 = x_438;
}
lean::cnstr_set(x_440, 0, x_175);
lean::cnstr_set(x_440, 1, x_425);
lean::cnstr_set(x_440, 2, x_427);
lean::cnstr_set(x_440, 3, x_430);
lean::cnstr_set_scalar(x_440, sizeof(void*)*4, x_439);
x_441 = x_440;
if (lean::is_scalar(x_429)) {
 x_442 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_442 = x_429;
}
lean::cnstr_set(x_442, 0, x_436);
lean::cnstr_set(x_442, 1, x_1);
lean::cnstr_set(x_442, 2, x_2);
lean::cnstr_set(x_442, 3, x_3);
lean::cnstr_set_scalar(x_442, sizeof(void*)*4, x_439);
x_443 = x_442;
x_444 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_444, 0, x_441);
lean::cnstr_set(x_444, 1, x_432);
lean::cnstr_set(x_444, 2, x_434);
lean::cnstr_set(x_444, 3, x_443);
lean::cnstr_set_scalar(x_444, sizeof(void*)*4, x_424);
x_445 = x_444;
return x_445;
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_446; obj* x_448; obj* x_450; obj* x_451; obj* x_452; obj* x_453; obj* x_454; 
x_446 = lean::cnstr_get(x_0, 1);
x_448 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_450 = x_0;
} else {
 lean::inc(x_446);
 lean::inc(x_448);
 lean::dec(x_0);
 x_450 = lean::box(0);
}
if (lean::is_scalar(x_450)) {
 x_451 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_451 = x_450;
}
lean::cnstr_set(x_451, 0, x_3);
lean::cnstr_set(x_451, 1, x_446);
lean::cnstr_set(x_451, 2, x_448);
lean::cnstr_set(x_451, 3, x_177);
lean::cnstr_set_scalar(x_451, sizeof(void*)*4, x_174);
x_452 = x_451;
x_453 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_453, 0, x_452);
lean::cnstr_set(x_453, 1, x_1);
lean::cnstr_set(x_453, 2, x_2);
lean::cnstr_set(x_453, 3, x_3);
lean::cnstr_set_scalar(x_453, sizeof(void*)*4, x_424);
x_454 = x_453;
return x_454;
}
else
{
uint8 x_455; 
x_455 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*4);
if (x_455 == 0)
{
obj* x_456; 
x_456 = lean::cnstr_get(x_3, 0);
lean::inc(x_456);
if (lean::obj_tag(x_456) == 0)
{
obj* x_458; 
x_458 = lean::cnstr_get(x_3, 3);
lean::inc(x_458);
if (lean::obj_tag(x_458) == 0)
{
obj* x_460; obj* x_462; obj* x_464; obj* x_465; obj* x_467; obj* x_469; obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; obj* x_477; 
x_460 = lean::cnstr_get(x_0, 1);
x_462 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_464 = x_0;
} else {
 lean::inc(x_460);
 lean::inc(x_462);
 lean::dec(x_0);
 x_464 = lean::box(0);
}
x_465 = lean::cnstr_get(x_3, 1);
x_467 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_469 = x_3;
} else {
 lean::inc(x_465);
 lean::inc(x_467);
 lean::dec(x_3);
 x_469 = lean::box(0);
}
lean::inc(x_177);
if (lean::is_scalar(x_469)) {
 x_471 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_471 = x_469;
}
lean::cnstr_set(x_471, 0, x_458);
lean::cnstr_set(x_471, 1, x_460);
lean::cnstr_set(x_471, 2, x_462);
lean::cnstr_set(x_471, 3, x_177);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_472 = x_177;
} else {
 lean::dec(x_177);
 x_472 = lean::box(0);
}
lean::cnstr_set_scalar(x_471, sizeof(void*)*4, x_455);
x_473 = x_471;
if (lean::is_scalar(x_472)) {
 x_474 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_474 = x_472;
}
lean::cnstr_set(x_474, 0, x_458);
lean::cnstr_set(x_474, 1, x_465);
lean::cnstr_set(x_474, 2, x_467);
lean::cnstr_set(x_474, 3, x_458);
lean::cnstr_set_scalar(x_474, sizeof(void*)*4, x_455);
x_475 = x_474;
if (lean::is_scalar(x_464)) {
 x_476 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_476 = x_464;
}
lean::cnstr_set(x_476, 0, x_473);
lean::cnstr_set(x_476, 1, x_1);
lean::cnstr_set(x_476, 2, x_2);
lean::cnstr_set(x_476, 3, x_475);
lean::cnstr_set_scalar(x_476, sizeof(void*)*4, x_424);
x_477 = x_476;
return x_477;
}
else
{
uint8 x_478; 
x_478 = lean::cnstr_get_scalar<uint8>(x_458, sizeof(void*)*4);
if (x_478 == 0)
{
obj* x_479; obj* x_481; obj* x_483; obj* x_484; obj* x_486; obj* x_488; obj* x_489; obj* x_491; obj* x_493; obj* x_495; obj* x_497; obj* x_499; obj* x_500; obj* x_501; obj* x_502; obj* x_503; obj* x_504; obj* x_505; obj* x_506; obj* x_507; 
x_479 = lean::cnstr_get(x_0, 1);
x_481 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_483 = x_0;
} else {
 lean::inc(x_479);
 lean::inc(x_481);
 lean::dec(x_0);
 x_483 = lean::box(0);
}
x_484 = lean::cnstr_get(x_3, 1);
x_486 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_488 = x_3;
} else {
 lean::inc(x_484);
 lean::inc(x_486);
 lean::dec(x_3);
 x_488 = lean::box(0);
}
x_489 = lean::cnstr_get(x_458, 0);
x_491 = lean::cnstr_get(x_458, 1);
x_493 = lean::cnstr_get(x_458, 2);
x_495 = lean::cnstr_get(x_458, 3);
if (lean::is_exclusive(x_458)) {
 x_497 = x_458;
} else {
 lean::inc(x_489);
 lean::inc(x_491);
 lean::inc(x_493);
 lean::inc(x_495);
 lean::dec(x_458);
 x_497 = lean::box(0);
}
lean::inc(x_177);
if (lean::is_scalar(x_497)) {
 x_499 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_499 = x_497;
}
lean::cnstr_set(x_499, 0, x_456);
lean::cnstr_set(x_499, 1, x_479);
lean::cnstr_set(x_499, 2, x_481);
lean::cnstr_set(x_499, 3, x_177);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_500 = x_177;
} else {
 lean::dec(x_177);
 x_500 = lean::box(0);
}
lean::cnstr_set_scalar(x_499, sizeof(void*)*4, x_478);
x_501 = x_499;
if (lean::is_scalar(x_488)) {
 x_502 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_502 = x_488;
}
lean::cnstr_set(x_502, 0, x_501);
lean::cnstr_set(x_502, 1, x_1);
lean::cnstr_set(x_502, 2, x_2);
lean::cnstr_set(x_502, 3, x_456);
lean::cnstr_set_scalar(x_502, sizeof(void*)*4, x_424);
x_503 = x_502;
if (lean::is_scalar(x_500)) {
 x_504 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_504 = x_500;
}
lean::cnstr_set(x_504, 0, x_489);
lean::cnstr_set(x_504, 1, x_491);
lean::cnstr_set(x_504, 2, x_493);
lean::cnstr_set(x_504, 3, x_495);
lean::cnstr_set_scalar(x_504, sizeof(void*)*4, x_424);
x_505 = x_504;
if (lean::is_scalar(x_483)) {
 x_506 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_506 = x_483;
}
lean::cnstr_set(x_506, 0, x_503);
lean::cnstr_set(x_506, 1, x_484);
lean::cnstr_set(x_506, 2, x_486);
lean::cnstr_set(x_506, 3, x_505);
lean::cnstr_set_scalar(x_506, sizeof(void*)*4, x_478);
x_507 = x_506;
return x_507;
}
else
{
obj* x_508; obj* x_509; obj* x_511; obj* x_513; obj* x_514; obj* x_516; obj* x_518; obj* x_520; obj* x_522; obj* x_523; obj* x_524; obj* x_525; obj* x_526; obj* x_527; obj* x_528; 
if (lean::is_exclusive(x_458)) {
 lean::cnstr_release(x_458, 0);
 lean::cnstr_release(x_458, 1);
 lean::cnstr_release(x_458, 2);
 lean::cnstr_release(x_458, 3);
 x_508 = x_458;
} else {
 lean::dec(x_458);
 x_508 = lean::box(0);
}
x_509 = lean::cnstr_get(x_0, 1);
x_511 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_513 = x_0;
} else {
 lean::inc(x_509);
 lean::inc(x_511);
 lean::dec(x_0);
 x_513 = lean::box(0);
}
x_514 = lean::cnstr_get(x_177, 0);
x_516 = lean::cnstr_get(x_177, 1);
x_518 = lean::cnstr_get(x_177, 2);
x_520 = lean::cnstr_get(x_177, 3);
if (lean::is_exclusive(x_177)) {
 x_522 = x_177;
} else {
 lean::inc(x_514);
 lean::inc(x_516);
 lean::inc(x_518);
 lean::inc(x_520);
 lean::dec(x_177);
 x_522 = lean::box(0);
}
if (lean::is_scalar(x_508)) {
 x_523 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_523 = x_508;
}
lean::cnstr_set(x_523, 0, x_514);
lean::cnstr_set(x_523, 1, x_516);
lean::cnstr_set(x_523, 2, x_518);
lean::cnstr_set(x_523, 3, x_520);
lean::cnstr_set_scalar(x_523, sizeof(void*)*4, x_478);
x_524 = x_523;
if (lean::is_scalar(x_522)) {
 x_525 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_525 = x_522;
}
lean::cnstr_set(x_525, 0, x_456);
lean::cnstr_set(x_525, 1, x_509);
lean::cnstr_set(x_525, 2, x_511);
lean::cnstr_set(x_525, 3, x_524);
lean::cnstr_set_scalar(x_525, sizeof(void*)*4, x_455);
x_526 = x_525;
if (lean::is_scalar(x_513)) {
 x_527 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_527 = x_513;
}
lean::cnstr_set(x_527, 0, x_526);
lean::cnstr_set(x_527, 1, x_1);
lean::cnstr_set(x_527, 2, x_2);
lean::cnstr_set(x_527, 3, x_3);
lean::cnstr_set_scalar(x_527, sizeof(void*)*4, x_478);
x_528 = x_527;
return x_528;
}
}
}
else
{
uint8 x_529; 
x_529 = lean::cnstr_get_scalar<uint8>(x_456, sizeof(void*)*4);
if (x_529 == 0)
{
obj* x_530; 
x_530 = lean::cnstr_get(x_3, 3);
lean::inc(x_530);
if (lean::obj_tag(x_530) == 0)
{
obj* x_532; obj* x_534; obj* x_536; obj* x_537; obj* x_539; obj* x_541; obj* x_542; obj* x_544; obj* x_546; obj* x_548; obj* x_550; obj* x_552; obj* x_553; obj* x_554; obj* x_555; obj* x_556; obj* x_557; obj* x_558; obj* x_559; obj* x_560; 
x_532 = lean::cnstr_get(x_0, 1);
x_534 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_536 = x_0;
} else {
 lean::inc(x_532);
 lean::inc(x_534);
 lean::dec(x_0);
 x_536 = lean::box(0);
}
x_537 = lean::cnstr_get(x_3, 1);
x_539 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_541 = x_3;
} else {
 lean::inc(x_537);
 lean::inc(x_539);
 lean::dec(x_3);
 x_541 = lean::box(0);
}
x_542 = lean::cnstr_get(x_456, 0);
x_544 = lean::cnstr_get(x_456, 1);
x_546 = lean::cnstr_get(x_456, 2);
x_548 = lean::cnstr_get(x_456, 3);
if (lean::is_exclusive(x_456)) {
 x_550 = x_456;
} else {
 lean::inc(x_542);
 lean::inc(x_544);
 lean::inc(x_546);
 lean::inc(x_548);
 lean::dec(x_456);
 x_550 = lean::box(0);
}
lean::inc(x_177);
if (lean::is_scalar(x_550)) {
 x_552 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_552 = x_550;
}
lean::cnstr_set(x_552, 0, x_530);
lean::cnstr_set(x_552, 1, x_532);
lean::cnstr_set(x_552, 2, x_534);
lean::cnstr_set(x_552, 3, x_177);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_553 = x_177;
} else {
 lean::dec(x_177);
 x_553 = lean::box(0);
}
lean::cnstr_set_scalar(x_552, sizeof(void*)*4, x_529);
x_554 = x_552;
if (lean::is_scalar(x_541)) {
 x_555 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_555 = x_541;
}
lean::cnstr_set(x_555, 0, x_554);
lean::cnstr_set(x_555, 1, x_1);
lean::cnstr_set(x_555, 2, x_2);
lean::cnstr_set(x_555, 3, x_542);
lean::cnstr_set_scalar(x_555, sizeof(void*)*4, x_424);
x_556 = x_555;
if (lean::is_scalar(x_553)) {
 x_557 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_557 = x_553;
}
lean::cnstr_set(x_557, 0, x_548);
lean::cnstr_set(x_557, 1, x_537);
lean::cnstr_set(x_557, 2, x_539);
lean::cnstr_set(x_557, 3, x_530);
lean::cnstr_set_scalar(x_557, sizeof(void*)*4, x_424);
x_558 = x_557;
if (lean::is_scalar(x_536)) {
 x_559 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_559 = x_536;
}
lean::cnstr_set(x_559, 0, x_556);
lean::cnstr_set(x_559, 1, x_544);
lean::cnstr_set(x_559, 2, x_546);
lean::cnstr_set(x_559, 3, x_558);
lean::cnstr_set_scalar(x_559, sizeof(void*)*4, x_529);
x_560 = x_559;
return x_560;
}
else
{
uint8 x_561; 
x_561 = lean::cnstr_get_scalar<uint8>(x_530, sizeof(void*)*4);
if (x_561 == 0)
{
obj* x_562; obj* x_564; obj* x_566; obj* x_567; obj* x_569; obj* x_571; obj* x_572; obj* x_574; obj* x_576; obj* x_578; obj* x_580; obj* x_581; obj* x_583; obj* x_585; obj* x_587; obj* x_589; obj* x_591; obj* x_592; obj* x_593; obj* x_594; obj* x_595; obj* x_596; obj* x_597; obj* x_598; obj* x_599; obj* x_600; obj* x_601; 
x_562 = lean::cnstr_get(x_0, 1);
x_564 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_566 = x_0;
} else {
 lean::inc(x_562);
 lean::inc(x_564);
 lean::dec(x_0);
 x_566 = lean::box(0);
}
x_567 = lean::cnstr_get(x_3, 1);
x_569 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_571 = x_3;
} else {
 lean::inc(x_567);
 lean::inc(x_569);
 lean::dec(x_3);
 x_571 = lean::box(0);
}
x_572 = lean::cnstr_get(x_456, 0);
x_574 = lean::cnstr_get(x_456, 1);
x_576 = lean::cnstr_get(x_456, 2);
x_578 = lean::cnstr_get(x_456, 3);
if (lean::is_exclusive(x_456)) {
 x_580 = x_456;
} else {
 lean::inc(x_572);
 lean::inc(x_574);
 lean::inc(x_576);
 lean::inc(x_578);
 lean::dec(x_456);
 x_580 = lean::box(0);
}
x_581 = lean::cnstr_get(x_530, 0);
x_583 = lean::cnstr_get(x_530, 1);
x_585 = lean::cnstr_get(x_530, 2);
x_587 = lean::cnstr_get(x_530, 3);
if (lean::is_exclusive(x_530)) {
 x_589 = x_530;
} else {
 lean::inc(x_581);
 lean::inc(x_583);
 lean::inc(x_585);
 lean::inc(x_587);
 lean::dec(x_530);
 x_589 = lean::box(0);
}
lean::inc(x_177);
if (lean::is_scalar(x_589)) {
 x_591 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_591 = x_589;
}
lean::cnstr_set(x_591, 0, x_175);
lean::cnstr_set(x_591, 1, x_562);
lean::cnstr_set(x_591, 2, x_564);
lean::cnstr_set(x_591, 3, x_177);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 lean::cnstr_release(x_177, 2);
 lean::cnstr_release(x_177, 3);
 x_592 = x_177;
} else {
 lean::dec(x_177);
 x_592 = lean::box(0);
}
lean::cnstr_set_scalar(x_591, sizeof(void*)*4, x_561);
x_593 = x_591;
if (lean::is_scalar(x_580)) {
 x_594 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_594 = x_580;
}
lean::cnstr_set(x_594, 0, x_572);
lean::cnstr_set(x_594, 1, x_574);
lean::cnstr_set(x_594, 2, x_576);
lean::cnstr_set(x_594, 3, x_578);
lean::cnstr_set_scalar(x_594, sizeof(void*)*4, x_561);
x_595 = x_594;
if (lean::is_scalar(x_571)) {
 x_596 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_596 = x_571;
}
lean::cnstr_set(x_596, 0, x_593);
lean::cnstr_set(x_596, 1, x_1);
lean::cnstr_set(x_596, 2, x_2);
lean::cnstr_set(x_596, 3, x_595);
lean::cnstr_set_scalar(x_596, sizeof(void*)*4, x_424);
x_597 = x_596;
if (lean::is_scalar(x_592)) {
 x_598 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_598 = x_592;
}
lean::cnstr_set(x_598, 0, x_581);
lean::cnstr_set(x_598, 1, x_583);
lean::cnstr_set(x_598, 2, x_585);
lean::cnstr_set(x_598, 3, x_587);
lean::cnstr_set_scalar(x_598, sizeof(void*)*4, x_424);
x_599 = x_598;
if (lean::is_scalar(x_566)) {
 x_600 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_600 = x_566;
}
lean::cnstr_set(x_600, 0, x_597);
lean::cnstr_set(x_600, 1, x_567);
lean::cnstr_set(x_600, 2, x_569);
lean::cnstr_set(x_600, 3, x_599);
lean::cnstr_set_scalar(x_600, sizeof(void*)*4, x_561);
x_601 = x_600;
return x_601;
}
else
{
obj* x_602; obj* x_604; obj* x_606; obj* x_607; obj* x_609; obj* x_611; obj* x_613; obj* x_615; obj* x_616; obj* x_618; obj* x_620; obj* x_621; obj* x_623; obj* x_625; obj* x_627; obj* x_629; obj* x_630; obj* x_631; obj* x_632; obj* x_633; obj* x_634; obj* x_635; obj* x_636; obj* x_637; obj* x_638; obj* x_639; 
x_602 = lean::cnstr_get(x_0, 1);
x_604 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_606 = x_0;
} else {
 lean::inc(x_602);
 lean::inc(x_604);
 lean::dec(x_0);
 x_606 = lean::box(0);
}
x_607 = lean::cnstr_get(x_177, 0);
x_609 = lean::cnstr_get(x_177, 1);
x_611 = lean::cnstr_get(x_177, 2);
x_613 = lean::cnstr_get(x_177, 3);
if (lean::is_exclusive(x_177)) {
 x_615 = x_177;
} else {
 lean::inc(x_607);
 lean::inc(x_609);
 lean::inc(x_611);
 lean::inc(x_613);
 lean::dec(x_177);
 x_615 = lean::box(0);
}
x_616 = lean::cnstr_get(x_3, 1);
x_618 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_620 = x_3;
} else {
 lean::inc(x_616);
 lean::inc(x_618);
 lean::dec(x_3);
 x_620 = lean::box(0);
}
x_621 = lean::cnstr_get(x_456, 0);
x_623 = lean::cnstr_get(x_456, 1);
x_625 = lean::cnstr_get(x_456, 2);
x_627 = lean::cnstr_get(x_456, 3);
if (lean::is_exclusive(x_456)) {
 x_629 = x_456;
} else {
 lean::inc(x_621);
 lean::inc(x_623);
 lean::inc(x_625);
 lean::inc(x_627);
 lean::dec(x_456);
 x_629 = lean::box(0);
}
if (lean::is_scalar(x_629)) {
 x_630 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_630 = x_629;
}
lean::cnstr_set(x_630, 0, x_607);
lean::cnstr_set(x_630, 1, x_609);
lean::cnstr_set(x_630, 2, x_611);
lean::cnstr_set(x_630, 3, x_613);
lean::cnstr_set_scalar(x_630, sizeof(void*)*4, x_561);
x_631 = x_630;
if (lean::is_scalar(x_620)) {
 x_632 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_632 = x_620;
}
lean::cnstr_set(x_632, 0, x_175);
lean::cnstr_set(x_632, 1, x_602);
lean::cnstr_set(x_632, 2, x_604);
lean::cnstr_set(x_632, 3, x_631);
lean::cnstr_set_scalar(x_632, sizeof(void*)*4, x_529);
x_633 = x_632;
if (lean::is_scalar(x_615)) {
 x_634 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_634 = x_615;
}
lean::cnstr_set(x_634, 0, x_633);
lean::cnstr_set(x_634, 1, x_1);
lean::cnstr_set(x_634, 2, x_2);
lean::cnstr_set(x_634, 3, x_621);
lean::cnstr_set_scalar(x_634, sizeof(void*)*4, x_561);
x_635 = x_634;
if (lean::is_scalar(x_606)) {
 x_636 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_636 = x_606;
}
lean::cnstr_set(x_636, 0, x_627);
lean::cnstr_set(x_636, 1, x_616);
lean::cnstr_set(x_636, 2, x_618);
lean::cnstr_set(x_636, 3, x_530);
lean::cnstr_set_scalar(x_636, sizeof(void*)*4, x_561);
x_637 = x_636;
x_638 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_638, 0, x_635);
lean::cnstr_set(x_638, 1, x_623);
lean::cnstr_set(x_638, 2, x_625);
lean::cnstr_set(x_638, 3, x_637);
lean::cnstr_set_scalar(x_638, sizeof(void*)*4, x_529);
x_639 = x_638;
return x_639;
}
}
}
else
{
obj* x_640; 
x_640 = lean::cnstr_get(x_3, 3);
lean::inc(x_640);
if (lean::obj_tag(x_640) == 0)
{
obj* x_642; obj* x_643; obj* x_645; obj* x_647; obj* x_648; obj* x_650; obj* x_652; obj* x_654; obj* x_656; obj* x_657; obj* x_658; obj* x_659; obj* x_660; obj* x_661; obj* x_662; 
if (lean::is_exclusive(x_456)) {
 lean::cnstr_release(x_456, 0);
 lean::cnstr_release(x_456, 1);
 lean::cnstr_release(x_456, 2);
 lean::cnstr_release(x_456, 3);
 x_642 = x_456;
} else {
 lean::dec(x_456);
 x_642 = lean::box(0);
}
x_643 = lean::cnstr_get(x_0, 1);
x_645 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_647 = x_0;
} else {
 lean::inc(x_643);
 lean::inc(x_645);
 lean::dec(x_0);
 x_647 = lean::box(0);
}
x_648 = lean::cnstr_get(x_177, 0);
x_650 = lean::cnstr_get(x_177, 1);
x_652 = lean::cnstr_get(x_177, 2);
x_654 = lean::cnstr_get(x_177, 3);
if (lean::is_exclusive(x_177)) {
 x_656 = x_177;
} else {
 lean::inc(x_648);
 lean::inc(x_650);
 lean::inc(x_652);
 lean::inc(x_654);
 lean::dec(x_177);
 x_656 = lean::box(0);
}
if (lean::is_scalar(x_642)) {
 x_657 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_657 = x_642;
}
lean::cnstr_set(x_657, 0, x_648);
lean::cnstr_set(x_657, 1, x_650);
lean::cnstr_set(x_657, 2, x_652);
lean::cnstr_set(x_657, 3, x_654);
lean::cnstr_set_scalar(x_657, sizeof(void*)*4, x_529);
x_658 = x_657;
if (lean::is_scalar(x_656)) {
 x_659 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_659 = x_656;
}
lean::cnstr_set(x_659, 0, x_640);
lean::cnstr_set(x_659, 1, x_643);
lean::cnstr_set(x_659, 2, x_645);
lean::cnstr_set(x_659, 3, x_658);
lean::cnstr_set_scalar(x_659, sizeof(void*)*4, x_455);
x_660 = x_659;
if (lean::is_scalar(x_647)) {
 x_661 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_661 = x_647;
}
lean::cnstr_set(x_661, 0, x_660);
lean::cnstr_set(x_661, 1, x_1);
lean::cnstr_set(x_661, 2, x_2);
lean::cnstr_set(x_661, 3, x_3);
lean::cnstr_set_scalar(x_661, sizeof(void*)*4, x_529);
x_662 = x_661;
return x_662;
}
else
{
uint8 x_663; 
x_663 = lean::cnstr_get_scalar<uint8>(x_640, sizeof(void*)*4);
if (x_663 == 0)
{
obj* x_664; obj* x_666; obj* x_668; obj* x_669; obj* x_671; obj* x_673; obj* x_675; obj* x_677; obj* x_678; obj* x_680; obj* x_682; obj* x_683; obj* x_685; obj* x_687; obj* x_689; obj* x_691; obj* x_692; obj* x_693; obj* x_694; obj* x_695; obj* x_696; obj* x_697; obj* x_698; obj* x_699; obj* x_700; obj* x_701; 
x_664 = lean::cnstr_get(x_0, 1);
x_666 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_668 = x_0;
} else {
 lean::inc(x_664);
 lean::inc(x_666);
 lean::dec(x_0);
 x_668 = lean::box(0);
}
x_669 = lean::cnstr_get(x_177, 0);
x_671 = lean::cnstr_get(x_177, 1);
x_673 = lean::cnstr_get(x_177, 2);
x_675 = lean::cnstr_get(x_177, 3);
if (lean::is_exclusive(x_177)) {
 x_677 = x_177;
} else {
 lean::inc(x_669);
 lean::inc(x_671);
 lean::inc(x_673);
 lean::inc(x_675);
 lean::dec(x_177);
 x_677 = lean::box(0);
}
x_678 = lean::cnstr_get(x_3, 1);
x_680 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_682 = x_3;
} else {
 lean::inc(x_678);
 lean::inc(x_680);
 lean::dec(x_3);
 x_682 = lean::box(0);
}
x_683 = lean::cnstr_get(x_640, 0);
x_685 = lean::cnstr_get(x_640, 1);
x_687 = lean::cnstr_get(x_640, 2);
x_689 = lean::cnstr_get(x_640, 3);
if (lean::is_exclusive(x_640)) {
 x_691 = x_640;
} else {
 lean::inc(x_683);
 lean::inc(x_685);
 lean::inc(x_687);
 lean::inc(x_689);
 lean::dec(x_640);
 x_691 = lean::box(0);
}
if (lean::is_scalar(x_691)) {
 x_692 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_692 = x_691;
}
lean::cnstr_set(x_692, 0, x_669);
lean::cnstr_set(x_692, 1, x_671);
lean::cnstr_set(x_692, 2, x_673);
lean::cnstr_set(x_692, 3, x_675);
lean::cnstr_set_scalar(x_692, sizeof(void*)*4, x_529);
x_693 = x_692;
if (lean::is_scalar(x_682)) {
 x_694 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_694 = x_682;
}
lean::cnstr_set(x_694, 0, x_175);
lean::cnstr_set(x_694, 1, x_664);
lean::cnstr_set(x_694, 2, x_666);
lean::cnstr_set(x_694, 3, x_693);
lean::cnstr_set_scalar(x_694, sizeof(void*)*4, x_663);
x_695 = x_694;
if (lean::is_scalar(x_677)) {
 x_696 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_696 = x_677;
}
lean::cnstr_set(x_696, 0, x_695);
lean::cnstr_set(x_696, 1, x_1);
lean::cnstr_set(x_696, 2, x_2);
lean::cnstr_set(x_696, 3, x_456);
lean::cnstr_set_scalar(x_696, sizeof(void*)*4, x_529);
x_697 = x_696;
if (lean::is_scalar(x_668)) {
 x_698 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_698 = x_668;
}
lean::cnstr_set(x_698, 0, x_683);
lean::cnstr_set(x_698, 1, x_685);
lean::cnstr_set(x_698, 2, x_687);
lean::cnstr_set(x_698, 3, x_689);
lean::cnstr_set_scalar(x_698, sizeof(void*)*4, x_529);
x_699 = x_698;
x_700 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_700, 0, x_697);
lean::cnstr_set(x_700, 1, x_678);
lean::cnstr_set(x_700, 2, x_680);
lean::cnstr_set(x_700, 3, x_699);
lean::cnstr_set_scalar(x_700, sizeof(void*)*4, x_663);
x_701 = x_700;
return x_701;
}
else
{
obj* x_702; obj* x_704; obj* x_706; obj* x_707; obj* x_709; obj* x_711; obj* x_713; obj* x_715; obj* x_716; obj* x_718; obj* x_720; obj* x_721; obj* x_723; obj* x_725; obj* x_727; obj* x_729; obj* x_730; obj* x_731; obj* x_732; obj* x_733; obj* x_734; obj* x_735; obj* x_736; obj* x_737; obj* x_738; obj* x_739; 
x_702 = lean::cnstr_get(x_0, 1);
x_704 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_706 = x_0;
} else {
 lean::inc(x_702);
 lean::inc(x_704);
 lean::dec(x_0);
 x_706 = lean::box(0);
}
x_707 = lean::cnstr_get(x_177, 0);
x_709 = lean::cnstr_get(x_177, 1);
x_711 = lean::cnstr_get(x_177, 2);
x_713 = lean::cnstr_get(x_177, 3);
if (lean::is_exclusive(x_177)) {
 x_715 = x_177;
} else {
 lean::inc(x_707);
 lean::inc(x_709);
 lean::inc(x_711);
 lean::inc(x_713);
 lean::dec(x_177);
 x_715 = lean::box(0);
}
x_716 = lean::cnstr_get(x_3, 1);
x_718 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_720 = x_3;
} else {
 lean::inc(x_716);
 lean::inc(x_718);
 lean::dec(x_3);
 x_720 = lean::box(0);
}
x_721 = lean::cnstr_get(x_456, 0);
x_723 = lean::cnstr_get(x_456, 1);
x_725 = lean::cnstr_get(x_456, 2);
x_727 = lean::cnstr_get(x_456, 3);
if (lean::is_exclusive(x_456)) {
 x_729 = x_456;
} else {
 lean::inc(x_721);
 lean::inc(x_723);
 lean::inc(x_725);
 lean::inc(x_727);
 lean::dec(x_456);
 x_729 = lean::box(0);
}
if (lean::is_scalar(x_729)) {
 x_730 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_730 = x_729;
}
lean::cnstr_set(x_730, 0, x_707);
lean::cnstr_set(x_730, 1, x_709);
lean::cnstr_set(x_730, 2, x_711);
lean::cnstr_set(x_730, 3, x_713);
lean::cnstr_set_scalar(x_730, sizeof(void*)*4, x_663);
x_731 = x_730;
if (lean::is_scalar(x_720)) {
 x_732 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_732 = x_720;
}
lean::cnstr_set(x_732, 0, x_175);
lean::cnstr_set(x_732, 1, x_702);
lean::cnstr_set(x_732, 2, x_704);
lean::cnstr_set(x_732, 3, x_731);
lean::cnstr_set_scalar(x_732, sizeof(void*)*4, x_455);
x_733 = x_732;
if (lean::is_scalar(x_715)) {
 x_734 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_734 = x_715;
}
lean::cnstr_set(x_734, 0, x_721);
lean::cnstr_set(x_734, 1, x_723);
lean::cnstr_set(x_734, 2, x_725);
lean::cnstr_set(x_734, 3, x_727);
lean::cnstr_set_scalar(x_734, sizeof(void*)*4, x_663);
x_735 = x_734;
if (lean::is_scalar(x_706)) {
 x_736 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_736 = x_706;
}
lean::cnstr_set(x_736, 0, x_735);
lean::cnstr_set(x_736, 1, x_716);
lean::cnstr_set(x_736, 2, x_718);
lean::cnstr_set(x_736, 3, x_640);
lean::cnstr_set_scalar(x_736, sizeof(void*)*4, x_455);
x_737 = x_736;
x_738 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_738, 0, x_733);
lean::cnstr_set(x_738, 1, x_1);
lean::cnstr_set(x_738, 2, x_2);
lean::cnstr_set(x_738, 3, x_737);
lean::cnstr_set_scalar(x_738, sizeof(void*)*4, x_663);
x_739 = x_738;
return x_739;
}
}
}
}
}
else
{
obj* x_740; obj* x_742; obj* x_744; obj* x_745; obj* x_747; obj* x_749; obj* x_751; obj* x_753; obj* x_754; obj* x_755; obj* x_756; obj* x_757; obj* x_758; obj* x_759; 
x_740 = lean::cnstr_get(x_0, 1);
x_742 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_744 = x_0;
} else {
 lean::inc(x_740);
 lean::inc(x_742);
 lean::dec(x_0);
 x_744 = lean::box(0);
}
x_745 = lean::cnstr_get(x_177, 0);
x_747 = lean::cnstr_get(x_177, 1);
x_749 = lean::cnstr_get(x_177, 2);
x_751 = lean::cnstr_get(x_177, 3);
if (lean::is_exclusive(x_177)) {
 x_753 = x_177;
} else {
 lean::inc(x_745);
 lean::inc(x_747);
 lean::inc(x_749);
 lean::inc(x_751);
 lean::dec(x_177);
 x_753 = lean::box(0);
}
if (lean::is_scalar(x_753)) {
 x_754 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_754 = x_753;
}
lean::cnstr_set(x_754, 0, x_745);
lean::cnstr_set(x_754, 1, x_747);
lean::cnstr_set(x_754, 2, x_749);
lean::cnstr_set(x_754, 3, x_751);
lean::cnstr_set_scalar(x_754, sizeof(void*)*4, x_455);
x_755 = x_754;
if (lean::is_scalar(x_744)) {
 x_756 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_756 = x_744;
}
lean::cnstr_set(x_756, 0, x_175);
lean::cnstr_set(x_756, 1, x_740);
lean::cnstr_set(x_756, 2, x_742);
lean::cnstr_set(x_756, 3, x_755);
lean::cnstr_set_scalar(x_756, sizeof(void*)*4, x_174);
x_757 = x_756;
x_758 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_758, 0, x_757);
lean::cnstr_set(x_758, 1, x_1);
lean::cnstr_set(x_758, 2, x_2);
lean::cnstr_set(x_758, 3, x_3);
lean::cnstr_set_scalar(x_758, sizeof(void*)*4, x_455);
x_759 = x_758;
return x_759;
}
}
}
}
}
else
{
uint8 x_760; 
x_760 = lean::cnstr_get_scalar<uint8>(x_175, sizeof(void*)*4);
if (x_760 == 0)
{
obj* x_761; obj* x_763; obj* x_765; obj* x_767; obj* x_768; obj* x_770; obj* x_772; obj* x_774; obj* x_776; uint8 x_777; obj* x_778; obj* x_779; obj* x_780; obj* x_781; obj* x_782; obj* x_783; 
x_761 = lean::cnstr_get(x_0, 1);
x_763 = lean::cnstr_get(x_0, 2);
x_765 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_767 = x_0;
} else {
 lean::inc(x_761);
 lean::inc(x_763);
 lean::inc(x_765);
 lean::dec(x_0);
 x_767 = lean::box(0);
}
x_768 = lean::cnstr_get(x_175, 0);
x_770 = lean::cnstr_get(x_175, 1);
x_772 = lean::cnstr_get(x_175, 2);
x_774 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_776 = x_175;
} else {
 lean::inc(x_768);
 lean::inc(x_770);
 lean::inc(x_772);
 lean::inc(x_774);
 lean::dec(x_175);
 x_776 = lean::box(0);
}
x_777 = 1;
if (lean::is_scalar(x_776)) {
 x_778 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_778 = x_776;
}
lean::cnstr_set(x_778, 0, x_768);
lean::cnstr_set(x_778, 1, x_770);
lean::cnstr_set(x_778, 2, x_772);
lean::cnstr_set(x_778, 3, x_774);
lean::cnstr_set_scalar(x_778, sizeof(void*)*4, x_777);
x_779 = x_778;
if (lean::is_scalar(x_767)) {
 x_780 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_780 = x_767;
}
lean::cnstr_set(x_780, 0, x_765);
lean::cnstr_set(x_780, 1, x_1);
lean::cnstr_set(x_780, 2, x_2);
lean::cnstr_set(x_780, 3, x_3);
lean::cnstr_set_scalar(x_780, sizeof(void*)*4, x_777);
x_781 = x_780;
x_782 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_782, 0, x_779);
lean::cnstr_set(x_782, 1, x_761);
lean::cnstr_set(x_782, 2, x_763);
lean::cnstr_set(x_782, 3, x_781);
lean::cnstr_set_scalar(x_782, sizeof(void*)*4, x_760);
x_783 = x_782;
return x_783;
}
else
{
obj* x_784; 
x_784 = lean::cnstr_get(x_0, 3);
lean::inc(x_784);
if (lean::obj_tag(x_784) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_786; obj* x_788; obj* x_790; obj* x_791; obj* x_792; obj* x_793; obj* x_794; 
x_786 = lean::cnstr_get(x_0, 1);
x_788 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_790 = x_0;
} else {
 lean::inc(x_786);
 lean::inc(x_788);
 lean::dec(x_0);
 x_790 = lean::box(0);
}
if (lean::is_scalar(x_790)) {
 x_791 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_791 = x_790;
}
lean::cnstr_set(x_791, 0, x_175);
lean::cnstr_set(x_791, 1, x_786);
lean::cnstr_set(x_791, 2, x_788);
lean::cnstr_set(x_791, 3, x_3);
lean::cnstr_set_scalar(x_791, sizeof(void*)*4, x_174);
x_792 = x_791;
x_793 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_793, 0, x_792);
lean::cnstr_set(x_793, 1, x_1);
lean::cnstr_set(x_793, 2, x_2);
lean::cnstr_set(x_793, 3, x_3);
lean::cnstr_set_scalar(x_793, sizeof(void*)*4, x_760);
x_794 = x_793;
return x_794;
}
else
{
uint8 x_795; 
x_795 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*4);
if (x_795 == 0)
{
obj* x_796; 
x_796 = lean::cnstr_get(x_3, 0);
lean::inc(x_796);
if (lean::obj_tag(x_796) == 0)
{
obj* x_798; 
x_798 = lean::cnstr_get(x_3, 3);
lean::inc(x_798);
if (lean::obj_tag(x_798) == 0)
{
obj* x_800; obj* x_802; obj* x_804; obj* x_805; obj* x_807; obj* x_809; obj* x_811; obj* x_812; obj* x_813; obj* x_814; obj* x_815; obj* x_816; obj* x_817; 
x_800 = lean::cnstr_get(x_0, 1);
x_802 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_804 = x_0;
} else {
 lean::inc(x_800);
 lean::inc(x_802);
 lean::dec(x_0);
 x_804 = lean::box(0);
}
x_805 = lean::cnstr_get(x_3, 1);
x_807 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_809 = x_3;
} else {
 lean::inc(x_805);
 lean::inc(x_807);
 lean::dec(x_3);
 x_809 = lean::box(0);
}
lean::inc(x_175);
if (lean::is_scalar(x_809)) {
 x_811 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_811 = x_809;
}
lean::cnstr_set(x_811, 0, x_175);
lean::cnstr_set(x_811, 1, x_800);
lean::cnstr_set(x_811, 2, x_802);
lean::cnstr_set(x_811, 3, x_798);
if (lean::is_exclusive(x_175)) {
 lean::cnstr_release(x_175, 0);
 lean::cnstr_release(x_175, 1);
 lean::cnstr_release(x_175, 2);
 lean::cnstr_release(x_175, 3);
 x_812 = x_175;
} else {
 lean::dec(x_175);
 x_812 = lean::box(0);
}
lean::cnstr_set_scalar(x_811, sizeof(void*)*4, x_795);
x_813 = x_811;
if (lean::is_scalar(x_812)) {
 x_814 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_814 = x_812;
}
lean::cnstr_set(x_814, 0, x_798);
lean::cnstr_set(x_814, 1, x_805);
lean::cnstr_set(x_814, 2, x_807);
lean::cnstr_set(x_814, 3, x_798);
lean::cnstr_set_scalar(x_814, sizeof(void*)*4, x_795);
x_815 = x_814;
if (lean::is_scalar(x_804)) {
 x_816 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_816 = x_804;
}
lean::cnstr_set(x_816, 0, x_813);
lean::cnstr_set(x_816, 1, x_1);
lean::cnstr_set(x_816, 2, x_2);
lean::cnstr_set(x_816, 3, x_815);
lean::cnstr_set_scalar(x_816, sizeof(void*)*4, x_760);
x_817 = x_816;
return x_817;
}
else
{
uint8 x_818; 
x_818 = lean::cnstr_get_scalar<uint8>(x_798, sizeof(void*)*4);
if (x_818 == 0)
{
obj* x_819; obj* x_821; obj* x_823; obj* x_824; obj* x_826; obj* x_828; obj* x_829; obj* x_831; obj* x_833; obj* x_835; obj* x_837; obj* x_839; obj* x_840; obj* x_841; obj* x_842; obj* x_843; obj* x_844; obj* x_845; obj* x_846; obj* x_847; 
x_819 = lean::cnstr_get(x_0, 1);
x_821 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_823 = x_0;
} else {
 lean::inc(x_819);
 lean::inc(x_821);
 lean::dec(x_0);
 x_823 = lean::box(0);
}
x_824 = lean::cnstr_get(x_3, 1);
x_826 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_828 = x_3;
} else {
 lean::inc(x_824);
 lean::inc(x_826);
 lean::dec(x_3);
 x_828 = lean::box(0);
}
x_829 = lean::cnstr_get(x_798, 0);
x_831 = lean::cnstr_get(x_798, 1);
x_833 = lean::cnstr_get(x_798, 2);
x_835 = lean::cnstr_get(x_798, 3);
if (lean::is_exclusive(x_798)) {
 x_837 = x_798;
} else {
 lean::inc(x_829);
 lean::inc(x_831);
 lean::inc(x_833);
 lean::inc(x_835);
 lean::dec(x_798);
 x_837 = lean::box(0);
}
lean::inc(x_175);
if (lean::is_scalar(x_837)) {
 x_839 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_839 = x_837;
}
lean::cnstr_set(x_839, 0, x_175);
lean::cnstr_set(x_839, 1, x_819);
lean::cnstr_set(x_839, 2, x_821);
lean::cnstr_set(x_839, 3, x_796);
if (lean::is_exclusive(x_175)) {
 lean::cnstr_release(x_175, 0);
 lean::cnstr_release(x_175, 1);
 lean::cnstr_release(x_175, 2);
 lean::cnstr_release(x_175, 3);
 x_840 = x_175;
} else {
 lean::dec(x_175);
 x_840 = lean::box(0);
}
lean::cnstr_set_scalar(x_839, sizeof(void*)*4, x_818);
x_841 = x_839;
if (lean::is_scalar(x_828)) {
 x_842 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_842 = x_828;
}
lean::cnstr_set(x_842, 0, x_841);
lean::cnstr_set(x_842, 1, x_1);
lean::cnstr_set(x_842, 2, x_2);
lean::cnstr_set(x_842, 3, x_796);
lean::cnstr_set_scalar(x_842, sizeof(void*)*4, x_760);
x_843 = x_842;
if (lean::is_scalar(x_840)) {
 x_844 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_844 = x_840;
}
lean::cnstr_set(x_844, 0, x_829);
lean::cnstr_set(x_844, 1, x_831);
lean::cnstr_set(x_844, 2, x_833);
lean::cnstr_set(x_844, 3, x_835);
lean::cnstr_set_scalar(x_844, sizeof(void*)*4, x_760);
x_845 = x_844;
if (lean::is_scalar(x_823)) {
 x_846 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_846 = x_823;
}
lean::cnstr_set(x_846, 0, x_843);
lean::cnstr_set(x_846, 1, x_824);
lean::cnstr_set(x_846, 2, x_826);
lean::cnstr_set(x_846, 3, x_845);
lean::cnstr_set_scalar(x_846, sizeof(void*)*4, x_818);
x_847 = x_846;
return x_847;
}
else
{
obj* x_848; obj* x_849; obj* x_851; obj* x_853; obj* x_854; obj* x_856; obj* x_858; obj* x_860; obj* x_862; obj* x_863; obj* x_864; obj* x_865; obj* x_866; obj* x_867; obj* x_868; 
if (lean::is_exclusive(x_798)) {
 lean::cnstr_release(x_798, 0);
 lean::cnstr_release(x_798, 1);
 lean::cnstr_release(x_798, 2);
 lean::cnstr_release(x_798, 3);
 x_848 = x_798;
} else {
 lean::dec(x_798);
 x_848 = lean::box(0);
}
x_849 = lean::cnstr_get(x_0, 1);
x_851 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_853 = x_0;
} else {
 lean::inc(x_849);
 lean::inc(x_851);
 lean::dec(x_0);
 x_853 = lean::box(0);
}
x_854 = lean::cnstr_get(x_175, 0);
x_856 = lean::cnstr_get(x_175, 1);
x_858 = lean::cnstr_get(x_175, 2);
x_860 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_862 = x_175;
} else {
 lean::inc(x_854);
 lean::inc(x_856);
 lean::inc(x_858);
 lean::inc(x_860);
 lean::dec(x_175);
 x_862 = lean::box(0);
}
if (lean::is_scalar(x_848)) {
 x_863 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_863 = x_848;
}
lean::cnstr_set(x_863, 0, x_854);
lean::cnstr_set(x_863, 1, x_856);
lean::cnstr_set(x_863, 2, x_858);
lean::cnstr_set(x_863, 3, x_860);
lean::cnstr_set_scalar(x_863, sizeof(void*)*4, x_818);
x_864 = x_863;
if (lean::is_scalar(x_862)) {
 x_865 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_865 = x_862;
}
lean::cnstr_set(x_865, 0, x_864);
lean::cnstr_set(x_865, 1, x_849);
lean::cnstr_set(x_865, 2, x_851);
lean::cnstr_set(x_865, 3, x_796);
lean::cnstr_set_scalar(x_865, sizeof(void*)*4, x_795);
x_866 = x_865;
if (lean::is_scalar(x_853)) {
 x_867 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_867 = x_853;
}
lean::cnstr_set(x_867, 0, x_866);
lean::cnstr_set(x_867, 1, x_1);
lean::cnstr_set(x_867, 2, x_2);
lean::cnstr_set(x_867, 3, x_3);
lean::cnstr_set_scalar(x_867, sizeof(void*)*4, x_818);
x_868 = x_867;
return x_868;
}
}
}
else
{
uint8 x_869; 
x_869 = lean::cnstr_get_scalar<uint8>(x_796, sizeof(void*)*4);
if (x_869 == 0)
{
obj* x_870; 
x_870 = lean::cnstr_get(x_3, 3);
lean::inc(x_870);
if (lean::obj_tag(x_870) == 0)
{
obj* x_872; obj* x_874; obj* x_876; obj* x_877; obj* x_879; obj* x_881; obj* x_882; obj* x_884; obj* x_886; obj* x_888; obj* x_890; obj* x_892; obj* x_893; obj* x_894; obj* x_895; obj* x_896; obj* x_897; obj* x_898; obj* x_899; obj* x_900; 
x_872 = lean::cnstr_get(x_0, 1);
x_874 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_876 = x_0;
} else {
 lean::inc(x_872);
 lean::inc(x_874);
 lean::dec(x_0);
 x_876 = lean::box(0);
}
x_877 = lean::cnstr_get(x_3, 1);
x_879 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_881 = x_3;
} else {
 lean::inc(x_877);
 lean::inc(x_879);
 lean::dec(x_3);
 x_881 = lean::box(0);
}
x_882 = lean::cnstr_get(x_796, 0);
x_884 = lean::cnstr_get(x_796, 1);
x_886 = lean::cnstr_get(x_796, 2);
x_888 = lean::cnstr_get(x_796, 3);
if (lean::is_exclusive(x_796)) {
 x_890 = x_796;
} else {
 lean::inc(x_882);
 lean::inc(x_884);
 lean::inc(x_886);
 lean::inc(x_888);
 lean::dec(x_796);
 x_890 = lean::box(0);
}
lean::inc(x_175);
if (lean::is_scalar(x_890)) {
 x_892 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_892 = x_890;
}
lean::cnstr_set(x_892, 0, x_175);
lean::cnstr_set(x_892, 1, x_872);
lean::cnstr_set(x_892, 2, x_874);
lean::cnstr_set(x_892, 3, x_870);
if (lean::is_exclusive(x_175)) {
 lean::cnstr_release(x_175, 0);
 lean::cnstr_release(x_175, 1);
 lean::cnstr_release(x_175, 2);
 lean::cnstr_release(x_175, 3);
 x_893 = x_175;
} else {
 lean::dec(x_175);
 x_893 = lean::box(0);
}
lean::cnstr_set_scalar(x_892, sizeof(void*)*4, x_869);
x_894 = x_892;
if (lean::is_scalar(x_881)) {
 x_895 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_895 = x_881;
}
lean::cnstr_set(x_895, 0, x_894);
lean::cnstr_set(x_895, 1, x_1);
lean::cnstr_set(x_895, 2, x_2);
lean::cnstr_set(x_895, 3, x_882);
lean::cnstr_set_scalar(x_895, sizeof(void*)*4, x_760);
x_896 = x_895;
if (lean::is_scalar(x_893)) {
 x_897 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_897 = x_893;
}
lean::cnstr_set(x_897, 0, x_888);
lean::cnstr_set(x_897, 1, x_877);
lean::cnstr_set(x_897, 2, x_879);
lean::cnstr_set(x_897, 3, x_870);
lean::cnstr_set_scalar(x_897, sizeof(void*)*4, x_760);
x_898 = x_897;
if (lean::is_scalar(x_876)) {
 x_899 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_899 = x_876;
}
lean::cnstr_set(x_899, 0, x_896);
lean::cnstr_set(x_899, 1, x_884);
lean::cnstr_set(x_899, 2, x_886);
lean::cnstr_set(x_899, 3, x_898);
lean::cnstr_set_scalar(x_899, sizeof(void*)*4, x_869);
x_900 = x_899;
return x_900;
}
else
{
uint8 x_901; 
x_901 = lean::cnstr_get_scalar<uint8>(x_870, sizeof(void*)*4);
if (x_901 == 0)
{
obj* x_902; obj* x_904; obj* x_906; obj* x_907; obj* x_909; obj* x_911; obj* x_912; obj* x_914; obj* x_916; obj* x_918; obj* x_920; obj* x_921; obj* x_923; obj* x_925; obj* x_927; obj* x_929; obj* x_931; obj* x_932; obj* x_933; obj* x_934; obj* x_935; obj* x_936; obj* x_937; obj* x_938; obj* x_939; obj* x_940; obj* x_941; 
x_902 = lean::cnstr_get(x_0, 1);
x_904 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_906 = x_0;
} else {
 lean::inc(x_902);
 lean::inc(x_904);
 lean::dec(x_0);
 x_906 = lean::box(0);
}
x_907 = lean::cnstr_get(x_3, 1);
x_909 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_911 = x_3;
} else {
 lean::inc(x_907);
 lean::inc(x_909);
 lean::dec(x_3);
 x_911 = lean::box(0);
}
x_912 = lean::cnstr_get(x_796, 0);
x_914 = lean::cnstr_get(x_796, 1);
x_916 = lean::cnstr_get(x_796, 2);
x_918 = lean::cnstr_get(x_796, 3);
if (lean::is_exclusive(x_796)) {
 x_920 = x_796;
} else {
 lean::inc(x_912);
 lean::inc(x_914);
 lean::inc(x_916);
 lean::inc(x_918);
 lean::dec(x_796);
 x_920 = lean::box(0);
}
x_921 = lean::cnstr_get(x_870, 0);
x_923 = lean::cnstr_get(x_870, 1);
x_925 = lean::cnstr_get(x_870, 2);
x_927 = lean::cnstr_get(x_870, 3);
if (lean::is_exclusive(x_870)) {
 x_929 = x_870;
} else {
 lean::inc(x_921);
 lean::inc(x_923);
 lean::inc(x_925);
 lean::inc(x_927);
 lean::dec(x_870);
 x_929 = lean::box(0);
}
lean::inc(x_175);
if (lean::is_scalar(x_929)) {
 x_931 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_931 = x_929;
}
lean::cnstr_set(x_931, 0, x_175);
lean::cnstr_set(x_931, 1, x_902);
lean::cnstr_set(x_931, 2, x_904);
lean::cnstr_set(x_931, 3, x_784);
if (lean::is_exclusive(x_175)) {
 lean::cnstr_release(x_175, 0);
 lean::cnstr_release(x_175, 1);
 lean::cnstr_release(x_175, 2);
 lean::cnstr_release(x_175, 3);
 x_932 = x_175;
} else {
 lean::dec(x_175);
 x_932 = lean::box(0);
}
lean::cnstr_set_scalar(x_931, sizeof(void*)*4, x_901);
x_933 = x_931;
if (lean::is_scalar(x_920)) {
 x_934 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_934 = x_920;
}
lean::cnstr_set(x_934, 0, x_912);
lean::cnstr_set(x_934, 1, x_914);
lean::cnstr_set(x_934, 2, x_916);
lean::cnstr_set(x_934, 3, x_918);
lean::cnstr_set_scalar(x_934, sizeof(void*)*4, x_901);
x_935 = x_934;
if (lean::is_scalar(x_911)) {
 x_936 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_936 = x_911;
}
lean::cnstr_set(x_936, 0, x_933);
lean::cnstr_set(x_936, 1, x_1);
lean::cnstr_set(x_936, 2, x_2);
lean::cnstr_set(x_936, 3, x_935);
lean::cnstr_set_scalar(x_936, sizeof(void*)*4, x_760);
x_937 = x_936;
if (lean::is_scalar(x_932)) {
 x_938 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_938 = x_932;
}
lean::cnstr_set(x_938, 0, x_921);
lean::cnstr_set(x_938, 1, x_923);
lean::cnstr_set(x_938, 2, x_925);
lean::cnstr_set(x_938, 3, x_927);
lean::cnstr_set_scalar(x_938, sizeof(void*)*4, x_760);
x_939 = x_938;
if (lean::is_scalar(x_906)) {
 x_940 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_940 = x_906;
}
lean::cnstr_set(x_940, 0, x_937);
lean::cnstr_set(x_940, 1, x_907);
lean::cnstr_set(x_940, 2, x_909);
lean::cnstr_set(x_940, 3, x_939);
lean::cnstr_set_scalar(x_940, sizeof(void*)*4, x_901);
x_941 = x_940;
return x_941;
}
else
{
obj* x_942; obj* x_944; obj* x_946; obj* x_947; obj* x_949; obj* x_951; obj* x_953; obj* x_955; obj* x_956; obj* x_958; obj* x_960; obj* x_961; obj* x_963; obj* x_965; obj* x_967; obj* x_969; obj* x_970; obj* x_971; obj* x_972; obj* x_973; obj* x_974; obj* x_975; obj* x_976; obj* x_977; obj* x_978; obj* x_979; 
x_942 = lean::cnstr_get(x_0, 1);
x_944 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_946 = x_0;
} else {
 lean::inc(x_942);
 lean::inc(x_944);
 lean::dec(x_0);
 x_946 = lean::box(0);
}
x_947 = lean::cnstr_get(x_175, 0);
x_949 = lean::cnstr_get(x_175, 1);
x_951 = lean::cnstr_get(x_175, 2);
x_953 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_955 = x_175;
} else {
 lean::inc(x_947);
 lean::inc(x_949);
 lean::inc(x_951);
 lean::inc(x_953);
 lean::dec(x_175);
 x_955 = lean::box(0);
}
x_956 = lean::cnstr_get(x_3, 1);
x_958 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_960 = x_3;
} else {
 lean::inc(x_956);
 lean::inc(x_958);
 lean::dec(x_3);
 x_960 = lean::box(0);
}
x_961 = lean::cnstr_get(x_796, 0);
x_963 = lean::cnstr_get(x_796, 1);
x_965 = lean::cnstr_get(x_796, 2);
x_967 = lean::cnstr_get(x_796, 3);
if (lean::is_exclusive(x_796)) {
 x_969 = x_796;
} else {
 lean::inc(x_961);
 lean::inc(x_963);
 lean::inc(x_965);
 lean::inc(x_967);
 lean::dec(x_796);
 x_969 = lean::box(0);
}
if (lean::is_scalar(x_969)) {
 x_970 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_970 = x_969;
}
lean::cnstr_set(x_970, 0, x_947);
lean::cnstr_set(x_970, 1, x_949);
lean::cnstr_set(x_970, 2, x_951);
lean::cnstr_set(x_970, 3, x_953);
lean::cnstr_set_scalar(x_970, sizeof(void*)*4, x_901);
x_971 = x_970;
if (lean::is_scalar(x_960)) {
 x_972 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_972 = x_960;
}
lean::cnstr_set(x_972, 0, x_971);
lean::cnstr_set(x_972, 1, x_942);
lean::cnstr_set(x_972, 2, x_944);
lean::cnstr_set(x_972, 3, x_784);
lean::cnstr_set_scalar(x_972, sizeof(void*)*4, x_869);
x_973 = x_972;
if (lean::is_scalar(x_955)) {
 x_974 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_974 = x_955;
}
lean::cnstr_set(x_974, 0, x_973);
lean::cnstr_set(x_974, 1, x_1);
lean::cnstr_set(x_974, 2, x_2);
lean::cnstr_set(x_974, 3, x_961);
lean::cnstr_set_scalar(x_974, sizeof(void*)*4, x_901);
x_975 = x_974;
if (lean::is_scalar(x_946)) {
 x_976 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_976 = x_946;
}
lean::cnstr_set(x_976, 0, x_967);
lean::cnstr_set(x_976, 1, x_956);
lean::cnstr_set(x_976, 2, x_958);
lean::cnstr_set(x_976, 3, x_870);
lean::cnstr_set_scalar(x_976, sizeof(void*)*4, x_901);
x_977 = x_976;
x_978 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_978, 0, x_975);
lean::cnstr_set(x_978, 1, x_963);
lean::cnstr_set(x_978, 2, x_965);
lean::cnstr_set(x_978, 3, x_977);
lean::cnstr_set_scalar(x_978, sizeof(void*)*4, x_869);
x_979 = x_978;
return x_979;
}
}
}
else
{
obj* x_980; 
x_980 = lean::cnstr_get(x_3, 3);
lean::inc(x_980);
if (lean::obj_tag(x_980) == 0)
{
obj* x_982; obj* x_983; obj* x_985; obj* x_987; obj* x_988; obj* x_990; obj* x_992; obj* x_994; obj* x_996; obj* x_997; obj* x_998; obj* x_999; obj* x_1000; obj* x_1001; obj* x_1002; 
if (lean::is_exclusive(x_796)) {
 lean::cnstr_release(x_796, 0);
 lean::cnstr_release(x_796, 1);
 lean::cnstr_release(x_796, 2);
 lean::cnstr_release(x_796, 3);
 x_982 = x_796;
} else {
 lean::dec(x_796);
 x_982 = lean::box(0);
}
x_983 = lean::cnstr_get(x_0, 1);
x_985 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_987 = x_0;
} else {
 lean::inc(x_983);
 lean::inc(x_985);
 lean::dec(x_0);
 x_987 = lean::box(0);
}
x_988 = lean::cnstr_get(x_175, 0);
x_990 = lean::cnstr_get(x_175, 1);
x_992 = lean::cnstr_get(x_175, 2);
x_994 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_996 = x_175;
} else {
 lean::inc(x_988);
 lean::inc(x_990);
 lean::inc(x_992);
 lean::inc(x_994);
 lean::dec(x_175);
 x_996 = lean::box(0);
}
if (lean::is_scalar(x_982)) {
 x_997 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_997 = x_982;
}
lean::cnstr_set(x_997, 0, x_988);
lean::cnstr_set(x_997, 1, x_990);
lean::cnstr_set(x_997, 2, x_992);
lean::cnstr_set(x_997, 3, x_994);
lean::cnstr_set_scalar(x_997, sizeof(void*)*4, x_869);
x_998 = x_997;
if (lean::is_scalar(x_996)) {
 x_999 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_999 = x_996;
}
lean::cnstr_set(x_999, 0, x_998);
lean::cnstr_set(x_999, 1, x_983);
lean::cnstr_set(x_999, 2, x_985);
lean::cnstr_set(x_999, 3, x_980);
lean::cnstr_set_scalar(x_999, sizeof(void*)*4, x_795);
x_1000 = x_999;
if (lean::is_scalar(x_987)) {
 x_1001 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1001 = x_987;
}
lean::cnstr_set(x_1001, 0, x_1000);
lean::cnstr_set(x_1001, 1, x_1);
lean::cnstr_set(x_1001, 2, x_2);
lean::cnstr_set(x_1001, 3, x_3);
lean::cnstr_set_scalar(x_1001, sizeof(void*)*4, x_869);
x_1002 = x_1001;
return x_1002;
}
else
{
uint8 x_1003; 
x_1003 = lean::cnstr_get_scalar<uint8>(x_980, sizeof(void*)*4);
if (x_1003 == 0)
{
obj* x_1004; obj* x_1006; obj* x_1008; obj* x_1009; obj* x_1011; obj* x_1013; obj* x_1015; obj* x_1017; obj* x_1018; obj* x_1020; obj* x_1022; obj* x_1023; obj* x_1025; obj* x_1027; obj* x_1029; obj* x_1031; obj* x_1032; obj* x_1033; obj* x_1034; obj* x_1035; obj* x_1036; obj* x_1037; obj* x_1038; obj* x_1039; obj* x_1040; obj* x_1041; 
x_1004 = lean::cnstr_get(x_0, 1);
x_1006 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_1008 = x_0;
} else {
 lean::inc(x_1004);
 lean::inc(x_1006);
 lean::dec(x_0);
 x_1008 = lean::box(0);
}
x_1009 = lean::cnstr_get(x_175, 0);
x_1011 = lean::cnstr_get(x_175, 1);
x_1013 = lean::cnstr_get(x_175, 2);
x_1015 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_1017 = x_175;
} else {
 lean::inc(x_1009);
 lean::inc(x_1011);
 lean::inc(x_1013);
 lean::inc(x_1015);
 lean::dec(x_175);
 x_1017 = lean::box(0);
}
x_1018 = lean::cnstr_get(x_3, 1);
x_1020 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1022 = x_3;
} else {
 lean::inc(x_1018);
 lean::inc(x_1020);
 lean::dec(x_3);
 x_1022 = lean::box(0);
}
x_1023 = lean::cnstr_get(x_980, 0);
x_1025 = lean::cnstr_get(x_980, 1);
x_1027 = lean::cnstr_get(x_980, 2);
x_1029 = lean::cnstr_get(x_980, 3);
if (lean::is_exclusive(x_980)) {
 x_1031 = x_980;
} else {
 lean::inc(x_1023);
 lean::inc(x_1025);
 lean::inc(x_1027);
 lean::inc(x_1029);
 lean::dec(x_980);
 x_1031 = lean::box(0);
}
if (lean::is_scalar(x_1031)) {
 x_1032 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1032 = x_1031;
}
lean::cnstr_set(x_1032, 0, x_1009);
lean::cnstr_set(x_1032, 1, x_1011);
lean::cnstr_set(x_1032, 2, x_1013);
lean::cnstr_set(x_1032, 3, x_1015);
lean::cnstr_set_scalar(x_1032, sizeof(void*)*4, x_869);
x_1033 = x_1032;
if (lean::is_scalar(x_1022)) {
 x_1034 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1034 = x_1022;
}
lean::cnstr_set(x_1034, 0, x_1033);
lean::cnstr_set(x_1034, 1, x_1004);
lean::cnstr_set(x_1034, 2, x_1006);
lean::cnstr_set(x_1034, 3, x_784);
lean::cnstr_set_scalar(x_1034, sizeof(void*)*4, x_1003);
x_1035 = x_1034;
if (lean::is_scalar(x_1017)) {
 x_1036 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1036 = x_1017;
}
lean::cnstr_set(x_1036, 0, x_1035);
lean::cnstr_set(x_1036, 1, x_1);
lean::cnstr_set(x_1036, 2, x_2);
lean::cnstr_set(x_1036, 3, x_796);
lean::cnstr_set_scalar(x_1036, sizeof(void*)*4, x_869);
x_1037 = x_1036;
if (lean::is_scalar(x_1008)) {
 x_1038 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1038 = x_1008;
}
lean::cnstr_set(x_1038, 0, x_1023);
lean::cnstr_set(x_1038, 1, x_1025);
lean::cnstr_set(x_1038, 2, x_1027);
lean::cnstr_set(x_1038, 3, x_1029);
lean::cnstr_set_scalar(x_1038, sizeof(void*)*4, x_869);
x_1039 = x_1038;
x_1040 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1040, 0, x_1037);
lean::cnstr_set(x_1040, 1, x_1018);
lean::cnstr_set(x_1040, 2, x_1020);
lean::cnstr_set(x_1040, 3, x_1039);
lean::cnstr_set_scalar(x_1040, sizeof(void*)*4, x_1003);
x_1041 = x_1040;
return x_1041;
}
else
{
obj* x_1042; obj* x_1044; obj* x_1046; obj* x_1047; obj* x_1049; obj* x_1051; obj* x_1053; obj* x_1055; obj* x_1056; obj* x_1058; obj* x_1060; obj* x_1061; obj* x_1063; obj* x_1065; obj* x_1067; obj* x_1069; obj* x_1070; obj* x_1071; obj* x_1072; obj* x_1073; obj* x_1074; obj* x_1075; obj* x_1076; obj* x_1077; obj* x_1078; obj* x_1079; 
x_1042 = lean::cnstr_get(x_0, 1);
x_1044 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_1046 = x_0;
} else {
 lean::inc(x_1042);
 lean::inc(x_1044);
 lean::dec(x_0);
 x_1046 = lean::box(0);
}
x_1047 = lean::cnstr_get(x_175, 0);
x_1049 = lean::cnstr_get(x_175, 1);
x_1051 = lean::cnstr_get(x_175, 2);
x_1053 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_1055 = x_175;
} else {
 lean::inc(x_1047);
 lean::inc(x_1049);
 lean::inc(x_1051);
 lean::inc(x_1053);
 lean::dec(x_175);
 x_1055 = lean::box(0);
}
x_1056 = lean::cnstr_get(x_3, 1);
x_1058 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1060 = x_3;
} else {
 lean::inc(x_1056);
 lean::inc(x_1058);
 lean::dec(x_3);
 x_1060 = lean::box(0);
}
x_1061 = lean::cnstr_get(x_796, 0);
x_1063 = lean::cnstr_get(x_796, 1);
x_1065 = lean::cnstr_get(x_796, 2);
x_1067 = lean::cnstr_get(x_796, 3);
if (lean::is_exclusive(x_796)) {
 x_1069 = x_796;
} else {
 lean::inc(x_1061);
 lean::inc(x_1063);
 lean::inc(x_1065);
 lean::inc(x_1067);
 lean::dec(x_796);
 x_1069 = lean::box(0);
}
if (lean::is_scalar(x_1069)) {
 x_1070 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1070 = x_1069;
}
lean::cnstr_set(x_1070, 0, x_1047);
lean::cnstr_set(x_1070, 1, x_1049);
lean::cnstr_set(x_1070, 2, x_1051);
lean::cnstr_set(x_1070, 3, x_1053);
lean::cnstr_set_scalar(x_1070, sizeof(void*)*4, x_1003);
x_1071 = x_1070;
if (lean::is_scalar(x_1060)) {
 x_1072 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1072 = x_1060;
}
lean::cnstr_set(x_1072, 0, x_1071);
lean::cnstr_set(x_1072, 1, x_1042);
lean::cnstr_set(x_1072, 2, x_1044);
lean::cnstr_set(x_1072, 3, x_784);
lean::cnstr_set_scalar(x_1072, sizeof(void*)*4, x_795);
x_1073 = x_1072;
if (lean::is_scalar(x_1055)) {
 x_1074 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1074 = x_1055;
}
lean::cnstr_set(x_1074, 0, x_1061);
lean::cnstr_set(x_1074, 1, x_1063);
lean::cnstr_set(x_1074, 2, x_1065);
lean::cnstr_set(x_1074, 3, x_1067);
lean::cnstr_set_scalar(x_1074, sizeof(void*)*4, x_1003);
x_1075 = x_1074;
if (lean::is_scalar(x_1046)) {
 x_1076 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1076 = x_1046;
}
lean::cnstr_set(x_1076, 0, x_1075);
lean::cnstr_set(x_1076, 1, x_1056);
lean::cnstr_set(x_1076, 2, x_1058);
lean::cnstr_set(x_1076, 3, x_980);
lean::cnstr_set_scalar(x_1076, sizeof(void*)*4, x_795);
x_1077 = x_1076;
x_1078 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1078, 0, x_1073);
lean::cnstr_set(x_1078, 1, x_1);
lean::cnstr_set(x_1078, 2, x_2);
lean::cnstr_set(x_1078, 3, x_1077);
lean::cnstr_set_scalar(x_1078, sizeof(void*)*4, x_1003);
x_1079 = x_1078;
return x_1079;
}
}
}
}
}
else
{
obj* x_1080; obj* x_1082; obj* x_1084; obj* x_1085; obj* x_1087; obj* x_1089; obj* x_1091; obj* x_1093; obj* x_1094; obj* x_1095; obj* x_1096; obj* x_1097; obj* x_1098; obj* x_1099; 
x_1080 = lean::cnstr_get(x_0, 1);
x_1082 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_1084 = x_0;
} else {
 lean::inc(x_1080);
 lean::inc(x_1082);
 lean::dec(x_0);
 x_1084 = lean::box(0);
}
x_1085 = lean::cnstr_get(x_175, 0);
x_1087 = lean::cnstr_get(x_175, 1);
x_1089 = lean::cnstr_get(x_175, 2);
x_1091 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_1093 = x_175;
} else {
 lean::inc(x_1085);
 lean::inc(x_1087);
 lean::inc(x_1089);
 lean::inc(x_1091);
 lean::dec(x_175);
 x_1093 = lean::box(0);
}
if (lean::is_scalar(x_1093)) {
 x_1094 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1094 = x_1093;
}
lean::cnstr_set(x_1094, 0, x_1085);
lean::cnstr_set(x_1094, 1, x_1087);
lean::cnstr_set(x_1094, 2, x_1089);
lean::cnstr_set(x_1094, 3, x_1091);
lean::cnstr_set_scalar(x_1094, sizeof(void*)*4, x_795);
x_1095 = x_1094;
if (lean::is_scalar(x_1084)) {
 x_1096 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1096 = x_1084;
}
lean::cnstr_set(x_1096, 0, x_1095);
lean::cnstr_set(x_1096, 1, x_1080);
lean::cnstr_set(x_1096, 2, x_1082);
lean::cnstr_set(x_1096, 3, x_784);
lean::cnstr_set_scalar(x_1096, sizeof(void*)*4, x_174);
x_1097 = x_1096;
x_1098 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1098, 0, x_1097);
lean::cnstr_set(x_1098, 1, x_1);
lean::cnstr_set(x_1098, 2, x_2);
lean::cnstr_set(x_1098, 3, x_3);
lean::cnstr_set_scalar(x_1098, sizeof(void*)*4, x_795);
x_1099 = x_1098;
return x_1099;
}
}
}
else
{
uint8 x_1100; 
x_1100 = lean::cnstr_get_scalar<uint8>(x_784, sizeof(void*)*4);
if (x_1100 == 0)
{
obj* x_1101; obj* x_1103; obj* x_1105; obj* x_1106; obj* x_1108; obj* x_1110; obj* x_1112; obj* x_1114; obj* x_1116; obj* x_1117; obj* x_1118; obj* x_1119; obj* x_1120; obj* x_1121; obj* x_1122; 
x_1101 = lean::cnstr_get(x_0, 1);
x_1103 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_1105 = x_0;
} else {
 lean::inc(x_1101);
 lean::inc(x_1103);
 lean::dec(x_0);
 x_1105 = lean::box(0);
}
x_1106 = lean::cnstr_get(x_784, 0);
x_1108 = lean::cnstr_get(x_784, 1);
x_1110 = lean::cnstr_get(x_784, 2);
x_1112 = lean::cnstr_get(x_784, 3);
if (lean::is_exclusive(x_784)) {
 x_1114 = x_784;
} else {
 lean::inc(x_1106);
 lean::inc(x_1108);
 lean::inc(x_1110);
 lean::inc(x_1112);
 lean::dec(x_784);
 x_1114 = lean::box(0);
}
lean::inc(x_175);
if (lean::is_scalar(x_1114)) {
 x_1116 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1116 = x_1114;
}
lean::cnstr_set(x_1116, 0, x_175);
lean::cnstr_set(x_1116, 1, x_1101);
lean::cnstr_set(x_1116, 2, x_1103);
lean::cnstr_set(x_1116, 3, x_1106);
if (lean::is_exclusive(x_175)) {
 lean::cnstr_release(x_175, 0);
 lean::cnstr_release(x_175, 1);
 lean::cnstr_release(x_175, 2);
 lean::cnstr_release(x_175, 3);
 x_1117 = x_175;
} else {
 lean::dec(x_175);
 x_1117 = lean::box(0);
}
lean::cnstr_set_scalar(x_1116, sizeof(void*)*4, x_760);
x_1118 = x_1116;
if (lean::is_scalar(x_1117)) {
 x_1119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1119 = x_1117;
}
lean::cnstr_set(x_1119, 0, x_1112);
lean::cnstr_set(x_1119, 1, x_1);
lean::cnstr_set(x_1119, 2, x_2);
lean::cnstr_set(x_1119, 3, x_3);
lean::cnstr_set_scalar(x_1119, sizeof(void*)*4, x_760);
x_1120 = x_1119;
if (lean::is_scalar(x_1105)) {
 x_1121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1121 = x_1105;
}
lean::cnstr_set(x_1121, 0, x_1118);
lean::cnstr_set(x_1121, 1, x_1108);
lean::cnstr_set(x_1121, 2, x_1110);
lean::cnstr_set(x_1121, 3, x_1120);
lean::cnstr_set_scalar(x_1121, sizeof(void*)*4, x_1100);
x_1122 = x_1121;
return x_1122;
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_1123; obj* x_1125; obj* x_1127; obj* x_1128; obj* x_1130; obj* x_1132; obj* x_1134; obj* x_1136; obj* x_1137; obj* x_1138; obj* x_1139; obj* x_1140; obj* x_1141; obj* x_1142; 
x_1123 = lean::cnstr_get(x_0, 1);
x_1125 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_1127 = x_0;
} else {
 lean::inc(x_1123);
 lean::inc(x_1125);
 lean::dec(x_0);
 x_1127 = lean::box(0);
}
x_1128 = lean::cnstr_get(x_175, 0);
x_1130 = lean::cnstr_get(x_175, 1);
x_1132 = lean::cnstr_get(x_175, 2);
x_1134 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_1136 = x_175;
} else {
 lean::inc(x_1128);
 lean::inc(x_1130);
 lean::inc(x_1132);
 lean::inc(x_1134);
 lean::dec(x_175);
 x_1136 = lean::box(0);
}
if (lean::is_scalar(x_1136)) {
 x_1137 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1137 = x_1136;
}
lean::cnstr_set(x_1137, 0, x_1128);
lean::cnstr_set(x_1137, 1, x_1130);
lean::cnstr_set(x_1137, 2, x_1132);
lean::cnstr_set(x_1137, 3, x_1134);
lean::cnstr_set_scalar(x_1137, sizeof(void*)*4, x_1100);
x_1138 = x_1137;
if (lean::is_scalar(x_1127)) {
 x_1139 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1139 = x_1127;
}
lean::cnstr_set(x_1139, 0, x_1138);
lean::cnstr_set(x_1139, 1, x_1123);
lean::cnstr_set(x_1139, 2, x_1125);
lean::cnstr_set(x_1139, 3, x_784);
lean::cnstr_set_scalar(x_1139, sizeof(void*)*4, x_174);
x_1140 = x_1139;
x_1141 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1141, 0, x_1140);
lean::cnstr_set(x_1141, 1, x_1);
lean::cnstr_set(x_1141, 2, x_2);
lean::cnstr_set(x_1141, 3, x_3);
lean::cnstr_set_scalar(x_1141, sizeof(void*)*4, x_1100);
x_1142 = x_1141;
return x_1142;
}
else
{
uint8 x_1143; 
x_1143 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*4);
if (x_1143 == 0)
{
obj* x_1144; 
x_1144 = lean::cnstr_get(x_3, 0);
lean::inc(x_1144);
if (lean::obj_tag(x_1144) == 0)
{
obj* x_1146; 
x_1146 = lean::cnstr_get(x_3, 3);
lean::inc(x_1146);
if (lean::obj_tag(x_1146) == 0)
{
obj* x_1148; obj* x_1150; obj* x_1152; obj* x_1153; obj* x_1155; obj* x_1157; obj* x_1159; obj* x_1161; obj* x_1162; obj* x_1164; obj* x_1166; obj* x_1167; obj* x_1168; obj* x_1169; obj* x_1170; obj* x_1171; obj* x_1172; obj* x_1173; obj* x_1174; 
x_1148 = lean::cnstr_get(x_0, 1);
x_1150 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_1152 = x_0;
} else {
 lean::inc(x_1148);
 lean::inc(x_1150);
 lean::dec(x_0);
 x_1152 = lean::box(0);
}
x_1153 = lean::cnstr_get(x_175, 0);
x_1155 = lean::cnstr_get(x_175, 1);
x_1157 = lean::cnstr_get(x_175, 2);
x_1159 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_1161 = x_175;
} else {
 lean::inc(x_1153);
 lean::inc(x_1155);
 lean::inc(x_1157);
 lean::inc(x_1159);
 lean::dec(x_175);
 x_1161 = lean::box(0);
}
x_1162 = lean::cnstr_get(x_3, 1);
x_1164 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1166 = x_3;
} else {
 lean::inc(x_1162);
 lean::inc(x_1164);
 lean::dec(x_3);
 x_1166 = lean::box(0);
}
if (lean::is_scalar(x_1166)) {
 x_1167 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1167 = x_1166;
}
lean::cnstr_set(x_1167, 0, x_1153);
lean::cnstr_set(x_1167, 1, x_1155);
lean::cnstr_set(x_1167, 2, x_1157);
lean::cnstr_set(x_1167, 3, x_1159);
lean::cnstr_set_scalar(x_1167, sizeof(void*)*4, x_1100);
x_1168 = x_1167;
if (lean::is_scalar(x_1161)) {
 x_1169 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1169 = x_1161;
}
lean::cnstr_set(x_1169, 0, x_1168);
lean::cnstr_set(x_1169, 1, x_1148);
lean::cnstr_set(x_1169, 2, x_1150);
lean::cnstr_set(x_1169, 3, x_784);
lean::cnstr_set_scalar(x_1169, sizeof(void*)*4, x_1143);
x_1170 = x_1169;
if (lean::is_scalar(x_1152)) {
 x_1171 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1171 = x_1152;
}
lean::cnstr_set(x_1171, 0, x_1146);
lean::cnstr_set(x_1171, 1, x_1162);
lean::cnstr_set(x_1171, 2, x_1164);
lean::cnstr_set(x_1171, 3, x_1146);
lean::cnstr_set_scalar(x_1171, sizeof(void*)*4, x_1143);
x_1172 = x_1171;
x_1173 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1173, 0, x_1170);
lean::cnstr_set(x_1173, 1, x_1);
lean::cnstr_set(x_1173, 2, x_2);
lean::cnstr_set(x_1173, 3, x_1172);
lean::cnstr_set_scalar(x_1173, sizeof(void*)*4, x_1100);
x_1174 = x_1173;
return x_1174;
}
else
{
uint8 x_1175; 
x_1175 = lean::cnstr_get_scalar<uint8>(x_1146, sizeof(void*)*4);
if (x_1175 == 0)
{
obj* x_1176; obj* x_1178; obj* x_1180; obj* x_1181; obj* x_1183; obj* x_1185; obj* x_1187; obj* x_1189; obj* x_1190; obj* x_1192; obj* x_1194; obj* x_1195; obj* x_1197; obj* x_1199; obj* x_1201; obj* x_1203; obj* x_1204; obj* x_1205; obj* x_1207; obj* x_1208; obj* x_1209; obj* x_1210; obj* x_1211; obj* x_1212; obj* x_1213; obj* x_1214; obj* x_1215; 
x_1176 = lean::cnstr_get(x_0, 1);
x_1178 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_1180 = x_0;
} else {
 lean::inc(x_1176);
 lean::inc(x_1178);
 lean::dec(x_0);
 x_1180 = lean::box(0);
}
x_1181 = lean::cnstr_get(x_175, 0);
x_1183 = lean::cnstr_get(x_175, 1);
x_1185 = lean::cnstr_get(x_175, 2);
x_1187 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_1189 = x_175;
} else {
 lean::inc(x_1181);
 lean::inc(x_1183);
 lean::inc(x_1185);
 lean::inc(x_1187);
 lean::dec(x_175);
 x_1189 = lean::box(0);
}
x_1190 = lean::cnstr_get(x_3, 1);
x_1192 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1194 = x_3;
} else {
 lean::inc(x_1190);
 lean::inc(x_1192);
 lean::dec(x_3);
 x_1194 = lean::box(0);
}
x_1195 = lean::cnstr_get(x_1146, 0);
x_1197 = lean::cnstr_get(x_1146, 1);
x_1199 = lean::cnstr_get(x_1146, 2);
x_1201 = lean::cnstr_get(x_1146, 3);
if (lean::is_exclusive(x_1146)) {
 x_1203 = x_1146;
} else {
 lean::inc(x_1195);
 lean::inc(x_1197);
 lean::inc(x_1199);
 lean::inc(x_1201);
 lean::dec(x_1146);
 x_1203 = lean::box(0);
}
if (lean::is_scalar(x_1203)) {
 x_1204 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1204 = x_1203;
}
lean::cnstr_set(x_1204, 0, x_1181);
lean::cnstr_set(x_1204, 1, x_1183);
lean::cnstr_set(x_1204, 2, x_1185);
lean::cnstr_set(x_1204, 3, x_1187);
lean::cnstr_set_scalar(x_1204, sizeof(void*)*4, x_1100);
x_1205 = x_1204;
lean::inc(x_784);
if (lean::is_scalar(x_1194)) {
 x_1207 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1207 = x_1194;
}
lean::cnstr_set(x_1207, 0, x_1205);
lean::cnstr_set(x_1207, 1, x_1176);
lean::cnstr_set(x_1207, 2, x_1178);
lean::cnstr_set(x_1207, 3, x_784);
if (lean::is_exclusive(x_784)) {
 lean::cnstr_release(x_784, 0);
 lean::cnstr_release(x_784, 1);
 lean::cnstr_release(x_784, 2);
 lean::cnstr_release(x_784, 3);
 x_1208 = x_784;
} else {
 lean::dec(x_784);
 x_1208 = lean::box(0);
}
lean::cnstr_set_scalar(x_1207, sizeof(void*)*4, x_1175);
x_1209 = x_1207;
if (lean::is_scalar(x_1208)) {
 x_1210 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1210 = x_1208;
}
lean::cnstr_set(x_1210, 0, x_1209);
lean::cnstr_set(x_1210, 1, x_1);
lean::cnstr_set(x_1210, 2, x_2);
lean::cnstr_set(x_1210, 3, x_1144);
lean::cnstr_set_scalar(x_1210, sizeof(void*)*4, x_1100);
x_1211 = x_1210;
if (lean::is_scalar(x_1189)) {
 x_1212 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1212 = x_1189;
}
lean::cnstr_set(x_1212, 0, x_1195);
lean::cnstr_set(x_1212, 1, x_1197);
lean::cnstr_set(x_1212, 2, x_1199);
lean::cnstr_set(x_1212, 3, x_1201);
lean::cnstr_set_scalar(x_1212, sizeof(void*)*4, x_1100);
x_1213 = x_1212;
if (lean::is_scalar(x_1180)) {
 x_1214 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1214 = x_1180;
}
lean::cnstr_set(x_1214, 0, x_1211);
lean::cnstr_set(x_1214, 1, x_1190);
lean::cnstr_set(x_1214, 2, x_1192);
lean::cnstr_set(x_1214, 3, x_1213);
lean::cnstr_set_scalar(x_1214, sizeof(void*)*4, x_1175);
x_1215 = x_1214;
return x_1215;
}
else
{
obj* x_1216; obj* x_1217; obj* x_1219; obj* x_1221; obj* x_1222; obj* x_1224; obj* x_1226; obj* x_1228; obj* x_1230; obj* x_1231; obj* x_1233; obj* x_1235; obj* x_1237; obj* x_1239; obj* x_1240; obj* x_1241; obj* x_1242; obj* x_1243; obj* x_1244; obj* x_1245; obj* x_1246; obj* x_1247; 
if (lean::is_exclusive(x_1146)) {
 lean::cnstr_release(x_1146, 0);
 lean::cnstr_release(x_1146, 1);
 lean::cnstr_release(x_1146, 2);
 lean::cnstr_release(x_1146, 3);
 x_1216 = x_1146;
} else {
 lean::dec(x_1146);
 x_1216 = lean::box(0);
}
x_1217 = lean::cnstr_get(x_0, 1);
x_1219 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_1221 = x_0;
} else {
 lean::inc(x_1217);
 lean::inc(x_1219);
 lean::dec(x_0);
 x_1221 = lean::box(0);
}
x_1222 = lean::cnstr_get(x_175, 0);
x_1224 = lean::cnstr_get(x_175, 1);
x_1226 = lean::cnstr_get(x_175, 2);
x_1228 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_1230 = x_175;
} else {
 lean::inc(x_1222);
 lean::inc(x_1224);
 lean::inc(x_1226);
 lean::inc(x_1228);
 lean::dec(x_175);
 x_1230 = lean::box(0);
}
x_1231 = lean::cnstr_get(x_784, 0);
x_1233 = lean::cnstr_get(x_784, 1);
x_1235 = lean::cnstr_get(x_784, 2);
x_1237 = lean::cnstr_get(x_784, 3);
if (lean::is_exclusive(x_784)) {
 x_1239 = x_784;
} else {
 lean::inc(x_1231);
 lean::inc(x_1233);
 lean::inc(x_1235);
 lean::inc(x_1237);
 lean::dec(x_784);
 x_1239 = lean::box(0);
}
if (lean::is_scalar(x_1216)) {
 x_1240 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1240 = x_1216;
}
lean::cnstr_set(x_1240, 0, x_1222);
lean::cnstr_set(x_1240, 1, x_1224);
lean::cnstr_set(x_1240, 2, x_1226);
lean::cnstr_set(x_1240, 3, x_1228);
lean::cnstr_set_scalar(x_1240, sizeof(void*)*4, x_1175);
x_1241 = x_1240;
if (lean::is_scalar(x_1239)) {
 x_1242 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1242 = x_1239;
}
lean::cnstr_set(x_1242, 0, x_1231);
lean::cnstr_set(x_1242, 1, x_1233);
lean::cnstr_set(x_1242, 2, x_1235);
lean::cnstr_set(x_1242, 3, x_1237);
lean::cnstr_set_scalar(x_1242, sizeof(void*)*4, x_1175);
x_1243 = x_1242;
if (lean::is_scalar(x_1230)) {
 x_1244 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1244 = x_1230;
}
lean::cnstr_set(x_1244, 0, x_1241);
lean::cnstr_set(x_1244, 1, x_1217);
lean::cnstr_set(x_1244, 2, x_1219);
lean::cnstr_set(x_1244, 3, x_1243);
lean::cnstr_set_scalar(x_1244, sizeof(void*)*4, x_1143);
x_1245 = x_1244;
if (lean::is_scalar(x_1221)) {
 x_1246 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1246 = x_1221;
}
lean::cnstr_set(x_1246, 0, x_1245);
lean::cnstr_set(x_1246, 1, x_1);
lean::cnstr_set(x_1246, 2, x_2);
lean::cnstr_set(x_1246, 3, x_3);
lean::cnstr_set_scalar(x_1246, sizeof(void*)*4, x_1175);
x_1247 = x_1246;
return x_1247;
}
}
}
else
{
uint8 x_1248; 
x_1248 = lean::cnstr_get_scalar<uint8>(x_1144, sizeof(void*)*4);
if (x_1248 == 0)
{
obj* x_1249; 
x_1249 = lean::cnstr_get(x_3, 3);
lean::inc(x_1249);
if (lean::obj_tag(x_1249) == 0)
{
obj* x_1251; obj* x_1253; obj* x_1255; obj* x_1256; obj* x_1258; obj* x_1260; obj* x_1262; obj* x_1264; obj* x_1265; obj* x_1267; obj* x_1269; obj* x_1270; obj* x_1272; obj* x_1274; obj* x_1276; obj* x_1278; obj* x_1279; obj* x_1280; obj* x_1282; obj* x_1283; obj* x_1284; obj* x_1285; obj* x_1286; obj* x_1287; obj* x_1288; obj* x_1289; obj* x_1290; 
x_1251 = lean::cnstr_get(x_0, 1);
x_1253 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_1255 = x_0;
} else {
 lean::inc(x_1251);
 lean::inc(x_1253);
 lean::dec(x_0);
 x_1255 = lean::box(0);
}
x_1256 = lean::cnstr_get(x_175, 0);
x_1258 = lean::cnstr_get(x_175, 1);
x_1260 = lean::cnstr_get(x_175, 2);
x_1262 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_1264 = x_175;
} else {
 lean::inc(x_1256);
 lean::inc(x_1258);
 lean::inc(x_1260);
 lean::inc(x_1262);
 lean::dec(x_175);
 x_1264 = lean::box(0);
}
x_1265 = lean::cnstr_get(x_3, 1);
x_1267 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1269 = x_3;
} else {
 lean::inc(x_1265);
 lean::inc(x_1267);
 lean::dec(x_3);
 x_1269 = lean::box(0);
}
x_1270 = lean::cnstr_get(x_1144, 0);
x_1272 = lean::cnstr_get(x_1144, 1);
x_1274 = lean::cnstr_get(x_1144, 2);
x_1276 = lean::cnstr_get(x_1144, 3);
if (lean::is_exclusive(x_1144)) {
 x_1278 = x_1144;
} else {
 lean::inc(x_1270);
 lean::inc(x_1272);
 lean::inc(x_1274);
 lean::inc(x_1276);
 lean::dec(x_1144);
 x_1278 = lean::box(0);
}
if (lean::is_scalar(x_1278)) {
 x_1279 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1279 = x_1278;
}
lean::cnstr_set(x_1279, 0, x_1256);
lean::cnstr_set(x_1279, 1, x_1258);
lean::cnstr_set(x_1279, 2, x_1260);
lean::cnstr_set(x_1279, 3, x_1262);
lean::cnstr_set_scalar(x_1279, sizeof(void*)*4, x_1100);
x_1280 = x_1279;
lean::inc(x_784);
if (lean::is_scalar(x_1269)) {
 x_1282 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1282 = x_1269;
}
lean::cnstr_set(x_1282, 0, x_1280);
lean::cnstr_set(x_1282, 1, x_1251);
lean::cnstr_set(x_1282, 2, x_1253);
lean::cnstr_set(x_1282, 3, x_784);
if (lean::is_exclusive(x_784)) {
 lean::cnstr_release(x_784, 0);
 lean::cnstr_release(x_784, 1);
 lean::cnstr_release(x_784, 2);
 lean::cnstr_release(x_784, 3);
 x_1283 = x_784;
} else {
 lean::dec(x_784);
 x_1283 = lean::box(0);
}
lean::cnstr_set_scalar(x_1282, sizeof(void*)*4, x_1248);
x_1284 = x_1282;
if (lean::is_scalar(x_1283)) {
 x_1285 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1285 = x_1283;
}
lean::cnstr_set(x_1285, 0, x_1284);
lean::cnstr_set(x_1285, 1, x_1);
lean::cnstr_set(x_1285, 2, x_2);
lean::cnstr_set(x_1285, 3, x_1270);
lean::cnstr_set_scalar(x_1285, sizeof(void*)*4, x_1100);
x_1286 = x_1285;
if (lean::is_scalar(x_1264)) {
 x_1287 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1287 = x_1264;
}
lean::cnstr_set(x_1287, 0, x_1276);
lean::cnstr_set(x_1287, 1, x_1265);
lean::cnstr_set(x_1287, 2, x_1267);
lean::cnstr_set(x_1287, 3, x_1249);
lean::cnstr_set_scalar(x_1287, sizeof(void*)*4, x_1100);
x_1288 = x_1287;
if (lean::is_scalar(x_1255)) {
 x_1289 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1289 = x_1255;
}
lean::cnstr_set(x_1289, 0, x_1286);
lean::cnstr_set(x_1289, 1, x_1272);
lean::cnstr_set(x_1289, 2, x_1274);
lean::cnstr_set(x_1289, 3, x_1288);
lean::cnstr_set_scalar(x_1289, sizeof(void*)*4, x_1248);
x_1290 = x_1289;
return x_1290;
}
else
{
uint8 x_1291; 
x_1291 = lean::cnstr_get_scalar<uint8>(x_1249, sizeof(void*)*4);
if (x_1291 == 0)
{
obj* x_1292; obj* x_1294; obj* x_1296; obj* x_1297; obj* x_1299; obj* x_1301; obj* x_1303; obj* x_1305; obj* x_1306; obj* x_1308; obj* x_1310; obj* x_1311; obj* x_1313; obj* x_1315; obj* x_1317; obj* x_1319; obj* x_1320; obj* x_1322; obj* x_1324; obj* x_1326; obj* x_1328; obj* x_1329; obj* x_1330; obj* x_1332; obj* x_1333; obj* x_1334; obj* x_1335; obj* x_1336; obj* x_1337; obj* x_1338; obj* x_1339; obj* x_1340; obj* x_1341; obj* x_1342; 
x_1292 = lean::cnstr_get(x_0, 1);
x_1294 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_1296 = x_0;
} else {
 lean::inc(x_1292);
 lean::inc(x_1294);
 lean::dec(x_0);
 x_1296 = lean::box(0);
}
x_1297 = lean::cnstr_get(x_175, 0);
x_1299 = lean::cnstr_get(x_175, 1);
x_1301 = lean::cnstr_get(x_175, 2);
x_1303 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_1305 = x_175;
} else {
 lean::inc(x_1297);
 lean::inc(x_1299);
 lean::inc(x_1301);
 lean::inc(x_1303);
 lean::dec(x_175);
 x_1305 = lean::box(0);
}
x_1306 = lean::cnstr_get(x_3, 1);
x_1308 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1310 = x_3;
} else {
 lean::inc(x_1306);
 lean::inc(x_1308);
 lean::dec(x_3);
 x_1310 = lean::box(0);
}
x_1311 = lean::cnstr_get(x_1144, 0);
x_1313 = lean::cnstr_get(x_1144, 1);
x_1315 = lean::cnstr_get(x_1144, 2);
x_1317 = lean::cnstr_get(x_1144, 3);
if (lean::is_exclusive(x_1144)) {
 x_1319 = x_1144;
} else {
 lean::inc(x_1311);
 lean::inc(x_1313);
 lean::inc(x_1315);
 lean::inc(x_1317);
 lean::dec(x_1144);
 x_1319 = lean::box(0);
}
x_1320 = lean::cnstr_get(x_1249, 0);
x_1322 = lean::cnstr_get(x_1249, 1);
x_1324 = lean::cnstr_get(x_1249, 2);
x_1326 = lean::cnstr_get(x_1249, 3);
if (lean::is_exclusive(x_1249)) {
 x_1328 = x_1249;
} else {
 lean::inc(x_1320);
 lean::inc(x_1322);
 lean::inc(x_1324);
 lean::inc(x_1326);
 lean::dec(x_1249);
 x_1328 = lean::box(0);
}
if (lean::is_scalar(x_1328)) {
 x_1329 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1329 = x_1328;
}
lean::cnstr_set(x_1329, 0, x_1297);
lean::cnstr_set(x_1329, 1, x_1299);
lean::cnstr_set(x_1329, 2, x_1301);
lean::cnstr_set(x_1329, 3, x_1303);
lean::cnstr_set_scalar(x_1329, sizeof(void*)*4, x_1100);
x_1330 = x_1329;
lean::inc(x_784);
if (lean::is_scalar(x_1319)) {
 x_1332 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1332 = x_1319;
}
lean::cnstr_set(x_1332, 0, x_1330);
lean::cnstr_set(x_1332, 1, x_1292);
lean::cnstr_set(x_1332, 2, x_1294);
lean::cnstr_set(x_1332, 3, x_784);
if (lean::is_exclusive(x_784)) {
 lean::cnstr_release(x_784, 0);
 lean::cnstr_release(x_784, 1);
 lean::cnstr_release(x_784, 2);
 lean::cnstr_release(x_784, 3);
 x_1333 = x_784;
} else {
 lean::dec(x_784);
 x_1333 = lean::box(0);
}
lean::cnstr_set_scalar(x_1332, sizeof(void*)*4, x_1291);
x_1334 = x_1332;
if (lean::is_scalar(x_1310)) {
 x_1335 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1335 = x_1310;
}
lean::cnstr_set(x_1335, 0, x_1311);
lean::cnstr_set(x_1335, 1, x_1313);
lean::cnstr_set(x_1335, 2, x_1315);
lean::cnstr_set(x_1335, 3, x_1317);
lean::cnstr_set_scalar(x_1335, sizeof(void*)*4, x_1291);
x_1336 = x_1335;
if (lean::is_scalar(x_1333)) {
 x_1337 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1337 = x_1333;
}
lean::cnstr_set(x_1337, 0, x_1334);
lean::cnstr_set(x_1337, 1, x_1);
lean::cnstr_set(x_1337, 2, x_2);
lean::cnstr_set(x_1337, 3, x_1336);
lean::cnstr_set_scalar(x_1337, sizeof(void*)*4, x_1100);
x_1338 = x_1337;
if (lean::is_scalar(x_1305)) {
 x_1339 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1339 = x_1305;
}
lean::cnstr_set(x_1339, 0, x_1320);
lean::cnstr_set(x_1339, 1, x_1322);
lean::cnstr_set(x_1339, 2, x_1324);
lean::cnstr_set(x_1339, 3, x_1326);
lean::cnstr_set_scalar(x_1339, sizeof(void*)*4, x_1100);
x_1340 = x_1339;
if (lean::is_scalar(x_1296)) {
 x_1341 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1341 = x_1296;
}
lean::cnstr_set(x_1341, 0, x_1338);
lean::cnstr_set(x_1341, 1, x_1306);
lean::cnstr_set(x_1341, 2, x_1308);
lean::cnstr_set(x_1341, 3, x_1340);
lean::cnstr_set_scalar(x_1341, sizeof(void*)*4, x_1291);
x_1342 = x_1341;
return x_1342;
}
else
{
obj* x_1343; obj* x_1345; obj* x_1347; obj* x_1348; obj* x_1350; obj* x_1352; obj* x_1354; obj* x_1356; obj* x_1357; obj* x_1359; obj* x_1361; obj* x_1363; obj* x_1365; obj* x_1366; obj* x_1368; obj* x_1370; obj* x_1371; obj* x_1373; obj* x_1375; obj* x_1377; obj* x_1379; obj* x_1380; obj* x_1381; obj* x_1382; obj* x_1383; obj* x_1384; obj* x_1385; obj* x_1386; obj* x_1387; obj* x_1388; obj* x_1389; obj* x_1390; obj* x_1391; 
x_1343 = lean::cnstr_get(x_0, 1);
x_1345 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_1347 = x_0;
} else {
 lean::inc(x_1343);
 lean::inc(x_1345);
 lean::dec(x_0);
 x_1347 = lean::box(0);
}
x_1348 = lean::cnstr_get(x_175, 0);
x_1350 = lean::cnstr_get(x_175, 1);
x_1352 = lean::cnstr_get(x_175, 2);
x_1354 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_1356 = x_175;
} else {
 lean::inc(x_1348);
 lean::inc(x_1350);
 lean::inc(x_1352);
 lean::inc(x_1354);
 lean::dec(x_175);
 x_1356 = lean::box(0);
}
x_1357 = lean::cnstr_get(x_784, 0);
x_1359 = lean::cnstr_get(x_784, 1);
x_1361 = lean::cnstr_get(x_784, 2);
x_1363 = lean::cnstr_get(x_784, 3);
if (lean::is_exclusive(x_784)) {
 x_1365 = x_784;
} else {
 lean::inc(x_1357);
 lean::inc(x_1359);
 lean::inc(x_1361);
 lean::inc(x_1363);
 lean::dec(x_784);
 x_1365 = lean::box(0);
}
x_1366 = lean::cnstr_get(x_3, 1);
x_1368 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1370 = x_3;
} else {
 lean::inc(x_1366);
 lean::inc(x_1368);
 lean::dec(x_3);
 x_1370 = lean::box(0);
}
x_1371 = lean::cnstr_get(x_1144, 0);
x_1373 = lean::cnstr_get(x_1144, 1);
x_1375 = lean::cnstr_get(x_1144, 2);
x_1377 = lean::cnstr_get(x_1144, 3);
if (lean::is_exclusive(x_1144)) {
 x_1379 = x_1144;
} else {
 lean::inc(x_1371);
 lean::inc(x_1373);
 lean::inc(x_1375);
 lean::inc(x_1377);
 lean::dec(x_1144);
 x_1379 = lean::box(0);
}
if (lean::is_scalar(x_1379)) {
 x_1380 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1380 = x_1379;
}
lean::cnstr_set(x_1380, 0, x_1348);
lean::cnstr_set(x_1380, 1, x_1350);
lean::cnstr_set(x_1380, 2, x_1352);
lean::cnstr_set(x_1380, 3, x_1354);
lean::cnstr_set_scalar(x_1380, sizeof(void*)*4, x_1291);
x_1381 = x_1380;
if (lean::is_scalar(x_1370)) {
 x_1382 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1382 = x_1370;
}
lean::cnstr_set(x_1382, 0, x_1357);
lean::cnstr_set(x_1382, 1, x_1359);
lean::cnstr_set(x_1382, 2, x_1361);
lean::cnstr_set(x_1382, 3, x_1363);
lean::cnstr_set_scalar(x_1382, sizeof(void*)*4, x_1291);
x_1383 = x_1382;
if (lean::is_scalar(x_1365)) {
 x_1384 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1384 = x_1365;
}
lean::cnstr_set(x_1384, 0, x_1381);
lean::cnstr_set(x_1384, 1, x_1343);
lean::cnstr_set(x_1384, 2, x_1345);
lean::cnstr_set(x_1384, 3, x_1383);
lean::cnstr_set_scalar(x_1384, sizeof(void*)*4, x_1248);
x_1385 = x_1384;
if (lean::is_scalar(x_1356)) {
 x_1386 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1386 = x_1356;
}
lean::cnstr_set(x_1386, 0, x_1385);
lean::cnstr_set(x_1386, 1, x_1);
lean::cnstr_set(x_1386, 2, x_2);
lean::cnstr_set(x_1386, 3, x_1371);
lean::cnstr_set_scalar(x_1386, sizeof(void*)*4, x_1291);
x_1387 = x_1386;
if (lean::is_scalar(x_1347)) {
 x_1388 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1388 = x_1347;
}
lean::cnstr_set(x_1388, 0, x_1377);
lean::cnstr_set(x_1388, 1, x_1366);
lean::cnstr_set(x_1388, 2, x_1368);
lean::cnstr_set(x_1388, 3, x_1249);
lean::cnstr_set_scalar(x_1388, sizeof(void*)*4, x_1291);
x_1389 = x_1388;
x_1390 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1390, 0, x_1387);
lean::cnstr_set(x_1390, 1, x_1373);
lean::cnstr_set(x_1390, 2, x_1375);
lean::cnstr_set(x_1390, 3, x_1389);
lean::cnstr_set_scalar(x_1390, sizeof(void*)*4, x_1248);
x_1391 = x_1390;
return x_1391;
}
}
}
else
{
obj* x_1392; 
x_1392 = lean::cnstr_get(x_3, 3);
lean::inc(x_1392);
if (lean::obj_tag(x_1392) == 0)
{
obj* x_1394; obj* x_1395; obj* x_1397; obj* x_1399; obj* x_1400; obj* x_1402; obj* x_1404; obj* x_1406; obj* x_1408; obj* x_1409; obj* x_1411; obj* x_1413; obj* x_1415; obj* x_1417; obj* x_1418; obj* x_1419; obj* x_1420; obj* x_1421; obj* x_1422; obj* x_1423; obj* x_1424; obj* x_1425; 
if (lean::is_exclusive(x_1144)) {
 lean::cnstr_release(x_1144, 0);
 lean::cnstr_release(x_1144, 1);
 lean::cnstr_release(x_1144, 2);
 lean::cnstr_release(x_1144, 3);
 x_1394 = x_1144;
} else {
 lean::dec(x_1144);
 x_1394 = lean::box(0);
}
x_1395 = lean::cnstr_get(x_0, 1);
x_1397 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_1399 = x_0;
} else {
 lean::inc(x_1395);
 lean::inc(x_1397);
 lean::dec(x_0);
 x_1399 = lean::box(0);
}
x_1400 = lean::cnstr_get(x_175, 0);
x_1402 = lean::cnstr_get(x_175, 1);
x_1404 = lean::cnstr_get(x_175, 2);
x_1406 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_1408 = x_175;
} else {
 lean::inc(x_1400);
 lean::inc(x_1402);
 lean::inc(x_1404);
 lean::inc(x_1406);
 lean::dec(x_175);
 x_1408 = lean::box(0);
}
x_1409 = lean::cnstr_get(x_784, 0);
x_1411 = lean::cnstr_get(x_784, 1);
x_1413 = lean::cnstr_get(x_784, 2);
x_1415 = lean::cnstr_get(x_784, 3);
if (lean::is_exclusive(x_784)) {
 x_1417 = x_784;
} else {
 lean::inc(x_1409);
 lean::inc(x_1411);
 lean::inc(x_1413);
 lean::inc(x_1415);
 lean::dec(x_784);
 x_1417 = lean::box(0);
}
if (lean::is_scalar(x_1394)) {
 x_1418 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1418 = x_1394;
}
lean::cnstr_set(x_1418, 0, x_1400);
lean::cnstr_set(x_1418, 1, x_1402);
lean::cnstr_set(x_1418, 2, x_1404);
lean::cnstr_set(x_1418, 3, x_1406);
lean::cnstr_set_scalar(x_1418, sizeof(void*)*4, x_1248);
x_1419 = x_1418;
if (lean::is_scalar(x_1417)) {
 x_1420 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1420 = x_1417;
}
lean::cnstr_set(x_1420, 0, x_1409);
lean::cnstr_set(x_1420, 1, x_1411);
lean::cnstr_set(x_1420, 2, x_1413);
lean::cnstr_set(x_1420, 3, x_1415);
lean::cnstr_set_scalar(x_1420, sizeof(void*)*4, x_1248);
x_1421 = x_1420;
if (lean::is_scalar(x_1408)) {
 x_1422 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1422 = x_1408;
}
lean::cnstr_set(x_1422, 0, x_1419);
lean::cnstr_set(x_1422, 1, x_1395);
lean::cnstr_set(x_1422, 2, x_1397);
lean::cnstr_set(x_1422, 3, x_1421);
lean::cnstr_set_scalar(x_1422, sizeof(void*)*4, x_1143);
x_1423 = x_1422;
if (lean::is_scalar(x_1399)) {
 x_1424 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1424 = x_1399;
}
lean::cnstr_set(x_1424, 0, x_1423);
lean::cnstr_set(x_1424, 1, x_1);
lean::cnstr_set(x_1424, 2, x_2);
lean::cnstr_set(x_1424, 3, x_3);
lean::cnstr_set_scalar(x_1424, sizeof(void*)*4, x_1248);
x_1425 = x_1424;
return x_1425;
}
else
{
uint8 x_1426; 
x_1426 = lean::cnstr_get_scalar<uint8>(x_1392, sizeof(void*)*4);
if (x_1426 == 0)
{
obj* x_1427; obj* x_1429; obj* x_1431; obj* x_1432; obj* x_1434; obj* x_1436; obj* x_1438; obj* x_1440; obj* x_1441; obj* x_1443; obj* x_1445; obj* x_1447; obj* x_1449; obj* x_1450; obj* x_1452; obj* x_1454; obj* x_1455; obj* x_1457; obj* x_1459; obj* x_1461; obj* x_1463; obj* x_1464; obj* x_1465; obj* x_1466; obj* x_1467; obj* x_1468; obj* x_1469; obj* x_1470; obj* x_1471; obj* x_1472; obj* x_1473; obj* x_1474; obj* x_1475; 
x_1427 = lean::cnstr_get(x_0, 1);
x_1429 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_1431 = x_0;
} else {
 lean::inc(x_1427);
 lean::inc(x_1429);
 lean::dec(x_0);
 x_1431 = lean::box(0);
}
x_1432 = lean::cnstr_get(x_175, 0);
x_1434 = lean::cnstr_get(x_175, 1);
x_1436 = lean::cnstr_get(x_175, 2);
x_1438 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_1440 = x_175;
} else {
 lean::inc(x_1432);
 lean::inc(x_1434);
 lean::inc(x_1436);
 lean::inc(x_1438);
 lean::dec(x_175);
 x_1440 = lean::box(0);
}
x_1441 = lean::cnstr_get(x_784, 0);
x_1443 = lean::cnstr_get(x_784, 1);
x_1445 = lean::cnstr_get(x_784, 2);
x_1447 = lean::cnstr_get(x_784, 3);
if (lean::is_exclusive(x_784)) {
 x_1449 = x_784;
} else {
 lean::inc(x_1441);
 lean::inc(x_1443);
 lean::inc(x_1445);
 lean::inc(x_1447);
 lean::dec(x_784);
 x_1449 = lean::box(0);
}
x_1450 = lean::cnstr_get(x_3, 1);
x_1452 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1454 = x_3;
} else {
 lean::inc(x_1450);
 lean::inc(x_1452);
 lean::dec(x_3);
 x_1454 = lean::box(0);
}
x_1455 = lean::cnstr_get(x_1392, 0);
x_1457 = lean::cnstr_get(x_1392, 1);
x_1459 = lean::cnstr_get(x_1392, 2);
x_1461 = lean::cnstr_get(x_1392, 3);
if (lean::is_exclusive(x_1392)) {
 x_1463 = x_1392;
} else {
 lean::inc(x_1455);
 lean::inc(x_1457);
 lean::inc(x_1459);
 lean::inc(x_1461);
 lean::dec(x_1392);
 x_1463 = lean::box(0);
}
if (lean::is_scalar(x_1463)) {
 x_1464 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1464 = x_1463;
}
lean::cnstr_set(x_1464, 0, x_1432);
lean::cnstr_set(x_1464, 1, x_1434);
lean::cnstr_set(x_1464, 2, x_1436);
lean::cnstr_set(x_1464, 3, x_1438);
lean::cnstr_set_scalar(x_1464, sizeof(void*)*4, x_1248);
x_1465 = x_1464;
if (lean::is_scalar(x_1454)) {
 x_1466 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1466 = x_1454;
}
lean::cnstr_set(x_1466, 0, x_1441);
lean::cnstr_set(x_1466, 1, x_1443);
lean::cnstr_set(x_1466, 2, x_1445);
lean::cnstr_set(x_1466, 3, x_1447);
lean::cnstr_set_scalar(x_1466, sizeof(void*)*4, x_1248);
x_1467 = x_1466;
if (lean::is_scalar(x_1449)) {
 x_1468 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1468 = x_1449;
}
lean::cnstr_set(x_1468, 0, x_1465);
lean::cnstr_set(x_1468, 1, x_1427);
lean::cnstr_set(x_1468, 2, x_1429);
lean::cnstr_set(x_1468, 3, x_1467);
lean::cnstr_set_scalar(x_1468, sizeof(void*)*4, x_1426);
x_1469 = x_1468;
if (lean::is_scalar(x_1440)) {
 x_1470 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1470 = x_1440;
}
lean::cnstr_set(x_1470, 0, x_1469);
lean::cnstr_set(x_1470, 1, x_1);
lean::cnstr_set(x_1470, 2, x_2);
lean::cnstr_set(x_1470, 3, x_1144);
lean::cnstr_set_scalar(x_1470, sizeof(void*)*4, x_1248);
x_1471 = x_1470;
if (lean::is_scalar(x_1431)) {
 x_1472 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1472 = x_1431;
}
lean::cnstr_set(x_1472, 0, x_1455);
lean::cnstr_set(x_1472, 1, x_1457);
lean::cnstr_set(x_1472, 2, x_1459);
lean::cnstr_set(x_1472, 3, x_1461);
lean::cnstr_set_scalar(x_1472, sizeof(void*)*4, x_1248);
x_1473 = x_1472;
x_1474 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1474, 0, x_1471);
lean::cnstr_set(x_1474, 1, x_1450);
lean::cnstr_set(x_1474, 2, x_1452);
lean::cnstr_set(x_1474, 3, x_1473);
lean::cnstr_set_scalar(x_1474, sizeof(void*)*4, x_1426);
x_1475 = x_1474;
return x_1475;
}
else
{
obj* x_1476; obj* x_1478; obj* x_1480; obj* x_1481; obj* x_1483; obj* x_1485; obj* x_1487; obj* x_1489; obj* x_1490; obj* x_1492; obj* x_1494; obj* x_1496; obj* x_1498; obj* x_1499; obj* x_1501; obj* x_1503; obj* x_1504; obj* x_1506; obj* x_1508; obj* x_1510; obj* x_1512; obj* x_1513; obj* x_1514; obj* x_1515; obj* x_1516; obj* x_1517; obj* x_1518; obj* x_1519; obj* x_1520; obj* x_1521; obj* x_1522; obj* x_1523; obj* x_1524; 
x_1476 = lean::cnstr_get(x_0, 1);
x_1478 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_1480 = x_0;
} else {
 lean::inc(x_1476);
 lean::inc(x_1478);
 lean::dec(x_0);
 x_1480 = lean::box(0);
}
x_1481 = lean::cnstr_get(x_175, 0);
x_1483 = lean::cnstr_get(x_175, 1);
x_1485 = lean::cnstr_get(x_175, 2);
x_1487 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_1489 = x_175;
} else {
 lean::inc(x_1481);
 lean::inc(x_1483);
 lean::inc(x_1485);
 lean::inc(x_1487);
 lean::dec(x_175);
 x_1489 = lean::box(0);
}
x_1490 = lean::cnstr_get(x_784, 0);
x_1492 = lean::cnstr_get(x_784, 1);
x_1494 = lean::cnstr_get(x_784, 2);
x_1496 = lean::cnstr_get(x_784, 3);
if (lean::is_exclusive(x_784)) {
 x_1498 = x_784;
} else {
 lean::inc(x_1490);
 lean::inc(x_1492);
 lean::inc(x_1494);
 lean::inc(x_1496);
 lean::dec(x_784);
 x_1498 = lean::box(0);
}
x_1499 = lean::cnstr_get(x_3, 1);
x_1501 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1503 = x_3;
} else {
 lean::inc(x_1499);
 lean::inc(x_1501);
 lean::dec(x_3);
 x_1503 = lean::box(0);
}
x_1504 = lean::cnstr_get(x_1144, 0);
x_1506 = lean::cnstr_get(x_1144, 1);
x_1508 = lean::cnstr_get(x_1144, 2);
x_1510 = lean::cnstr_get(x_1144, 3);
if (lean::is_exclusive(x_1144)) {
 x_1512 = x_1144;
} else {
 lean::inc(x_1504);
 lean::inc(x_1506);
 lean::inc(x_1508);
 lean::inc(x_1510);
 lean::dec(x_1144);
 x_1512 = lean::box(0);
}
if (lean::is_scalar(x_1512)) {
 x_1513 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1513 = x_1512;
}
lean::cnstr_set(x_1513, 0, x_1481);
lean::cnstr_set(x_1513, 1, x_1483);
lean::cnstr_set(x_1513, 2, x_1485);
lean::cnstr_set(x_1513, 3, x_1487);
lean::cnstr_set_scalar(x_1513, sizeof(void*)*4, x_1426);
x_1514 = x_1513;
if (lean::is_scalar(x_1503)) {
 x_1515 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1515 = x_1503;
}
lean::cnstr_set(x_1515, 0, x_1490);
lean::cnstr_set(x_1515, 1, x_1492);
lean::cnstr_set(x_1515, 2, x_1494);
lean::cnstr_set(x_1515, 3, x_1496);
lean::cnstr_set_scalar(x_1515, sizeof(void*)*4, x_1426);
x_1516 = x_1515;
if (lean::is_scalar(x_1498)) {
 x_1517 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1517 = x_1498;
}
lean::cnstr_set(x_1517, 0, x_1514);
lean::cnstr_set(x_1517, 1, x_1476);
lean::cnstr_set(x_1517, 2, x_1478);
lean::cnstr_set(x_1517, 3, x_1516);
lean::cnstr_set_scalar(x_1517, sizeof(void*)*4, x_1143);
x_1518 = x_1517;
if (lean::is_scalar(x_1489)) {
 x_1519 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1519 = x_1489;
}
lean::cnstr_set(x_1519, 0, x_1504);
lean::cnstr_set(x_1519, 1, x_1506);
lean::cnstr_set(x_1519, 2, x_1508);
lean::cnstr_set(x_1519, 3, x_1510);
lean::cnstr_set_scalar(x_1519, sizeof(void*)*4, x_1426);
x_1520 = x_1519;
if (lean::is_scalar(x_1480)) {
 x_1521 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1521 = x_1480;
}
lean::cnstr_set(x_1521, 0, x_1520);
lean::cnstr_set(x_1521, 1, x_1499);
lean::cnstr_set(x_1521, 2, x_1501);
lean::cnstr_set(x_1521, 3, x_1392);
lean::cnstr_set_scalar(x_1521, sizeof(void*)*4, x_1143);
x_1522 = x_1521;
x_1523 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1523, 0, x_1518);
lean::cnstr_set(x_1523, 1, x_1);
lean::cnstr_set(x_1523, 2, x_2);
lean::cnstr_set(x_1523, 3, x_1522);
lean::cnstr_set_scalar(x_1523, sizeof(void*)*4, x_1426);
x_1524 = x_1523;
return x_1524;
}
}
}
}
}
else
{
obj* x_1525; obj* x_1527; obj* x_1529; obj* x_1530; obj* x_1532; obj* x_1534; obj* x_1536; obj* x_1538; obj* x_1539; obj* x_1541; obj* x_1543; obj* x_1545; obj* x_1547; obj* x_1548; obj* x_1549; obj* x_1550; obj* x_1551; obj* x_1552; obj* x_1553; obj* x_1554; obj* x_1555; 
x_1525 = lean::cnstr_get(x_0, 1);
x_1527 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 3);
 x_1529 = x_0;
} else {
 lean::inc(x_1525);
 lean::inc(x_1527);
 lean::dec(x_0);
 x_1529 = lean::box(0);
}
x_1530 = lean::cnstr_get(x_175, 0);
x_1532 = lean::cnstr_get(x_175, 1);
x_1534 = lean::cnstr_get(x_175, 2);
x_1536 = lean::cnstr_get(x_175, 3);
if (lean::is_exclusive(x_175)) {
 x_1538 = x_175;
} else {
 lean::inc(x_1530);
 lean::inc(x_1532);
 lean::inc(x_1534);
 lean::inc(x_1536);
 lean::dec(x_175);
 x_1538 = lean::box(0);
}
x_1539 = lean::cnstr_get(x_784, 0);
x_1541 = lean::cnstr_get(x_784, 1);
x_1543 = lean::cnstr_get(x_784, 2);
x_1545 = lean::cnstr_get(x_784, 3);
if (lean::is_exclusive(x_784)) {
 x_1547 = x_784;
} else {
 lean::inc(x_1539);
 lean::inc(x_1541);
 lean::inc(x_1543);
 lean::inc(x_1545);
 lean::dec(x_784);
 x_1547 = lean::box(0);
}
if (lean::is_scalar(x_1547)) {
 x_1548 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1548 = x_1547;
}
lean::cnstr_set(x_1548, 0, x_1530);
lean::cnstr_set(x_1548, 1, x_1532);
lean::cnstr_set(x_1548, 2, x_1534);
lean::cnstr_set(x_1548, 3, x_1536);
lean::cnstr_set_scalar(x_1548, sizeof(void*)*4, x_1143);
x_1549 = x_1548;
if (lean::is_scalar(x_1538)) {
 x_1550 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1550 = x_1538;
}
lean::cnstr_set(x_1550, 0, x_1539);
lean::cnstr_set(x_1550, 1, x_1541);
lean::cnstr_set(x_1550, 2, x_1543);
lean::cnstr_set(x_1550, 3, x_1545);
lean::cnstr_set_scalar(x_1550, sizeof(void*)*4, x_1143);
x_1551 = x_1550;
if (lean::is_scalar(x_1529)) {
 x_1552 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1552 = x_1529;
}
lean::cnstr_set(x_1552, 0, x_1549);
lean::cnstr_set(x_1552, 1, x_1525);
lean::cnstr_set(x_1552, 2, x_1527);
lean::cnstr_set(x_1552, 3, x_1551);
lean::cnstr_set_scalar(x_1552, sizeof(void*)*4, x_174);
x_1553 = x_1552;
x_1554 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1554, 0, x_1553);
lean::cnstr_set(x_1554, 1, x_1);
lean::cnstr_set(x_1554, 2, x_2);
lean::cnstr_set(x_1554, 3, x_3);
lean::cnstr_set_scalar(x_1554, sizeof(void*)*4, x_1143);
x_1555 = x_1554;
return x_1555;
}
}
}
}
}
}
}
else
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_1556; obj* x_1557; 
x_1556 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1556, 0, x_0);
lean::cnstr_set(x_1556, 1, x_1);
lean::cnstr_set(x_1556, 2, x_2);
lean::cnstr_set(x_1556, 3, x_3);
lean::cnstr_set_scalar(x_1556, sizeof(void*)*4, x_174);
x_1557 = x_1556;
return x_1557;
}
else
{
uint8 x_1558; 
x_1558 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*4);
if (x_1558 == 0)
{
obj* x_1559; 
x_1559 = lean::cnstr_get(x_3, 0);
lean::inc(x_1559);
if (lean::obj_tag(x_1559) == 0)
{
obj* x_1561; 
x_1561 = lean::cnstr_get(x_3, 3);
lean::inc(x_1561);
if (lean::obj_tag(x_1561) == 0)
{
obj* x_1563; obj* x_1565; obj* x_1567; obj* x_1568; obj* x_1569; obj* x_1570; obj* x_1571; 
x_1563 = lean::cnstr_get(x_3, 1);
x_1565 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1567 = x_3;
} else {
 lean::inc(x_1563);
 lean::inc(x_1565);
 lean::dec(x_3);
 x_1567 = lean::box(0);
}
if (lean::is_scalar(x_1567)) {
 x_1568 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1568 = x_1567;
}
lean::cnstr_set(x_1568, 0, x_1561);
lean::cnstr_set(x_1568, 1, x_1563);
lean::cnstr_set(x_1568, 2, x_1565);
lean::cnstr_set(x_1568, 3, x_1561);
lean::cnstr_set_scalar(x_1568, sizeof(void*)*4, x_1558);
x_1569 = x_1568;
x_1570 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1570, 0, x_0);
lean::cnstr_set(x_1570, 1, x_1);
lean::cnstr_set(x_1570, 2, x_2);
lean::cnstr_set(x_1570, 3, x_1569);
lean::cnstr_set_scalar(x_1570, sizeof(void*)*4, x_174);
x_1571 = x_1570;
return x_1571;
}
else
{
uint8 x_1572; 
x_1572 = lean::cnstr_get_scalar<uint8>(x_1561, sizeof(void*)*4);
if (x_1572 == 0)
{
obj* x_1573; obj* x_1575; obj* x_1577; obj* x_1578; obj* x_1580; obj* x_1582; obj* x_1584; obj* x_1586; obj* x_1588; obj* x_1589; obj* x_1590; obj* x_1591; obj* x_1592; obj* x_1593; obj* x_1594; 
x_1573 = lean::cnstr_get(x_3, 1);
x_1575 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1577 = x_3;
} else {
 lean::inc(x_1573);
 lean::inc(x_1575);
 lean::dec(x_3);
 x_1577 = lean::box(0);
}
x_1578 = lean::cnstr_get(x_1561, 0);
x_1580 = lean::cnstr_get(x_1561, 1);
x_1582 = lean::cnstr_get(x_1561, 2);
x_1584 = lean::cnstr_get(x_1561, 3);
if (lean::is_exclusive(x_1561)) {
 x_1586 = x_1561;
} else {
 lean::inc(x_1578);
 lean::inc(x_1580);
 lean::inc(x_1582);
 lean::inc(x_1584);
 lean::dec(x_1561);
 x_1586 = lean::box(0);
}
lean::inc(x_0);
if (lean::is_scalar(x_1586)) {
 x_1588 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1588 = x_1586;
}
lean::cnstr_set(x_1588, 0, x_0);
lean::cnstr_set(x_1588, 1, x_1);
lean::cnstr_set(x_1588, 2, x_2);
lean::cnstr_set(x_1588, 3, x_1559);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_1589 = x_0;
} else {
 lean::dec(x_0);
 x_1589 = lean::box(0);
}
lean::cnstr_set_scalar(x_1588, sizeof(void*)*4, x_174);
x_1590 = x_1588;
if (lean::is_scalar(x_1577)) {
 x_1591 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1591 = x_1577;
}
lean::cnstr_set(x_1591, 0, x_1578);
lean::cnstr_set(x_1591, 1, x_1580);
lean::cnstr_set(x_1591, 2, x_1582);
lean::cnstr_set(x_1591, 3, x_1584);
lean::cnstr_set_scalar(x_1591, sizeof(void*)*4, x_174);
x_1592 = x_1591;
if (lean::is_scalar(x_1589)) {
 x_1593 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1593 = x_1589;
}
lean::cnstr_set(x_1593, 0, x_1590);
lean::cnstr_set(x_1593, 1, x_1573);
lean::cnstr_set(x_1593, 2, x_1575);
lean::cnstr_set(x_1593, 3, x_1592);
lean::cnstr_set_scalar(x_1593, sizeof(void*)*4, x_1572);
x_1594 = x_1593;
return x_1594;
}
else
{
obj* x_1595; obj* x_1596; obj* x_1598; obj* x_1600; obj* x_1602; obj* x_1604; obj* x_1605; obj* x_1606; obj* x_1607; obj* x_1608; 
if (lean::is_exclusive(x_1561)) {
 lean::cnstr_release(x_1561, 0);
 lean::cnstr_release(x_1561, 1);
 lean::cnstr_release(x_1561, 2);
 lean::cnstr_release(x_1561, 3);
 x_1595 = x_1561;
} else {
 lean::dec(x_1561);
 x_1595 = lean::box(0);
}
x_1596 = lean::cnstr_get(x_0, 0);
x_1598 = lean::cnstr_get(x_0, 1);
x_1600 = lean::cnstr_get(x_0, 2);
x_1602 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_1604 = x_0;
} else {
 lean::inc(x_1596);
 lean::inc(x_1598);
 lean::inc(x_1600);
 lean::inc(x_1602);
 lean::dec(x_0);
 x_1604 = lean::box(0);
}
if (lean::is_scalar(x_1595)) {
 x_1605 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1605 = x_1595;
}
lean::cnstr_set(x_1605, 0, x_1596);
lean::cnstr_set(x_1605, 1, x_1598);
lean::cnstr_set(x_1605, 2, x_1600);
lean::cnstr_set(x_1605, 3, x_1602);
lean::cnstr_set_scalar(x_1605, sizeof(void*)*4, x_1572);
x_1606 = x_1605;
if (lean::is_scalar(x_1604)) {
 x_1607 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1607 = x_1604;
}
lean::cnstr_set(x_1607, 0, x_1606);
lean::cnstr_set(x_1607, 1, x_1);
lean::cnstr_set(x_1607, 2, x_2);
lean::cnstr_set(x_1607, 3, x_3);
lean::cnstr_set_scalar(x_1607, sizeof(void*)*4, x_1572);
x_1608 = x_1607;
return x_1608;
}
}
}
else
{
uint8 x_1609; 
x_1609 = lean::cnstr_get_scalar<uint8>(x_1559, sizeof(void*)*4);
if (x_1609 == 0)
{
obj* x_1610; 
x_1610 = lean::cnstr_get(x_3, 3);
lean::inc(x_1610);
if (lean::obj_tag(x_1610) == 0)
{
obj* x_1612; obj* x_1614; obj* x_1616; obj* x_1617; obj* x_1619; obj* x_1621; obj* x_1623; obj* x_1625; obj* x_1627; obj* x_1628; obj* x_1629; obj* x_1630; obj* x_1631; obj* x_1632; obj* x_1633; 
x_1612 = lean::cnstr_get(x_3, 1);
x_1614 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1616 = x_3;
} else {
 lean::inc(x_1612);
 lean::inc(x_1614);
 lean::dec(x_3);
 x_1616 = lean::box(0);
}
x_1617 = lean::cnstr_get(x_1559, 0);
x_1619 = lean::cnstr_get(x_1559, 1);
x_1621 = lean::cnstr_get(x_1559, 2);
x_1623 = lean::cnstr_get(x_1559, 3);
if (lean::is_exclusive(x_1559)) {
 x_1625 = x_1559;
} else {
 lean::inc(x_1617);
 lean::inc(x_1619);
 lean::inc(x_1621);
 lean::inc(x_1623);
 lean::dec(x_1559);
 x_1625 = lean::box(0);
}
lean::inc(x_0);
if (lean::is_scalar(x_1625)) {
 x_1627 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1627 = x_1625;
}
lean::cnstr_set(x_1627, 0, x_0);
lean::cnstr_set(x_1627, 1, x_1);
lean::cnstr_set(x_1627, 2, x_2);
lean::cnstr_set(x_1627, 3, x_1617);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_1628 = x_0;
} else {
 lean::dec(x_0);
 x_1628 = lean::box(0);
}
lean::cnstr_set_scalar(x_1627, sizeof(void*)*4, x_174);
x_1629 = x_1627;
if (lean::is_scalar(x_1616)) {
 x_1630 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1630 = x_1616;
}
lean::cnstr_set(x_1630, 0, x_1623);
lean::cnstr_set(x_1630, 1, x_1612);
lean::cnstr_set(x_1630, 2, x_1614);
lean::cnstr_set(x_1630, 3, x_1610);
lean::cnstr_set_scalar(x_1630, sizeof(void*)*4, x_174);
x_1631 = x_1630;
if (lean::is_scalar(x_1628)) {
 x_1632 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1632 = x_1628;
}
lean::cnstr_set(x_1632, 0, x_1629);
lean::cnstr_set(x_1632, 1, x_1619);
lean::cnstr_set(x_1632, 2, x_1621);
lean::cnstr_set(x_1632, 3, x_1631);
lean::cnstr_set_scalar(x_1632, sizeof(void*)*4, x_1609);
x_1633 = x_1632;
return x_1633;
}
else
{
uint8 x_1634; 
x_1634 = lean::cnstr_get_scalar<uint8>(x_1610, sizeof(void*)*4);
if (x_1634 == 0)
{
obj* x_1635; obj* x_1637; obj* x_1639; obj* x_1640; obj* x_1642; obj* x_1644; obj* x_1646; obj* x_1648; obj* x_1649; obj* x_1651; obj* x_1653; obj* x_1655; obj* x_1657; obj* x_1658; obj* x_1659; obj* x_1661; obj* x_1662; obj* x_1663; obj* x_1664; obj* x_1665; obj* x_1666; obj* x_1667; 
x_1635 = lean::cnstr_get(x_3, 1);
x_1637 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1639 = x_3;
} else {
 lean::inc(x_1635);
 lean::inc(x_1637);
 lean::dec(x_3);
 x_1639 = lean::box(0);
}
x_1640 = lean::cnstr_get(x_1559, 0);
x_1642 = lean::cnstr_get(x_1559, 1);
x_1644 = lean::cnstr_get(x_1559, 2);
x_1646 = lean::cnstr_get(x_1559, 3);
if (lean::is_exclusive(x_1559)) {
 x_1648 = x_1559;
} else {
 lean::inc(x_1640);
 lean::inc(x_1642);
 lean::inc(x_1644);
 lean::inc(x_1646);
 lean::dec(x_1559);
 x_1648 = lean::box(0);
}
x_1649 = lean::cnstr_get(x_1610, 0);
x_1651 = lean::cnstr_get(x_1610, 1);
x_1653 = lean::cnstr_get(x_1610, 2);
x_1655 = lean::cnstr_get(x_1610, 3);
if (lean::is_exclusive(x_1610)) {
 x_1657 = x_1610;
} else {
 lean::inc(x_1649);
 lean::inc(x_1651);
 lean::inc(x_1653);
 lean::inc(x_1655);
 lean::dec(x_1610);
 x_1657 = lean::box(0);
}
if (lean::is_scalar(x_1657)) {
 x_1658 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1658 = x_1657;
}
lean::cnstr_set(x_1658, 0, x_1640);
lean::cnstr_set(x_1658, 1, x_1642);
lean::cnstr_set(x_1658, 2, x_1644);
lean::cnstr_set(x_1658, 3, x_1646);
lean::cnstr_set_scalar(x_1658, sizeof(void*)*4, x_1634);
x_1659 = x_1658;
lean::inc(x_0);
if (lean::is_scalar(x_1648)) {
 x_1661 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1661 = x_1648;
}
lean::cnstr_set(x_1661, 0, x_0);
lean::cnstr_set(x_1661, 1, x_1);
lean::cnstr_set(x_1661, 2, x_2);
lean::cnstr_set(x_1661, 3, x_1659);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_1662 = x_0;
} else {
 lean::dec(x_0);
 x_1662 = lean::box(0);
}
lean::cnstr_set_scalar(x_1661, sizeof(void*)*4, x_174);
x_1663 = x_1661;
if (lean::is_scalar(x_1639)) {
 x_1664 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1664 = x_1639;
}
lean::cnstr_set(x_1664, 0, x_1649);
lean::cnstr_set(x_1664, 1, x_1651);
lean::cnstr_set(x_1664, 2, x_1653);
lean::cnstr_set(x_1664, 3, x_1655);
lean::cnstr_set_scalar(x_1664, sizeof(void*)*4, x_174);
x_1665 = x_1664;
if (lean::is_scalar(x_1662)) {
 x_1666 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1666 = x_1662;
}
lean::cnstr_set(x_1666, 0, x_1663);
lean::cnstr_set(x_1666, 1, x_1635);
lean::cnstr_set(x_1666, 2, x_1637);
lean::cnstr_set(x_1666, 3, x_1665);
lean::cnstr_set_scalar(x_1666, sizeof(void*)*4, x_1634);
x_1667 = x_1666;
return x_1667;
}
else
{
obj* x_1668; obj* x_1670; obj* x_1672; obj* x_1674; obj* x_1676; obj* x_1677; obj* x_1679; obj* x_1681; obj* x_1682; obj* x_1684; obj* x_1686; obj* x_1688; obj* x_1690; obj* x_1691; obj* x_1692; obj* x_1693; obj* x_1694; obj* x_1695; obj* x_1696; obj* x_1697; obj* x_1698; 
x_1668 = lean::cnstr_get(x_0, 0);
x_1670 = lean::cnstr_get(x_0, 1);
x_1672 = lean::cnstr_get(x_0, 2);
x_1674 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_1676 = x_0;
} else {
 lean::inc(x_1668);
 lean::inc(x_1670);
 lean::inc(x_1672);
 lean::inc(x_1674);
 lean::dec(x_0);
 x_1676 = lean::box(0);
}
x_1677 = lean::cnstr_get(x_3, 1);
x_1679 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1681 = x_3;
} else {
 lean::inc(x_1677);
 lean::inc(x_1679);
 lean::dec(x_3);
 x_1681 = lean::box(0);
}
x_1682 = lean::cnstr_get(x_1559, 0);
x_1684 = lean::cnstr_get(x_1559, 1);
x_1686 = lean::cnstr_get(x_1559, 2);
x_1688 = lean::cnstr_get(x_1559, 3);
if (lean::is_exclusive(x_1559)) {
 x_1690 = x_1559;
} else {
 lean::inc(x_1682);
 lean::inc(x_1684);
 lean::inc(x_1686);
 lean::inc(x_1688);
 lean::dec(x_1559);
 x_1690 = lean::box(0);
}
if (lean::is_scalar(x_1690)) {
 x_1691 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1691 = x_1690;
}
lean::cnstr_set(x_1691, 0, x_1668);
lean::cnstr_set(x_1691, 1, x_1670);
lean::cnstr_set(x_1691, 2, x_1672);
lean::cnstr_set(x_1691, 3, x_1674);
lean::cnstr_set_scalar(x_1691, sizeof(void*)*4, x_1634);
x_1692 = x_1691;
if (lean::is_scalar(x_1681)) {
 x_1693 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1693 = x_1681;
}
lean::cnstr_set(x_1693, 0, x_1692);
lean::cnstr_set(x_1693, 1, x_1);
lean::cnstr_set(x_1693, 2, x_2);
lean::cnstr_set(x_1693, 3, x_1682);
lean::cnstr_set_scalar(x_1693, sizeof(void*)*4, x_1634);
x_1694 = x_1693;
if (lean::is_scalar(x_1676)) {
 x_1695 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1695 = x_1676;
}
lean::cnstr_set(x_1695, 0, x_1688);
lean::cnstr_set(x_1695, 1, x_1677);
lean::cnstr_set(x_1695, 2, x_1679);
lean::cnstr_set(x_1695, 3, x_1610);
lean::cnstr_set_scalar(x_1695, sizeof(void*)*4, x_1634);
x_1696 = x_1695;
x_1697 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1697, 0, x_1694);
lean::cnstr_set(x_1697, 1, x_1684);
lean::cnstr_set(x_1697, 2, x_1686);
lean::cnstr_set(x_1697, 3, x_1696);
lean::cnstr_set_scalar(x_1697, sizeof(void*)*4, x_1609);
x_1698 = x_1697;
return x_1698;
}
}
}
else
{
obj* x_1699; 
x_1699 = lean::cnstr_get(x_3, 3);
lean::inc(x_1699);
if (lean::obj_tag(x_1699) == 0)
{
obj* x_1701; obj* x_1702; obj* x_1704; obj* x_1706; obj* x_1708; obj* x_1710; obj* x_1711; obj* x_1712; obj* x_1713; obj* x_1714; 
if (lean::is_exclusive(x_1559)) {
 lean::cnstr_release(x_1559, 0);
 lean::cnstr_release(x_1559, 1);
 lean::cnstr_release(x_1559, 2);
 lean::cnstr_release(x_1559, 3);
 x_1701 = x_1559;
} else {
 lean::dec(x_1559);
 x_1701 = lean::box(0);
}
x_1702 = lean::cnstr_get(x_0, 0);
x_1704 = lean::cnstr_get(x_0, 1);
x_1706 = lean::cnstr_get(x_0, 2);
x_1708 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_1710 = x_0;
} else {
 lean::inc(x_1702);
 lean::inc(x_1704);
 lean::inc(x_1706);
 lean::inc(x_1708);
 lean::dec(x_0);
 x_1710 = lean::box(0);
}
if (lean::is_scalar(x_1701)) {
 x_1711 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1711 = x_1701;
}
lean::cnstr_set(x_1711, 0, x_1702);
lean::cnstr_set(x_1711, 1, x_1704);
lean::cnstr_set(x_1711, 2, x_1706);
lean::cnstr_set(x_1711, 3, x_1708);
lean::cnstr_set_scalar(x_1711, sizeof(void*)*4, x_1609);
x_1712 = x_1711;
if (lean::is_scalar(x_1710)) {
 x_1713 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1713 = x_1710;
}
lean::cnstr_set(x_1713, 0, x_1712);
lean::cnstr_set(x_1713, 1, x_1);
lean::cnstr_set(x_1713, 2, x_2);
lean::cnstr_set(x_1713, 3, x_3);
lean::cnstr_set_scalar(x_1713, sizeof(void*)*4, x_1609);
x_1714 = x_1713;
return x_1714;
}
else
{
uint8 x_1715; 
x_1715 = lean::cnstr_get_scalar<uint8>(x_1699, sizeof(void*)*4);
if (x_1715 == 0)
{
obj* x_1716; obj* x_1718; obj* x_1720; obj* x_1722; obj* x_1724; obj* x_1725; obj* x_1727; obj* x_1729; obj* x_1730; obj* x_1732; obj* x_1734; obj* x_1736; obj* x_1738; obj* x_1739; obj* x_1740; obj* x_1741; obj* x_1742; obj* x_1743; obj* x_1744; obj* x_1745; obj* x_1746; 
x_1716 = lean::cnstr_get(x_0, 0);
x_1718 = lean::cnstr_get(x_0, 1);
x_1720 = lean::cnstr_get(x_0, 2);
x_1722 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_1724 = x_0;
} else {
 lean::inc(x_1716);
 lean::inc(x_1718);
 lean::inc(x_1720);
 lean::inc(x_1722);
 lean::dec(x_0);
 x_1724 = lean::box(0);
}
x_1725 = lean::cnstr_get(x_3, 1);
x_1727 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1729 = x_3;
} else {
 lean::inc(x_1725);
 lean::inc(x_1727);
 lean::dec(x_3);
 x_1729 = lean::box(0);
}
x_1730 = lean::cnstr_get(x_1699, 0);
x_1732 = lean::cnstr_get(x_1699, 1);
x_1734 = lean::cnstr_get(x_1699, 2);
x_1736 = lean::cnstr_get(x_1699, 3);
if (lean::is_exclusive(x_1699)) {
 x_1738 = x_1699;
} else {
 lean::inc(x_1730);
 lean::inc(x_1732);
 lean::inc(x_1734);
 lean::inc(x_1736);
 lean::dec(x_1699);
 x_1738 = lean::box(0);
}
if (lean::is_scalar(x_1738)) {
 x_1739 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1739 = x_1738;
}
lean::cnstr_set(x_1739, 0, x_1716);
lean::cnstr_set(x_1739, 1, x_1718);
lean::cnstr_set(x_1739, 2, x_1720);
lean::cnstr_set(x_1739, 3, x_1722);
lean::cnstr_set_scalar(x_1739, sizeof(void*)*4, x_1609);
x_1740 = x_1739;
if (lean::is_scalar(x_1729)) {
 x_1741 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1741 = x_1729;
}
lean::cnstr_set(x_1741, 0, x_1740);
lean::cnstr_set(x_1741, 1, x_1);
lean::cnstr_set(x_1741, 2, x_2);
lean::cnstr_set(x_1741, 3, x_1559);
lean::cnstr_set_scalar(x_1741, sizeof(void*)*4, x_1609);
x_1742 = x_1741;
if (lean::is_scalar(x_1724)) {
 x_1743 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1743 = x_1724;
}
lean::cnstr_set(x_1743, 0, x_1730);
lean::cnstr_set(x_1743, 1, x_1732);
lean::cnstr_set(x_1743, 2, x_1734);
lean::cnstr_set(x_1743, 3, x_1736);
lean::cnstr_set_scalar(x_1743, sizeof(void*)*4, x_1609);
x_1744 = x_1743;
x_1745 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1745, 0, x_1742);
lean::cnstr_set(x_1745, 1, x_1725);
lean::cnstr_set(x_1745, 2, x_1727);
lean::cnstr_set(x_1745, 3, x_1744);
lean::cnstr_set_scalar(x_1745, sizeof(void*)*4, x_1715);
x_1746 = x_1745;
return x_1746;
}
else
{
obj* x_1747; obj* x_1749; obj* x_1751; obj* x_1753; obj* x_1755; obj* x_1756; obj* x_1758; obj* x_1760; obj* x_1761; obj* x_1763; obj* x_1765; obj* x_1767; obj* x_1769; obj* x_1770; obj* x_1771; obj* x_1772; obj* x_1773; obj* x_1774; obj* x_1775; obj* x_1776; obj* x_1777; 
x_1747 = lean::cnstr_get(x_0, 0);
x_1749 = lean::cnstr_get(x_0, 1);
x_1751 = lean::cnstr_get(x_0, 2);
x_1753 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_1755 = x_0;
} else {
 lean::inc(x_1747);
 lean::inc(x_1749);
 lean::inc(x_1751);
 lean::inc(x_1753);
 lean::dec(x_0);
 x_1755 = lean::box(0);
}
x_1756 = lean::cnstr_get(x_3, 1);
x_1758 = lean::cnstr_get(x_3, 2);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 3);
 x_1760 = x_3;
} else {
 lean::inc(x_1756);
 lean::inc(x_1758);
 lean::dec(x_3);
 x_1760 = lean::box(0);
}
x_1761 = lean::cnstr_get(x_1559, 0);
x_1763 = lean::cnstr_get(x_1559, 1);
x_1765 = lean::cnstr_get(x_1559, 2);
x_1767 = lean::cnstr_get(x_1559, 3);
if (lean::is_exclusive(x_1559)) {
 x_1769 = x_1559;
} else {
 lean::inc(x_1761);
 lean::inc(x_1763);
 lean::inc(x_1765);
 lean::inc(x_1767);
 lean::dec(x_1559);
 x_1769 = lean::box(0);
}
if (lean::is_scalar(x_1769)) {
 x_1770 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1770 = x_1769;
}
lean::cnstr_set(x_1770, 0, x_1747);
lean::cnstr_set(x_1770, 1, x_1749);
lean::cnstr_set(x_1770, 2, x_1751);
lean::cnstr_set(x_1770, 3, x_1753);
lean::cnstr_set_scalar(x_1770, sizeof(void*)*4, x_1715);
x_1771 = x_1770;
if (lean::is_scalar(x_1760)) {
 x_1772 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1772 = x_1760;
}
lean::cnstr_set(x_1772, 0, x_1761);
lean::cnstr_set(x_1772, 1, x_1763);
lean::cnstr_set(x_1772, 2, x_1765);
lean::cnstr_set(x_1772, 3, x_1767);
lean::cnstr_set_scalar(x_1772, sizeof(void*)*4, x_1715);
x_1773 = x_1772;
if (lean::is_scalar(x_1755)) {
 x_1774 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1774 = x_1755;
}
lean::cnstr_set(x_1774, 0, x_1773);
lean::cnstr_set(x_1774, 1, x_1756);
lean::cnstr_set(x_1774, 2, x_1758);
lean::cnstr_set(x_1774, 3, x_1699);
lean::cnstr_set_scalar(x_1774, sizeof(void*)*4, x_1558);
x_1775 = x_1774;
x_1776 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1776, 0, x_1771);
lean::cnstr_set(x_1776, 1, x_1);
lean::cnstr_set(x_1776, 2, x_2);
lean::cnstr_set(x_1776, 3, x_1775);
lean::cnstr_set_scalar(x_1776, sizeof(void*)*4, x_1715);
x_1777 = x_1776;
return x_1777;
}
}
}
}
}
else
{
obj* x_1778; obj* x_1780; obj* x_1782; obj* x_1784; obj* x_1786; obj* x_1787; obj* x_1788; obj* x_1789; obj* x_1790; 
x_1778 = lean::cnstr_get(x_0, 0);
x_1780 = lean::cnstr_get(x_0, 1);
x_1782 = lean::cnstr_get(x_0, 2);
x_1784 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_1786 = x_0;
} else {
 lean::inc(x_1778);
 lean::inc(x_1780);
 lean::inc(x_1782);
 lean::inc(x_1784);
 lean::dec(x_0);
 x_1786 = lean::box(0);
}
if (lean::is_scalar(x_1786)) {
 x_1787 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_1787 = x_1786;
}
lean::cnstr_set(x_1787, 0, x_1778);
lean::cnstr_set(x_1787, 1, x_1780);
lean::cnstr_set(x_1787, 2, x_1782);
lean::cnstr_set(x_1787, 3, x_1784);
lean::cnstr_set_scalar(x_1787, sizeof(void*)*4, x_1558);
x_1788 = x_1787;
x_1789 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_1789, 0, x_1788);
lean::cnstr_set(x_1789, 1, x_1);
lean::cnstr_set(x_1789, 2, x_2);
lean::cnstr_set(x_1789, 3, x_3);
lean::cnstr_set_scalar(x_1789, sizeof(void*)*4, x_1558);
x_1790 = x_1789;
return x_1790;
}
}
}
}
}
}
obj* l_RBNode_balance_u_2083___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balance_u_2083___main___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_balance_u_2083___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_balance_u_2083___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_balance_u_2083___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_balance_u_2083___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBNode_balance_u_2083(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balance_u_2083___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_balance_u_2083___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_balance_u_2083(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_setRed___main___rarg(obj* x_0) {
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
x_10 = 0;
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
obj* l_RBNode_setRed___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_setRed___main___rarg), 1, 0);
return x_2;
}
}
obj* l_RBNode_setRed___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_setRed___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_setRed___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBNode_setRed___main___rarg(x_0);
return x_1;
}
}
obj* l_RBNode_setRed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_setRed___rarg), 1, 0);
return x_2;
}
}
obj* l_RBNode_setRed___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_setRed(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_balLeft___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 2, x_2);
lean::cnstr_set(x_5, 3, x_3);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_1);
lean::cnstr_set(x_10, 2, x_2);
lean::cnstr_set(x_10, 3, x_3);
lean::cnstr_set_scalar(x_10, sizeof(void*)*4, x_7);
x_11 = x_10;
return x_11;
}
else
{
uint8 x_12; 
x_12 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*4);
if (x_12 == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_13 = lean::cnstr_get(x_3, 1);
x_15 = lean::cnstr_get(x_3, 2);
x_17 = lean::cnstr_get(x_3, 3);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_19 = x_3;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_3);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_8);
lean::cnstr_set(x_20, 1, x_13);
lean::cnstr_set(x_20, 2, x_15);
lean::cnstr_set(x_20, 3, x_17);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_12);
x_21 = x_20;
x_22 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_22, 0, x_0);
lean::cnstr_set(x_22, 1, x_1);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_21);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_12);
x_23 = x_22;
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_24 = lean::cnstr_get(x_3, 1);
x_26 = lean::cnstr_get(x_3, 2);
x_28 = lean::cnstr_get(x_3, 3);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_30 = x_3;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_3);
 x_30 = lean::box(0);
}
x_31 = lean::cnstr_get(x_8, 0);
x_33 = lean::cnstr_get(x_8, 1);
x_35 = lean::cnstr_get(x_8, 2);
x_37 = lean::cnstr_get(x_8, 3);
if (lean::is_exclusive(x_8)) {
 x_39 = x_8;
} else {
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_8);
 x_39 = lean::box(0);
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_0);
lean::cnstr_set(x_40, 1, x_1);
lean::cnstr_set(x_40, 2, x_2);
lean::cnstr_set(x_40, 3, x_31);
lean::cnstr_set_scalar(x_40, sizeof(void*)*4, x_12);
x_41 = x_40;
x_42 = l_RBNode_setRed___main___rarg(x_28);
x_43 = l_RBNode_balance_u_2083___main___rarg(x_37, x_24, x_26, x_42);
if (lean::is_scalar(x_30)) {
 x_44 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_44 = x_30;
}
lean::cnstr_set(x_44, 0, x_41);
lean::cnstr_set(x_44, 1, x_33);
lean::cnstr_set(x_44, 2, x_35);
lean::cnstr_set(x_44, 3, x_43);
lean::cnstr_set_scalar(x_44, sizeof(void*)*4, x_7);
x_45 = x_44;
return x_45;
}
}
}
else
{
obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_54; uint8 x_55; obj* x_56; obj* x_57; obj* x_58; 
x_46 = lean::cnstr_get(x_3, 0);
x_48 = lean::cnstr_get(x_3, 1);
x_50 = lean::cnstr_get(x_3, 2);
x_52 = lean::cnstr_get(x_3, 3);
if (lean::is_exclusive(x_3)) {
 x_54 = x_3;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::inc(x_50);
 lean::inc(x_52);
 lean::dec(x_3);
 x_54 = lean::box(0);
}
x_55 = 0;
if (lean::is_scalar(x_54)) {
 x_56 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_56 = x_54;
}
lean::cnstr_set(x_56, 0, x_46);
lean::cnstr_set(x_56, 1, x_48);
lean::cnstr_set(x_56, 2, x_50);
lean::cnstr_set(x_56, 3, x_52);
lean::cnstr_set_scalar(x_56, sizeof(void*)*4, x_55);
x_57 = x_56;
x_58 = l_RBNode_balance_u_2083___main___rarg(x_0, x_1, x_2, x_57);
return x_58;
}
}
}
else
{
uint8 x_59; 
x_59 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_59 == 0)
{
obj* x_60; obj* x_62; obj* x_64; obj* x_66; obj* x_68; uint8 x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_60 = lean::cnstr_get(x_0, 0);
x_62 = lean::cnstr_get(x_0, 1);
x_64 = lean::cnstr_get(x_0, 2);
x_66 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_68 = x_0;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::inc(x_64);
 lean::inc(x_66);
 lean::dec(x_0);
 x_68 = lean::box(0);
}
x_69 = 1;
if (lean::is_scalar(x_68)) {
 x_70 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_70 = x_68;
}
lean::cnstr_set(x_70, 0, x_60);
lean::cnstr_set(x_70, 1, x_62);
lean::cnstr_set(x_70, 2, x_64);
lean::cnstr_set(x_70, 3, x_66);
lean::cnstr_set_scalar(x_70, sizeof(void*)*4, x_69);
x_71 = x_70;
x_72 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_1);
lean::cnstr_set(x_72, 2, x_2);
lean::cnstr_set(x_72, 3, x_3);
lean::cnstr_set_scalar(x_72, sizeof(void*)*4, x_59);
x_73 = x_72;
return x_73;
}
else
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_74; obj* x_75; obj* x_76; 
x_74 = 0;
x_75 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_75, 0, x_0);
lean::cnstr_set(x_75, 1, x_1);
lean::cnstr_set(x_75, 2, x_2);
lean::cnstr_set(x_75, 3, x_3);
lean::cnstr_set_scalar(x_75, sizeof(void*)*4, x_74);
x_76 = x_75;
return x_76;
}
else
{
uint8 x_77; 
x_77 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*4);
if (x_77 == 0)
{
obj* x_78; 
x_78 = lean::cnstr_get(x_3, 0);
lean::inc(x_78);
if (lean::obj_tag(x_78) == 0)
{
obj* x_80; obj* x_81; 
x_80 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_80, 0, x_0);
lean::cnstr_set(x_80, 1, x_1);
lean::cnstr_set(x_80, 2, x_2);
lean::cnstr_set(x_80, 3, x_3);
lean::cnstr_set_scalar(x_80, sizeof(void*)*4, x_77);
x_81 = x_80;
return x_81;
}
else
{
uint8 x_82; 
x_82 = lean::cnstr_get_scalar<uint8>(x_78, sizeof(void*)*4);
if (x_82 == 0)
{
obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_83 = lean::cnstr_get(x_3, 1);
x_85 = lean::cnstr_get(x_3, 2);
x_87 = lean::cnstr_get(x_3, 3);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_89 = x_3;
} else {
 lean::inc(x_83);
 lean::inc(x_85);
 lean::inc(x_87);
 lean::dec(x_3);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_78);
lean::cnstr_set(x_90, 1, x_83);
lean::cnstr_set(x_90, 2, x_85);
lean::cnstr_set(x_90, 3, x_87);
lean::cnstr_set_scalar(x_90, sizeof(void*)*4, x_82);
x_91 = x_90;
x_92 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_92, 0, x_0);
lean::cnstr_set(x_92, 1, x_1);
lean::cnstr_set(x_92, 2, x_2);
lean::cnstr_set(x_92, 3, x_91);
lean::cnstr_set_scalar(x_92, sizeof(void*)*4, x_82);
x_93 = x_92;
return x_93;
}
else
{
obj* x_94; obj* x_96; obj* x_98; obj* x_100; obj* x_102; obj* x_103; obj* x_105; obj* x_107; obj* x_109; obj* x_110; obj* x_112; obj* x_114; obj* x_116; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
x_94 = lean::cnstr_get(x_0, 0);
x_96 = lean::cnstr_get(x_0, 1);
x_98 = lean::cnstr_get(x_0, 2);
x_100 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_102 = x_0;
} else {
 lean::inc(x_94);
 lean::inc(x_96);
 lean::inc(x_98);
 lean::inc(x_100);
 lean::dec(x_0);
 x_102 = lean::box(0);
}
x_103 = lean::cnstr_get(x_3, 1);
x_105 = lean::cnstr_get(x_3, 2);
x_107 = lean::cnstr_get(x_3, 3);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_109 = x_3;
} else {
 lean::inc(x_103);
 lean::inc(x_105);
 lean::inc(x_107);
 lean::dec(x_3);
 x_109 = lean::box(0);
}
x_110 = lean::cnstr_get(x_78, 0);
x_112 = lean::cnstr_get(x_78, 1);
x_114 = lean::cnstr_get(x_78, 2);
x_116 = lean::cnstr_get(x_78, 3);
if (lean::is_exclusive(x_78)) {
 x_118 = x_78;
} else {
 lean::inc(x_110);
 lean::inc(x_112);
 lean::inc(x_114);
 lean::inc(x_116);
 lean::dec(x_78);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_94);
lean::cnstr_set(x_119, 1, x_96);
lean::cnstr_set(x_119, 2, x_98);
lean::cnstr_set(x_119, 3, x_100);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_82);
x_120 = x_119;
if (lean::is_scalar(x_109)) {
 x_121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_121 = x_109;
}
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_1);
lean::cnstr_set(x_121, 2, x_2);
lean::cnstr_set(x_121, 3, x_110);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_82);
x_122 = x_121;
x_123 = l_RBNode_setRed___main___rarg(x_107);
x_124 = l_RBNode_balance_u_2083___main___rarg(x_116, x_103, x_105, x_123);
if (lean::is_scalar(x_102)) {
 x_125 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_125 = x_102;
}
lean::cnstr_set(x_125, 0, x_122);
lean::cnstr_set(x_125, 1, x_112);
lean::cnstr_set(x_125, 2, x_114);
lean::cnstr_set(x_125, 3, x_124);
lean::cnstr_set_scalar(x_125, sizeof(void*)*4, x_77);
x_126 = x_125;
return x_126;
}
}
}
else
{
obj* x_127; obj* x_129; obj* x_131; obj* x_133; obj* x_135; obj* x_136; obj* x_138; obj* x_140; obj* x_142; obj* x_144; obj* x_145; obj* x_146; uint8 x_147; obj* x_148; obj* x_149; obj* x_150; 
x_127 = lean::cnstr_get(x_0, 0);
x_129 = lean::cnstr_get(x_0, 1);
x_131 = lean::cnstr_get(x_0, 2);
x_133 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_135 = x_0;
} else {
 lean::inc(x_127);
 lean::inc(x_129);
 lean::inc(x_131);
 lean::inc(x_133);
 lean::dec(x_0);
 x_135 = lean::box(0);
}
x_136 = lean::cnstr_get(x_3, 0);
x_138 = lean::cnstr_get(x_3, 1);
x_140 = lean::cnstr_get(x_3, 2);
x_142 = lean::cnstr_get(x_3, 3);
if (lean::is_exclusive(x_3)) {
 x_144 = x_3;
} else {
 lean::inc(x_136);
 lean::inc(x_138);
 lean::inc(x_140);
 lean::inc(x_142);
 lean::dec(x_3);
 x_144 = lean::box(0);
}
if (lean::is_scalar(x_144)) {
 x_145 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_145 = x_144;
}
lean::cnstr_set(x_145, 0, x_127);
lean::cnstr_set(x_145, 1, x_129);
lean::cnstr_set(x_145, 2, x_131);
lean::cnstr_set(x_145, 3, x_133);
lean::cnstr_set_scalar(x_145, sizeof(void*)*4, x_77);
x_146 = x_145;
x_147 = 0;
if (lean::is_scalar(x_135)) {
 x_148 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_148 = x_135;
}
lean::cnstr_set(x_148, 0, x_136);
lean::cnstr_set(x_148, 1, x_138);
lean::cnstr_set(x_148, 2, x_140);
lean::cnstr_set(x_148, 3, x_142);
lean::cnstr_set_scalar(x_148, sizeof(void*)*4, x_147);
x_149 = x_148;
x_150 = l_RBNode_balance_u_2083___main___rarg(x_146, x_1, x_2, x_149);
return x_150;
}
}
}
}
}
}
obj* l_RBNode_balLeft___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balLeft___main___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_balLeft___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_balLeft___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_balLeft___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_balLeft___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBNode_balLeft(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balLeft___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_balLeft___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_balLeft(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_balRight___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_4; obj* x_5; obj* x_6; 
x_4 = 0;
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 2, x_2);
lean::cnstr_set(x_5, 3, x_3);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_4);
x_6 = x_5;
return x_6;
}
else
{
uint8 x_7; 
x_7 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_7 == 0)
{
obj* x_8; 
x_8 = lean::cnstr_get(x_0, 3);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_1);
lean::cnstr_set(x_10, 2, x_2);
lean::cnstr_set(x_10, 3, x_3);
lean::cnstr_set_scalar(x_10, sizeof(void*)*4, x_7);
x_11 = x_10;
return x_11;
}
else
{
uint8 x_12; 
x_12 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*4);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 lean::cnstr_release(x_8, 3);
 x_13 = x_8;
} else {
 lean::dec(x_8);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_0);
lean::cnstr_set(x_14, 1, x_1);
lean::cnstr_set(x_14, 2, x_2);
lean::cnstr_set(x_14, 3, x_3);
lean::cnstr_set_scalar(x_14, sizeof(void*)*4, x_12);
x_15 = x_14;
return x_15;
}
else
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_16 = lean::cnstr_get(x_0, 0);
x_18 = lean::cnstr_get(x_0, 1);
x_20 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 3);
 x_22 = x_0;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_0);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_8, 0);
x_25 = lean::cnstr_get(x_8, 1);
x_27 = lean::cnstr_get(x_8, 2);
x_29 = lean::cnstr_get(x_8, 3);
if (lean::is_exclusive(x_8)) {
 x_31 = x_8;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::inc(x_27);
 lean::inc(x_29);
 lean::dec(x_8);
 x_31 = lean::box(0);
}
x_32 = l_RBNode_setRed___main___rarg(x_16);
x_33 = l_RBNode_balance_u_2083___main___rarg(x_32, x_18, x_20, x_23);
if (lean::is_scalar(x_31)) {
 x_34 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_34 = x_31;
}
lean::cnstr_set(x_34, 0, x_29);
lean::cnstr_set(x_34, 1, x_1);
lean::cnstr_set(x_34, 2, x_2);
lean::cnstr_set(x_34, 3, x_3);
lean::cnstr_set_scalar(x_34, sizeof(void*)*4, x_12);
x_35 = x_34;
if (lean::is_scalar(x_22)) {
 x_36 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_36 = x_22;
}
lean::cnstr_set(x_36, 0, x_33);
lean::cnstr_set(x_36, 1, x_25);
lean::cnstr_set(x_36, 2, x_27);
lean::cnstr_set(x_36, 3, x_35);
lean::cnstr_set_scalar(x_36, sizeof(void*)*4, x_7);
x_37 = x_36;
return x_37;
}
}
}
else
{
obj* x_38; obj* x_40; obj* x_42; obj* x_44; obj* x_46; uint8 x_47; obj* x_48; obj* x_49; obj* x_50; 
x_38 = lean::cnstr_get(x_0, 0);
x_40 = lean::cnstr_get(x_0, 1);
x_42 = lean::cnstr_get(x_0, 2);
x_44 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_46 = x_0;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_0);
 x_46 = lean::box(0);
}
x_47 = 0;
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_38);
lean::cnstr_set(x_48, 1, x_40);
lean::cnstr_set(x_48, 2, x_42);
lean::cnstr_set(x_48, 3, x_44);
lean::cnstr_set_scalar(x_48, sizeof(void*)*4, x_47);
x_49 = x_48;
x_50 = l_RBNode_balance_u_2083___main___rarg(x_49, x_1, x_2, x_3);
return x_50;
}
}
}
else
{
uint8 x_51; 
x_51 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*4);
if (x_51 == 0)
{
obj* x_52; obj* x_54; obj* x_56; obj* x_58; obj* x_60; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_52 = lean::cnstr_get(x_3, 0);
x_54 = lean::cnstr_get(x_3, 1);
x_56 = lean::cnstr_get(x_3, 2);
x_58 = lean::cnstr_get(x_3, 3);
if (lean::is_exclusive(x_3)) {
 x_60 = x_3;
} else {
 lean::inc(x_52);
 lean::inc(x_54);
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_3);
 x_60 = lean::box(0);
}
x_61 = 1;
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_52);
lean::cnstr_set(x_62, 1, x_54);
lean::cnstr_set(x_62, 2, x_56);
lean::cnstr_set(x_62, 3, x_58);
lean::cnstr_set_scalar(x_62, sizeof(void*)*4, x_61);
x_63 = x_62;
x_64 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_64, 0, x_0);
lean::cnstr_set(x_64, 1, x_1);
lean::cnstr_set(x_64, 2, x_2);
lean::cnstr_set(x_64, 3, x_63);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_51);
x_65 = x_64;
return x_65;
}
else
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_66; obj* x_67; obj* x_68; 
x_66 = 0;
x_67 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_67, 0, x_0);
lean::cnstr_set(x_67, 1, x_1);
lean::cnstr_set(x_67, 2, x_2);
lean::cnstr_set(x_67, 3, x_3);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_66);
x_68 = x_67;
return x_68;
}
else
{
uint8 x_69; 
x_69 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_69 == 0)
{
obj* x_70; 
x_70 = lean::cnstr_get(x_0, 3);
lean::inc(x_70);
if (lean::obj_tag(x_70) == 0)
{
obj* x_72; obj* x_73; 
x_72 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_72, 0, x_0);
lean::cnstr_set(x_72, 1, x_1);
lean::cnstr_set(x_72, 2, x_2);
lean::cnstr_set(x_72, 3, x_3);
lean::cnstr_set_scalar(x_72, sizeof(void*)*4, x_69);
x_73 = x_72;
return x_73;
}
else
{
uint8 x_74; 
x_74 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*4);
if (x_74 == 0)
{
obj* x_75; obj* x_76; obj* x_77; 
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 lean::cnstr_release(x_70, 1);
 lean::cnstr_release(x_70, 2);
 lean::cnstr_release(x_70, 3);
 x_75 = x_70;
} else {
 lean::dec(x_70);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_0);
lean::cnstr_set(x_76, 1, x_1);
lean::cnstr_set(x_76, 2, x_2);
lean::cnstr_set(x_76, 3, x_3);
lean::cnstr_set_scalar(x_76, sizeof(void*)*4, x_74);
x_77 = x_76;
return x_77;
}
else
{
obj* x_78; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_87; obj* x_89; obj* x_91; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_78 = lean::cnstr_get(x_0, 0);
x_80 = lean::cnstr_get(x_0, 1);
x_82 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 3);
 x_84 = x_0;
} else {
 lean::inc(x_78);
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_0);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_70, 0);
x_87 = lean::cnstr_get(x_70, 1);
x_89 = lean::cnstr_get(x_70, 2);
x_91 = lean::cnstr_get(x_70, 3);
if (lean::is_exclusive(x_70)) {
 x_93 = x_70;
} else {
 lean::inc(x_85);
 lean::inc(x_87);
 lean::inc(x_89);
 lean::inc(x_91);
 lean::dec(x_70);
 x_93 = lean::box(0);
}
x_94 = l_RBNode_setRed___main___rarg(x_78);
x_95 = l_RBNode_balance_u_2083___main___rarg(x_94, x_80, x_82, x_85);
if (lean::is_scalar(x_93)) {
 x_96 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_96 = x_93;
}
lean::cnstr_set(x_96, 0, x_91);
lean::cnstr_set(x_96, 1, x_1);
lean::cnstr_set(x_96, 2, x_2);
lean::cnstr_set(x_96, 3, x_3);
lean::cnstr_set_scalar(x_96, sizeof(void*)*4, x_74);
x_97 = x_96;
if (lean::is_scalar(x_84)) {
 x_98 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_98 = x_84;
}
lean::cnstr_set(x_98, 0, x_95);
lean::cnstr_set(x_98, 1, x_87);
lean::cnstr_set(x_98, 2, x_89);
lean::cnstr_set(x_98, 3, x_97);
lean::cnstr_set_scalar(x_98, sizeof(void*)*4, x_69);
x_99 = x_98;
return x_99;
}
}
}
else
{
obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_108; uint8 x_109; obj* x_110; obj* x_111; obj* x_112; 
x_100 = lean::cnstr_get(x_0, 0);
x_102 = lean::cnstr_get(x_0, 1);
x_104 = lean::cnstr_get(x_0, 2);
x_106 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 x_108 = x_0;
} else {
 lean::inc(x_100);
 lean::inc(x_102);
 lean::inc(x_104);
 lean::inc(x_106);
 lean::dec(x_0);
 x_108 = lean::box(0);
}
x_109 = 0;
if (lean::is_scalar(x_108)) {
 x_110 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_110 = x_108;
}
lean::cnstr_set(x_110, 0, x_100);
lean::cnstr_set(x_110, 1, x_102);
lean::cnstr_set(x_110, 2, x_104);
lean::cnstr_set(x_110, 3, x_106);
lean::cnstr_set_scalar(x_110, sizeof(void*)*4, x_109);
x_111 = x_110;
x_112 = l_RBNode_balance_u_2083___main___rarg(x_111, x_1, x_2, x_3);
return x_112;
}
}
}
}
}
}
obj* l_RBNode_balRight(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_balRight___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_balRight___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_balRight(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_appendTrees___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_1;
}
else
{
uint8 x_2; 
x_2 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_2 == 0)
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
uint8 x_3; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_3 == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; 
x_4 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_0, 1);
x_8 = lean::cnstr_get(x_0, 2);
x_10 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_1, 0);
x_15 = lean::cnstr_get(x_1, 1);
x_17 = lean::cnstr_get(x_1, 2);
x_19 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_21 = x_1;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::inc(x_19);
 lean::dec(x_1);
 x_21 = lean::box(0);
}
x_22 = l_RBNode_appendTrees___main___rarg(x_10, x_13);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
if (lean::is_scalar(x_21)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_21;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_15);
lean::cnstr_set(x_23, 2, x_17);
lean::cnstr_set(x_23, 3, x_19);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_3);
x_24 = x_23;
if (lean::is_scalar(x_12)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_12;
}
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_6);
lean::cnstr_set(x_25, 2, x_8);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_3);
x_26 = x_25;
return x_26;
}
else
{
uint8 x_27; 
x_27 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*4);
if (x_27 == 0)
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_28 = lean::cnstr_get(x_22, 0);
x_30 = lean::cnstr_get(x_22, 1);
x_32 = lean::cnstr_get(x_22, 2);
x_34 = lean::cnstr_get(x_22, 3);
if (lean::is_exclusive(x_22)) {
 x_36 = x_22;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_22);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_4);
lean::cnstr_set(x_37, 1, x_6);
lean::cnstr_set(x_37, 2, x_8);
lean::cnstr_set(x_37, 3, x_28);
lean::cnstr_set_scalar(x_37, sizeof(void*)*4, x_27);
x_38 = x_37;
if (lean::is_scalar(x_21)) {
 x_39 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_39 = x_21;
}
lean::cnstr_set(x_39, 0, x_34);
lean::cnstr_set(x_39, 1, x_15);
lean::cnstr_set(x_39, 2, x_17);
lean::cnstr_set(x_39, 3, x_19);
lean::cnstr_set_scalar(x_39, sizeof(void*)*4, x_27);
x_40 = x_39;
if (lean::is_scalar(x_12)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_12;
}
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set(x_41, 1, x_30);
lean::cnstr_set(x_41, 2, x_32);
lean::cnstr_set(x_41, 3, x_40);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_27);
x_42 = x_41;
return x_42;
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
if (lean::is_scalar(x_21)) {
 x_43 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_43 = x_21;
}
lean::cnstr_set(x_43, 0, x_22);
lean::cnstr_set(x_43, 1, x_15);
lean::cnstr_set(x_43, 2, x_17);
lean::cnstr_set(x_43, 3, x_19);
lean::cnstr_set_scalar(x_43, sizeof(void*)*4, x_3);
x_44 = x_43;
if (lean::is_scalar(x_12)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_12;
}
lean::cnstr_set(x_45, 0, x_4);
lean::cnstr_set(x_45, 1, x_6);
lean::cnstr_set(x_45, 2, x_8);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_3);
x_46 = x_45;
return x_46;
}
}
}
else
{
obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_47 = lean::cnstr_get(x_0, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_0, 1);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_0, 2);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_0, 3);
lean::inc(x_53);
lean::dec(x_0);
lean::inc(x_1);
x_57 = l_RBNode_appendTrees___main___rarg(x_53, x_1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_58 = x_1;
} else {
 lean::dec(x_1);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_47);
lean::cnstr_set(x_59, 1, x_49);
lean::cnstr_set(x_59, 2, x_51);
lean::cnstr_set(x_59, 3, x_57);
lean::cnstr_set_scalar(x_59, sizeof(void*)*4, x_2);
x_60 = x_59;
return x_60;
}
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
uint8 x_61; 
x_61 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
if (x_61 == 0)
{
obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_62 = lean::cnstr_get(x_1, 0);
x_64 = lean::cnstr_get(x_1, 1);
x_66 = lean::cnstr_get(x_1, 2);
x_68 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 x_70 = x_1;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::inc(x_66);
 lean::inc(x_68);
 lean::dec(x_1);
 x_70 = lean::box(0);
}
x_71 = l_RBNode_appendTrees___main___rarg(x_0, x_62);
if (lean::is_scalar(x_70)) {
 x_72 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_72 = x_70;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_64);
lean::cnstr_set(x_72, 2, x_66);
lean::cnstr_set(x_72, 3, x_68);
lean::cnstr_set_scalar(x_72, sizeof(void*)*4, x_61);
x_73 = x_72;
return x_73;
}
else
{
obj* x_74; obj* x_76; obj* x_78; obj* x_80; obj* x_82; obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_91; obj* x_92; 
x_74 = lean::cnstr_get(x_0, 0);
x_76 = lean::cnstr_get(x_0, 1);
x_78 = lean::cnstr_get(x_0, 2);
x_80 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_82 = x_0;
} else {
 lean::inc(x_74);
 lean::inc(x_76);
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_0);
 x_82 = lean::box(0);
}
x_83 = lean::cnstr_get(x_1, 0);
x_85 = lean::cnstr_get(x_1, 1);
x_87 = lean::cnstr_get(x_1, 2);
x_89 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_91 = x_1;
} else {
 lean::inc(x_83);
 lean::inc(x_85);
 lean::inc(x_87);
 lean::inc(x_89);
 lean::dec(x_1);
 x_91 = lean::box(0);
}
x_92 = l_RBNode_appendTrees___main___rarg(x_80, x_83);
if (lean::obj_tag(x_92) == 0)
{
obj* x_94; obj* x_95; obj* x_96; 
lean::dec(x_82);
if (lean::is_scalar(x_91)) {
 x_94 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_94 = x_91;
}
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set(x_94, 1, x_85);
lean::cnstr_set(x_94, 2, x_87);
lean::cnstr_set(x_94, 3, x_89);
lean::cnstr_set_scalar(x_94, sizeof(void*)*4, x_61);
x_95 = x_94;
x_96 = l_RBNode_balLeft___main___rarg(x_74, x_76, x_78, x_95);
return x_96;
}
else
{
uint8 x_97; 
x_97 = lean::cnstr_get_scalar<uint8>(x_92, sizeof(void*)*4);
if (x_97 == 0)
{
obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_98 = lean::cnstr_get(x_92, 0);
x_100 = lean::cnstr_get(x_92, 1);
x_102 = lean::cnstr_get(x_92, 2);
x_104 = lean::cnstr_get(x_92, 3);
if (lean::is_exclusive(x_92)) {
 x_106 = x_92;
} else {
 lean::inc(x_98);
 lean::inc(x_100);
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_92);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_74);
lean::cnstr_set(x_107, 1, x_76);
lean::cnstr_set(x_107, 2, x_78);
lean::cnstr_set(x_107, 3, x_98);
lean::cnstr_set_scalar(x_107, sizeof(void*)*4, x_61);
x_108 = x_107;
if (lean::is_scalar(x_91)) {
 x_109 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_109 = x_91;
}
lean::cnstr_set(x_109, 0, x_104);
lean::cnstr_set(x_109, 1, x_85);
lean::cnstr_set(x_109, 2, x_87);
lean::cnstr_set(x_109, 3, x_89);
lean::cnstr_set_scalar(x_109, sizeof(void*)*4, x_61);
x_110 = x_109;
if (lean::is_scalar(x_82)) {
 x_111 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_111 = x_82;
}
lean::cnstr_set(x_111, 0, x_108);
lean::cnstr_set(x_111, 1, x_100);
lean::cnstr_set(x_111, 2, x_102);
lean::cnstr_set(x_111, 3, x_110);
lean::cnstr_set_scalar(x_111, sizeof(void*)*4, x_97);
x_112 = x_111;
return x_112;
}
else
{
obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_82);
if (lean::is_scalar(x_91)) {
 x_114 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_114 = x_91;
}
lean::cnstr_set(x_114, 0, x_92);
lean::cnstr_set(x_114, 1, x_85);
lean::cnstr_set(x_114, 2, x_87);
lean::cnstr_set(x_114, 3, x_89);
lean::cnstr_set_scalar(x_114, sizeof(void*)*4, x_97);
x_115 = x_114;
x_116 = l_RBNode_balLeft___main___rarg(x_74, x_76, x_78, x_115);
return x_116;
}
}
}
}
}
}
}
}
obj* l_RBNode_appendTrees___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_appendTrees___main___rarg), 2, 0);
return x_2;
}
}
obj* l_RBNode_appendTrees___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_appendTrees___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_appendTrees___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_appendTrees___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_RBNode_appendTrees(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_appendTrees___rarg), 2, 0);
return x_2;
}
}
obj* l_RBNode_appendTrees___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_appendTrees(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_del___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_17; uint8 x_18; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
x_9 = lean::cnstr_get(x_2, 2);
x_11 = lean::cnstr_get(x_2, 3);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 lean::cnstr_set(x_2, 3, lean::box(0));
 x_13 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_2);
 x_13 = lean::box(0);
}
lean::inc(x_7);
lean::inc(x_1);
lean::inc(x_0);
x_17 = lean::apply_2(x_0, x_1, x_7);
x_18 = lean::unbox(x_17);
if (x_18 == 0)
{
obj* x_22; uint8 x_23; 
lean::inc(x_1);
lean::inc(x_7);
lean::inc(x_0);
x_22 = lean::apply_2(x_0, x_7, x_1);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_29; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_7);
lean::dec(x_13);
x_29 = l_RBNode_appendTrees___main___rarg(x_5, x_11);
return x_29;
}
else
{
uint8 x_30; 
x_30 = l_RBNode_isBlack___main___rarg(x_11);
if (x_30 == 0)
{
obj* x_31; uint8 x_32; obj* x_33; obj* x_34; 
x_31 = l_RBNode_del___main___rarg(x_0, x_1, x_11);
x_32 = 0;
if (lean::is_scalar(x_13)) {
 x_33 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_33 = x_13;
}
lean::cnstr_set(x_33, 0, x_5);
lean::cnstr_set(x_33, 1, x_7);
lean::cnstr_set(x_33, 2, x_9);
lean::cnstr_set(x_33, 3, x_31);
lean::cnstr_set_scalar(x_33, sizeof(void*)*4, x_32);
x_34 = x_33;
return x_34;
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_13);
x_36 = l_RBNode_del___main___rarg(x_0, x_1, x_11);
x_37 = l_RBNode_balRight___rarg(x_5, x_7, x_9, x_36);
return x_37;
}
}
}
else
{
uint8 x_38; 
x_38 = l_RBNode_isBlack___main___rarg(x_5);
if (x_38 == 0)
{
obj* x_39; uint8 x_40; obj* x_41; obj* x_42; 
x_39 = l_RBNode_del___main___rarg(x_0, x_1, x_5);
x_40 = 0;
if (lean::is_scalar(x_13)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_13;
}
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_7);
lean::cnstr_set(x_41, 2, x_9);
lean::cnstr_set(x_41, 3, x_11);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_40);
x_42 = x_41;
return x_42;
}
else
{
obj* x_44; obj* x_45; 
lean::dec(x_13);
x_44 = l_RBNode_del___main___rarg(x_0, x_1, x_5);
x_45 = l_RBNode_balLeft___main___rarg(x_44, x_7, x_9, x_11);
return x_45;
}
}
}
}
}
obj* l_RBNode_del___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_del___main___rarg), 3, 0);
return x_2;
}
}
obj* l_RBNode_del___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_del___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_del___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_del___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBNode_del(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_del___rarg), 3, 0);
return x_2;
}
}
obj* l_RBNode_del___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_del(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_erase___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_RBNode_del___main___rarg(x_0, x_1, x_2);
x_4 = l_RBNode_setBlack___main___rarg(x_3);
return x_4;
}
}
obj* l_RBNode_erase(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_erase___rarg), 3, 0);
return x_2;
}
}
obj* l_RBNode_erase___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_erase(x_0, x_1);
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
obj* x_4; 
x_4 = l_RBNode_insert___rarg(x_0, x_1, x_2, x_3);
return x_4;
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
obj* x_4; 
x_4 = l_RBNode_insert___rarg(x_0, x_1, x_2, x_3);
return x_4;
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
obj* l_RBMap_erase___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_erase___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_RBMap_erase___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_erase___main___rarg), 3, 0);
return x_2;
}
}
obj* l_RBMap_erase___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_erase___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_erase___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_erase___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_RBMap_erase(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_erase___rarg), 3, 0);
return x_2;
}
}
obj* l_RBMap_erase___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_erase(x_0, x_1);
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
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15; obj* x_16; 
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
x_16 = l_RBNode_insert___rarg(x_0, x_15, x_9, x_11);
return x_16;
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
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15; 
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
lean::inc(x_0);
x_15 = l_RBNode_insert___rarg(x_0, x_1, x_9, x_11);
x_1 = x_15;
x_2 = x_6;
goto _start;
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
obj* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 3);
x_4 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_0, x_2);
x_5 = lean::mk_nat_obj(1ul);
x_6 = lean::nat_add(x_4, x_5);
lean::dec(x_4);
x_0 = x_6;
x_1 = x_3;
goto _start;
}
}
}
obj* l_RBNode_fold___main___at_RBMap_size___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_fold___main___at_RBMap_size___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBMap_size___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_1, x_0);
return x_2;
}
}
obj* l_RBMap_size(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_size___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_RBNode_fold___main___at_RBMap_size___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_fold___main___at_RBMap_size___spec__1___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_fold___main___at_RBMap_size___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_fold___main___at_RBMap_size___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_size___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBMap_size___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBMap_size___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBMap_size(x_0, x_1, x_2);
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
obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_15; 
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
lean::inc(x_0);
x_15 = l_RBNode_insert___rarg(x_0, x_1, x_9, x_11);
x_1 = x_15;
x_2 = x_6;
goto _start;
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
