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
obj* l_RBNode_all___main___at_RBTree_subset___spec__4___boxed(obj*, obj*);
obj* l_RBTree_min___boxed(obj*, obj*);
obj* l_RBNode_ins___main___at_RBTree_insert___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_RBTree_HasEmptyc___boxed(obj*, obj*);
uint8 l_RBNode_all___main___at_RBTree_seteq___spec__10___rarg(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBTree_fromList___spec__5___boxed(obj*, obj*);
obj* l_RBNode_any___main___at_RBTree_any___spec__1(obj*);
obj* l_RBMap_findCore___main___at_RBTree_seteq___spec__3(obj*, obj*);
obj* l_RBNode_all___main___at_RBTree_seteq___spec__5(obj*, obj*);
obj* l_RBNode_ins___main___at_RBTree_insert___spec__3___boxed(obj*, obj*);
obj* l_RBNode_ins___main___at_RBTree_ofList___main___spec__4(obj*, obj*);
obj* l_RBNode_insert___at_RBTree_ofList___main___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_rbtreeOf___spec__4___boxed(obj*, obj*);
obj* l_rbtreeOf___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_rbtreeOf___spec__5(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBTree_insert___spec__4___boxed(obj*, obj*);
obj* l_RBTree_subset___at_RBTree_seteq___spec__6(obj*, obj*);
obj* l_RBTree_fromList___at_rbtreeOf___spec__1(obj*, obj*);
obj* l_RBMap_insert___main___at_rbtreeOf___spec__3___boxed(obj*, obj*);
obj* l_RBTree_find___boxed(obj*, obj*);
obj* l_RBNode_revFold___main___at_RBTree_revFold___spec__1___boxed(obj*, obj*);
obj* l_rbtreeOf___boxed(obj*);
obj* l_rbtreeOf(obj*);
obj* l_RBTree_insert___at_rbtreeOf___spec__2___boxed(obj*, obj*);
obj* l_RBNode_findCore___main___at_RBTree_seteq___spec__4___rarg(obj*, obj*, obj*);
uint8 l_Option_isSome___main___rarg(obj*);
obj* l_RBNode_ins___main___at_RBTree_ofList___main___spec__3___boxed(obj*, obj*);
obj* l_RBNode_all___main___at_RBTree_seteq___spec__5___rarg___boxed(obj*, obj*, obj*);
obj* l_RBTree_max___boxed(obj*, obj*);
obj* l_RBTree_ofList___main(obj*, obj*);
obj* l_RBNode_fold___main___at_RBTree_fold___spec__1(obj*, obj*);
obj* l_RBNode_findCore___main___at_RBTree_seteq___spec__4(obj*, obj*);
obj* l_RBTree_seteq___rarg___boxed(obj*, obj*, obj*);
obj* l_RBTree_toList(obj*, obj*);
obj* l_RBTree_subset___at_RBTree_seteq___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_RBTree_find___at_RBTree_seteq___spec__2___rarg(obj*, obj*, obj*);
obj* l_RBNode_all___main___at_RBTree_subset___spec__4___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_findCore___main___at_RBTree_seteq___spec__9___boxed(obj*, obj*);
obj* l_RBMap_findCore___main___at_RBTree_subset___spec__2(obj*, obj*);
obj* l_RBNode_findCore___main___at_RBTree_seteq___spec__9___rarg(obj*, obj*, obj*);
obj* l_RBTree_any___rarg___boxed(obj*, obj*);
obj* l_RBTree_isEmpty___rarg___boxed(obj*);
obj* l_RBNode_ins___main___at_rbtreeOf___spec__6___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBTree_fromList___spec__4(obj*, obj*);
uint8 l_RBTree_all___rarg(obj*, obj*);
obj* l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(obj*, obj*);
obj* l_RBMap_findCore___main___at_RBTree_find___spec__1___boxed(obj*, obj*);
obj* l_RBTree_min___rarg(obj*);
obj* l_RBTree_all___boxed(obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_RBTree_ofList___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1(obj*, obj*, obj*);
obj* l_RBMap_findCore___main___at_RBTree_seteq___spec__8___rarg(obj*, obj*, obj*);
obj* l_RBTree_depth___rarg___boxed(obj*, obj*);
obj* l_RBTree_fromList___rarg(obj*, obj*, obj*);
obj* l_RBNode_findCore___main___at_RBTree_subset___spec__3___boxed(obj*, obj*);
obj* l_RBTree_fromList___at_rbtreeOf___spec__1___boxed(obj*, obj*);
obj* l_RBNode_min___main___rarg(obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_max___main___rarg(obj*);
obj* l_RBNode_ins___main___at_RBTree_fromList___spec__4___boxed(obj*, obj*);
obj* l_RBNode_findCore___main___at_RBTree_seteq___spec__4___boxed(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_findCore___main___at_RBTree_seteq___spec__3___rarg(obj*, obj*, obj*);
obj* l_RBTree_contains___boxed(obj*, obj*);
obj* l_RBTree_toList___rarg(obj*);
obj* l_RBNode_ins___main___at_rbtreeOf___spec__5___boxed(obj*, obj*);
obj* l_RBTree_HasRepr___boxed(obj*, obj*);
obj* l_RBTree_find___at_RBTree_subset___spec__1___boxed(obj*, obj*);
obj* l_RBTree_subset___at_RBTree_seteq___spec__1(obj*, obj*);
obj* l_RBMap_findCore___main___at_RBTree_seteq___spec__8(obj*, obj*);
obj* l_RBNode_insert___at_RBTree_insert___spec__2___boxed(obj*, obj*);
obj* l_RBTree_find___at_RBTree_subset___spec__1(obj*, obj*);
obj* l_RBTree_find___at_RBTree_contains___spec__1(obj*, obj*);
obj* l_RBNode_depth___main___rarg(obj*, obj*);
obj* l_RBMap_findCore___main___at_RBTree_seteq___spec__3___boxed(obj*, obj*);
obj* l_RBMap_insert___main___at_rbtreeOf___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_revFold___main___at_RBTree_toList___spec__1(obj*);
obj* l_RBNode_ins___main___at_RBTree_ofList___main___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_rbtreeOf___spec__3(obj*, obj*);
obj* l_RBNode_ins___main___at_RBTree_ofList___main___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_RBTree_find___at_RBTree_contains___spec__1___rarg(obj*, obj*, obj*);
uint8 l_RBTree_any___rarg(obj*, obj*);
obj* l_RBNode_balance2___main___rarg(obj*, obj*);
obj* l_RBMap_insert___main___at_RBTree_ofList___main___spec__1___boxed(obj*, obj*);
obj* l_RBTree_fromList___rarg___boxed(obj*, obj*, obj*);
obj* l_RBMap_findCore___main___at_RBTree_contains___spec__2___rarg(obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_RBTree_fromList___spec__2___rarg(obj*, obj*, obj*, obj*);
uint8 l_RBTree_subset___at_RBTree_seteq___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBTree_HasRepr___rarg___closed__1;
obj* l_RBTree_insert___at_RBTree_fromList___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_rbtreeOf___spec__6___boxed(obj*, obj*);
obj* l_RBTree_insert___at_rbtreeOf___spec__2(obj*, obj*);
obj* l_List_foldl___main___at_RBTree_fromList___spec__6___boxed(obj*, obj*);
obj* l_RBTree_depth___boxed(obj*, obj*);
obj* l_RBTree_depth___rarg(obj*, obj*);
obj* l_RBTree_find(obj*, obj*);
obj* l_RBTree_find___rarg(obj*, obj*, obj*);
uint8 l_RBTree_contains___rarg(obj*, obj*, obj*);
obj* l_RBTree_subset___at_RBTree_seteq___spec__6___boxed(obj*, obj*);
obj* l_List_foldl___main___at_rbtreeOf___spec__7___boxed(obj*, obj*);
obj* l_RBNode_findCore___main___at_RBTree_find___spec__2___boxed(obj*, obj*);
obj* l_RBMap_insert___main___at_RBTree_insert___spec__1___boxed(obj*, obj*);
obj* l_RBTree_revFold___rarg(obj*, obj*, obj*);
obj* l_mkRBTree(obj*, obj*);
obj* l_RBTree_min(obj*, obj*);
uint8 l_RBNode_any___main___at_RBTree_any___spec__1___rarg(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_RBNode_findCore___main___at_RBTree_contains___spec__3___boxed(obj*, obj*);
obj* l_RBTree_find___at_RBTree_contains___spec__1___boxed(obj*, obj*);
obj* l_RBNode_findCore___main___at_RBTree_subset___spec__3(obj*, obj*);
obj* l_RBTree_contains___rarg___boxed(obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_RBTree_insert___spec__1(obj*, obj*);
uint8 l_RBTree_seteq___rarg(obj*, obj*, obj*);
obj* l_RBTree_fromList(obj*);
obj* l_RBMap_insert___main___at_RBTree_ofList___main___spec__1(obj*, obj*);
obj* l_RBMap_findCore___main___at_RBTree_contains___spec__2___boxed(obj*, obj*);
obj* l_RBTree_fromList___boxed(obj*);
obj* l_RBTree_subset___at_RBTree_seteq___spec__1___boxed(obj*, obj*);
obj* l_RBTree_seteq(obj*, obj*);
obj* l_RBTree_HasEmptyc(obj*, obj*);
obj* l_RBTree_insert___at_RBTree_fromList___spec__1___boxed(obj*, obj*);
obj* l_RBNode_all___main___at_RBTree_seteq___spec__10___rarg___boxed(obj*, obj*, obj*);
obj* l_RBTree_revFold___boxed(obj*, obj*, obj*);
obj* l_RBTree_find___at_RBTree_seteq___spec__7___boxed(obj*, obj*);
obj* l_RBNode_all___main___at_RBTree_seteq___spec__10___boxed(obj*, obj*);
uint8 l_Option_toBool___main___rarg(obj*);
obj* l_RBTree_isEmpty(obj*, obj*);
obj* l_List_foldl___main___at_rbtreeOf___spec__7(obj*, obj*);
obj* l_RBTree_mfold___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_revFold___main___at_RBTree_revFold___spec__1(obj*, obj*);
obj* l_RBTree_mfor___boxed(obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_RBTree_fromList___spec__6(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___boxed(obj*, obj*, obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_RBNode_findCore___main___at_RBTree_contains___spec__3___rarg(obj*, obj*, obj*);
obj* l_RBTree_HasRepr(obj*, obj*);
uint8 l_RBNode_all___main___at_RBTree_all___spec__1___rarg(obj*, obj*);
obj* l_RBNode_findCore___main___at_RBTree_contains___spec__3(obj*, obj*);
obj* l_RBMap_findCore___main___at_RBTree_find___spec__1(obj*, obj*);
obj* l_RBTree_revFold(obj*, obj*, obj*);
obj* l_RBNode_insert___at_RBTree_insert___spec__2(obj*, obj*);
obj* l_RBNode_findCore___main___at_RBTree_find___spec__2___rarg(obj*, obj*, obj*);
obj* l_RBTree_subset(obj*, obj*);
obj* l_RBNode_ins___main___at_RBTree_insert___spec__4(obj*, obj*);
obj* l_RBNode_ins___main___at_RBTree_fromList___spec__5___rarg(obj*, obj*, obj*, obj*);
obj* l_RBTree_subset___boxed(obj*, obj*);
obj* l_RBTree_any___boxed(obj*, obj*, obj*);
obj* l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBTree_any(obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_RBTree_fromList___spec__2___boxed(obj*, obj*);
obj* l_List_foldl___main___at_RBTree_fromList___spec__6___rarg(obj*, obj*, obj*);
obj* l_RBNode_all___main___at_RBTree_all___spec__1(obj*);
obj* l_RBNode_any___main___at_RBTree_any___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBMap_insert___main___at_RBTree_insert___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBTree_subset___rarg___boxed(obj*, obj*, obj*);
obj* l_RBNode_insert___at_rbtreeOf___spec__4___rarg(obj*, obj*, obj*, obj*);
uint8 l_RBNode_all___main___at_RBTree_subset___spec__4___rarg(obj*, obj*, obj*);
obj* l_RBNode_all___main___at_RBTree_seteq___spec__10(obj*, obj*);
obj* l_RBNode_insert___at_RBTree_ofList___main___spec__2___boxed(obj*, obj*);
obj* l_RBNode_ins___main___at_RBTree_ofList___main___spec__3(obj*, obj*);
obj* l_RBTree_mfold(obj*, obj*, obj*, obj*);
obj* l_RBNode_fold___main___at_RBTree_fold___spec__1___boxed(obj*, obj*);
obj* l_RBNode_ins___main___at_RBTree_fromList___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_RBTree_insert___rarg(obj*, obj*, obj*);
obj* l_RBTree_mfor(obj*, obj*, obj*, obj*);
obj* l_RBTree_find___at_RBTree_seteq___spec__7(obj*, obj*);
obj* l_RBNode_findCore___main___at_RBTree_find___spec__2(obj*, obj*);
obj* l_RBMap_findCore___main___at_RBTree_seteq___spec__8___boxed(obj*, obj*);
obj* l_RBNode_findCore___main___at_RBTree_seteq___spec__9(obj*, obj*);
obj* l_RBTree_fold___rarg(obj*, obj*, obj*);
obj* l_RBTree_insert___at_rbtreeOf___spec__2___rarg(obj*, obj*, obj*);
obj* l_RBMap_insert___main___at_RBTree_fromList___spec__2(obj*, obj*);
obj* l_RBTree_fold(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBTree_insert___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_all___main___at_RBTree_all___spec__1___rarg___boxed(obj*, obj*);
obj* l_RBTree_contains(obj*, obj*);
obj* l_RBTree_HasRepr___rarg(obj*, obj*);
uint8 l_RBTree_subset___rarg(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBTree_ofList___main___spec__4___boxed(obj*, obj*);
obj* l_RBTree_fromList___at_rbtreeOf___spec__1___rarg(obj*, obj*);
obj* l_RBMap_findCore___main___at_RBTree_find___spec__1___rarg(obj*, obj*, obj*);
obj* l_mkRBTree___boxed(obj*, obj*);
obj* l_rbtreeOf___rarg(obj*, obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1(obj*, obj*, obj*);
obj* l_RBNode_insert___at_RBTree_fromList___spec__3___boxed(obj*, obj*);
obj* l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBTree_all___rarg___boxed(obj*, obj*);
obj* l_List_foldl___main___at_rbtreeOf___spec__7___rarg(obj*, obj*, obj*);
obj* l_RBNode_insert___at_RBTree_insert___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_any___main___at_RBTree_any___spec__1___boxed(obj*);
obj* l_RBTree_find___at_RBTree_subset___spec__1___rarg(obj*, obj*, obj*);
obj* l_RBTree_ofList___main___rarg(obj*, obj*);
obj* l_RBMap_findCore___main___at_RBTree_subset___spec__2___boxed(obj*, obj*);
obj* l_RBTree_isEmpty___boxed(obj*, obj*);
uint8 l_RBNode_all___main___at_RBTree_seteq___spec__5___rarg(obj*, obj*, obj*);
obj* l_RBTree_max___rarg(obj*);
obj* l_RBTree_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_RBTree_insert(obj*, obj*);
obj* l_RBNode_revFold___main___at_RBTree_toList___spec__1___boxed(obj*);
uint8 l_RBTree_subset___at_RBTree_seteq___spec__6___rarg(obj*, obj*, obj*);
obj* l_RBNode_insert___at_rbtreeOf___spec__4(obj*, obj*);
uint8 l_RBTree_isEmpty___rarg(obj*);
obj* l_RBTree_ofList(obj*, obj*);
obj* l_RBNode_balance1___main___rarg(obj*, obj*);
obj* l_RBTree_ofList___main___boxed(obj*, obj*);
obj* l_RBNode_insert___at_RBTree_fromList___spec__3(obj*, obj*);
obj* l_RBTree_depth(obj*, obj*);
obj* l_RBMap_findCore___main___at_RBTree_subset___spec__2___rarg(obj*, obj*, obj*);
obj* l_RBTree_fold___boxed(obj*, obj*, obj*);
obj* l_RBTree_toList___boxed(obj*, obj*);
obj* l_RBTree_find___at_RBTree_seteq___spec__2(obj*, obj*);
obj* l_RBNode_ins___main___at_rbtreeOf___spec__5___rarg(obj*, obj*, obj*, obj*);
obj* l_RBTree_find___at_RBTree_seteq___spec__7___rarg(obj*, obj*, obj*);
obj* l_RBTree_ofList___rarg(obj*, obj*);
obj* l_RBNode_ins___main___at_RBTree_insert___spec__3(obj*, obj*);
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBTree_ofList___boxed(obj*, obj*);
obj* l_RBMap_findCore___main___at_RBTree_contains___spec__2(obj*, obj*);
obj* l_RBTree_mfor___rarg(obj*, obj*, obj*);
obj* l_RBTree_insert___boxed(obj*, obj*);
obj* l_RBTree_insert___at_RBTree_fromList___spec__1(obj*, obj*);
obj* l_RBTree_all(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_RBTree_fromList___spec__5(obj*, obj*);
obj* l_RBNode_findCore___main___at_RBTree_subset___spec__3___rarg(obj*, obj*, obj*);
obj* l_RBNode_insert___at_RBTree_fromList___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_RBNode_insert___at_RBTree_ofList___main___spec__2(obj*, obj*);
obj* l_RBTree_subset___at_RBTree_seteq___spec__6___rarg___boxed(obj*, obj*, obj*);
obj* l_List_repr___main___rarg(obj*, obj*);
obj* l_RBNode_all___main___at_RBTree_subset___spec__4(obj*, obj*);
obj* l_RBTree_max(obj*, obj*);
obj* l_RBNode_all___main___at_RBTree_all___spec__1___boxed(obj*);
obj* l_RBNode_all___main___at_RBTree_seteq___spec__5___boxed(obj*, obj*);
obj* l_RBNode_ins___main___at_rbtreeOf___spec__6(obj*, obj*);
obj* l_RBTree_find___at_RBTree_seteq___spec__2___boxed(obj*, obj*);
obj* l_RBTree_seteq___boxed(obj*, obj*);
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
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_12; obj* x_14; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = l_RBNode_fold___main___at_RBTree_fold___spec__1___rarg(x_0, x_4, x_2);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_6, x_12);
x_1 = x_8;
x_2 = x_14;
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
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_2;
}
else
{
obj* x_4; obj* x_6; obj* x_8; obj* x_12; obj* x_14; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 3);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_0);
x_12 = l_RBNode_revFold___main___at_RBTree_revFold___spec__1___rarg(x_0, x_8, x_2);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_6, x_12);
x_1 = x_4;
x_2 = x_14;
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
obj* l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_0);
x_7 = lean::apply_2(x_0, x_1, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg), 4, 3);
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_8; obj* x_11; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_2(x_8, lean::box(0), x_3);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_23; obj* x_25; obj* x_26; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_2, 3);
lean::inc(x_16);
lean::dec(x_2);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::inc(x_1);
lean::inc(x_0);
x_23 = l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg(x_0, x_1, x_12, x_3);
lean::inc(x_19);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfold___spec__1___rarg___lambda__1), 6, 5);
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
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg), 4, 3);
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_8; obj* x_11; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_2(x_8, lean::box(0), x_3);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_23; obj* x_25; obj* x_26; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_2, 3);
lean::inc(x_16);
lean::dec(x_2);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::inc(x_1);
lean::inc(x_0);
x_23 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(x_0, x_1, x_12, x_3);
lean::inc(x_19);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__1___boxed), 6, 5);
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
x_4 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg(x_0, x_1, x_2, x_3);
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
obj* l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_RBNode_mfold___main___at_RBTree_mfor___spec__1___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5);
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
if (lean::obj_tag(x_0) == 0)
{
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 3);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(x_6, x_1);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
x_0 = x_2;
x_1 = x_10;
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
x_2 = l_RBNode_revFold___main___at_RBTree_toList___spec__1___rarg(x_0, x_1);
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
obj* l_RBNode_ins___main___at_RBTree_insert___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_33 = l_RBNode_ins___main___at_RBTree_insert___spec__3___rarg(x_0, x_15, x_2, x_3);
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
x_36 = l_RBNode_ins___main___at_RBTree_insert___spec__3___rarg(x_0, x_9, x_2, x_3);
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
x_64 = l_RBNode_ins___main___at_RBTree_insert___spec__3___rarg(x_0, x_45, x_2, x_3);
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
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_RBTree_insert___spec__3___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_RBTree_insert___spec__3___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_RBTree_insert___spec__3___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_RBTree_insert___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_RBTree_insert___spec__3___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at_RBTree_insert___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_33 = l_RBNode_ins___main___at_RBTree_insert___spec__4___rarg(x_0, x_15, x_2, x_3);
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
x_36 = l_RBNode_ins___main___at_RBTree_insert___spec__4___rarg(x_0, x_9, x_2, x_3);
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
x_64 = l_RBNode_ins___main___at_RBTree_insert___spec__4___rarg(x_0, x_45, x_2, x_3);
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
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_RBTree_insert___spec__4___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_RBTree_insert___spec__4___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_RBTree_insert___spec__4___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_RBTree_insert___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_RBTree_insert___spec__4___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_insert___at_RBTree_insert___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_RBTree_insert___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_RBTree_insert___spec__4___rarg(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert___at_RBTree_insert___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at_RBTree_insert___spec__2___rarg), 4, 0);
return x_2;
}
}
obj* l_RBMap_insert___main___at_RBTree_insert___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_RBTree_insert___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_insert___main___at_RBTree_insert___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_insert___main___at_RBTree_insert___spec__1___rarg), 4, 0);
return x_2;
}
}
obj* l_RBTree_insert___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_RBNode_insert___at_RBTree_insert___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBTree_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_insert___rarg), 3, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at_RBTree_insert___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_ins___main___at_RBTree_insert___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_ins___main___at_RBTree_insert___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_ins___main___at_RBTree_insert___spec__4(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_insert___at_RBTree_insert___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_insert___at_RBTree_insert___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_insert___main___at_RBTree_insert___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_insert___main___at_RBTree_insert___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_insert___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_insert(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_ins___main___at_RBTree_ofList___main___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_33 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__3___rarg(x_0, x_15, x_2, x_3);
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
x_36 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__3___rarg(x_0, x_9, x_2, x_3);
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
x_64 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__3___rarg(x_0, x_45, x_2, x_3);
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
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__3___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__3___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__3___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_RBTree_ofList___main___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_RBTree_ofList___main___spec__3___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at_RBTree_ofList___main___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_33 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__4___rarg(x_0, x_15, x_2, x_3);
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
x_36 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__4___rarg(x_0, x_9, x_2, x_3);
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
x_64 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__4___rarg(x_0, x_45, x_2, x_3);
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
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__4___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__4___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__4___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_RBTree_ofList___main___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_RBTree_ofList___main___spec__4___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_insert___at_RBTree_ofList___main___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__4___rarg(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert___at_RBTree_ofList___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at_RBTree_ofList___main___spec__2___rarg), 4, 0);
return x_2;
}
}
obj* l_RBMap_insert___main___at_RBTree_ofList___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_RBTree_ofList___main___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_insert___main___at_RBTree_ofList___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_insert___main___at_RBTree_ofList___main___spec__1___rarg), 4, 0);
return x_2;
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
obj* x_4; obj* x_6; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
lean::inc(x_0);
x_10 = l_RBTree_ofList___main___rarg(x_0, x_6);
x_11 = lean::box(0);
x_12 = l_RBNode_insert___at_RBTree_ofList___main___spec__2___rarg(x_0, x_10, x_4, x_11);
return x_12;
}
}
}
obj* l_RBTree_ofList___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_ofList___main___rarg), 2, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at_RBTree_ofList___main___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_ins___main___at_RBTree_ofList___main___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_ins___main___at_RBTree_ofList___main___spec__4(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_insert___at_RBTree_ofList___main___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_insert___at_RBTree_ofList___main___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_insert___main___at_RBTree_ofList___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_insert___main___at_RBTree_ofList___main___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_ofList___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_ofList___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* l_RBTree_ofList(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_ofList___rarg), 2, 0);
return x_2;
}
}
obj* l_RBTree_ofList___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_ofList(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_findCore___main___at_RBTree_find___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_RBNode_findCore___main___at_RBTree_find___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_findCore___main___at_RBTree_find___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_RBMap_findCore___main___at_RBTree_find___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at_RBTree_find___spec__2___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_findCore___main___at_RBTree_find___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_findCore___main___at_RBTree_find___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_RBTree_find___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at_RBTree_find___spec__2___rarg(x_0, x_1, x_2);
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
obj* l_RBTree_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_find___rarg), 3, 0);
return x_2;
}
}
obj* l_RBNode_findCore___main___at_RBTree_find___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_findCore___main___at_RBTree_find___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_findCore___main___at_RBTree_find___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_findCore___main___at_RBTree_find___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_findCore___main___at_RBTree_contains___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_RBNode_findCore___main___at_RBTree_contains___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_findCore___main___at_RBTree_contains___spec__3___rarg), 3, 0);
return x_2;
}
}
obj* l_RBMap_findCore___main___at_RBTree_contains___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at_RBTree_contains___spec__3___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_findCore___main___at_RBTree_contains___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_findCore___main___at_RBTree_contains___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_RBTree_find___at_RBTree_contains___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at_RBTree_contains___spec__3___rarg(x_0, x_1, x_2);
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
obj* l_RBTree_find___at_RBTree_contains___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_find___at_RBTree_contains___spec__1___rarg), 3, 0);
return x_2;
}
}
uint8 l_RBTree_contains___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_RBTree_find___at_RBTree_contains___spec__1___rarg(x_0, x_1, x_2);
x_4 = l_Option_isSome___main___rarg(x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_RBTree_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_contains___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBNode_findCore___main___at_RBTree_contains___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_findCore___main___at_RBTree_contains___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_findCore___main___at_RBTree_contains___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_findCore___main___at_RBTree_contains___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_find___at_RBTree_contains___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_find___at_RBTree_contains___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* l_RBTree_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_contains(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_ins___main___at_RBTree_fromList___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_33 = l_RBNode_ins___main___at_RBTree_fromList___spec__4___rarg(x_0, x_15, x_2, x_3);
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
x_36 = l_RBNode_ins___main___at_RBTree_fromList___spec__4___rarg(x_0, x_9, x_2, x_3);
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
x_64 = l_RBNode_ins___main___at_RBTree_fromList___spec__4___rarg(x_0, x_45, x_2, x_3);
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
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_RBTree_fromList___spec__4___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_RBTree_fromList___spec__4___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_RBTree_fromList___spec__4___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_RBTree_fromList___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_RBTree_fromList___spec__4___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at_RBTree_fromList___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_33 = l_RBNode_ins___main___at_RBTree_fromList___spec__5___rarg(x_0, x_15, x_2, x_3);
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
x_36 = l_RBNode_ins___main___at_RBTree_fromList___spec__5___rarg(x_0, x_9, x_2, x_3);
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
x_64 = l_RBNode_ins___main___at_RBTree_fromList___spec__5___rarg(x_0, x_45, x_2, x_3);
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
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_RBTree_fromList___spec__5___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_RBTree_fromList___spec__5___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_RBTree_fromList___spec__5___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_RBTree_fromList___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_RBTree_fromList___spec__5___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_insert___at_RBTree_fromList___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_RBTree_fromList___spec__4___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_RBTree_fromList___spec__5___rarg(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert___at_RBTree_fromList___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at_RBTree_fromList___spec__3___rarg), 4, 0);
return x_2;
}
}
obj* l_RBMap_insert___main___at_RBTree_fromList___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_RBTree_fromList___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_insert___main___at_RBTree_fromList___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_insert___main___at_RBTree_fromList___spec__2___rarg), 4, 0);
return x_2;
}
}
obj* l_RBTree_insert___at_RBTree_fromList___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_RBNode_insert___at_RBTree_fromList___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBTree_insert___at_RBTree_fromList___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_insert___at_RBTree_fromList___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_List_foldl___main___at_RBTree_fromList___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::box(0);
lean::inc(x_0);
x_11 = l_RBNode_insert___at_RBTree_fromList___spec__3___rarg(x_0, x_1, x_4, x_9);
x_1 = x_11;
x_2 = x_6;
goto _start;
}
}
}
obj* l_List_foldl___main___at_RBTree_fromList___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_RBTree_fromList___spec__6___rarg), 3, 0);
return x_2;
}
}
obj* l_RBTree_fromList___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_List_foldl___main___at_RBTree_fromList___spec__6___rarg(x_2, x_3, x_0);
return x_4;
}
}
obj* l_RBTree_fromList(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_fromList___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_RBNode_ins___main___at_RBTree_fromList___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_ins___main___at_RBTree_fromList___spec__4(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_ins___main___at_RBTree_fromList___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_ins___main___at_RBTree_fromList___spec__5(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_insert___at_RBTree_fromList___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_insert___at_RBTree_fromList___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_insert___main___at_RBTree_fromList___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_insert___main___at_RBTree_fromList___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_insert___at_RBTree_fromList___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_insert___at_RBTree_fromList___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_foldl___main___at_RBTree_fromList___spec__6___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldl___main___at_RBTree_fromList___spec__6(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_fromList___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_fromList___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
lean::dec(x_4);
if (x_13 == 0)
{
lean::dec(x_8);
lean::dec(x_0);
return x_13;
}
else
{
x_1 = x_8;
goto _start;
}
}
else
{
uint8 x_19; 
lean::inc(x_0);
x_19 = l_RBNode_all___main___at_RBTree_all___spec__1___rarg(x_0, x_4);
if (x_19 == 0)
{
lean::dec(x_8);
lean::dec(x_0);
return x_19;
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
obj* l_RBTree_all(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_all___rarg___boxed), 2, 0);
return x_3;
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
obj* l_RBTree_all___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_all(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
lean::dec(x_8);
lean::dec(x_0);
return x_15;
}
}
else
{
lean::dec(x_4);
if (x_13 == 0)
{
x_1 = x_8;
goto _start;
}
else
{
lean::dec(x_8);
lean::dec(x_0);
return x_13;
}
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
obj* l_RBTree_any(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_any___rarg___boxed), 2, 0);
return x_3;
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
obj* l_RBTree_any___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_any(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_RBNode_findCore___main___at_RBTree_subset___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_RBNode_findCore___main___at_RBTree_subset___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_findCore___main___at_RBTree_subset___spec__3___rarg), 3, 0);
return x_2;
}
}
obj* l_RBMap_findCore___main___at_RBTree_subset___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at_RBTree_subset___spec__3___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_findCore___main___at_RBTree_subset___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_findCore___main___at_RBTree_subset___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_RBTree_find___at_RBTree_subset___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at_RBTree_subset___spec__3___rarg(x_0, x_1, x_2);
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
obj* l_RBTree_find___at_RBTree_subset___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_find___at_RBTree_subset___spec__1___rarg), 3, 0);
return x_2;
}
}
uint8 l_RBNode_all___main___at_RBTree_subset___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_6; obj* x_8; obj* x_10; obj* x_15; uint8 x_16; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 3);
lean::inc(x_10);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_15 = l_RBTree_find___at_RBTree_subset___spec__1___rarg(x_0, x_1, x_8);
x_16 = l_Option_toBool___main___rarg(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
lean::dec(x_6);
if (x_16 == 0)
{
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_0);
return x_16;
}
else
{
x_2 = x_10;
goto _start;
}
}
else
{
uint8 x_25; 
lean::inc(x_1);
lean::inc(x_0);
x_25 = l_RBNode_all___main___at_RBTree_subset___spec__4___rarg(x_0, x_1, x_6);
if (x_25 == 0)
{
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_0);
return x_25;
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
obj* l_RBNode_all___main___at_RBTree_subset___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_all___main___at_RBTree_subset___spec__4___rarg___boxed), 3, 0);
return x_2;
}
}
uint8 l_RBTree_subset___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_all___main___at_RBTree_subset___spec__4___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_RBTree_subset(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_subset___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBNode_findCore___main___at_RBTree_subset___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_findCore___main___at_RBTree_subset___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_findCore___main___at_RBTree_subset___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_findCore___main___at_RBTree_subset___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_find___at_RBTree_subset___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_find___at_RBTree_subset___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_all___main___at_RBTree_subset___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBNode_all___main___at_RBTree_subset___spec__4___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBNode_all___main___at_RBTree_subset___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_all___main___at_RBTree_subset___spec__4(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* l_RBTree_subset___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_subset(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_findCore___main___at_RBTree_seteq___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_RBNode_findCore___main___at_RBTree_seteq___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_findCore___main___at_RBTree_seteq___spec__4___rarg), 3, 0);
return x_2;
}
}
obj* l_RBMap_findCore___main___at_RBTree_seteq___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at_RBTree_seteq___spec__4___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_findCore___main___at_RBTree_seteq___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_findCore___main___at_RBTree_seteq___spec__3___rarg), 3, 0);
return x_2;
}
}
obj* l_RBTree_find___at_RBTree_seteq___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at_RBTree_seteq___spec__4___rarg(x_0, x_1, x_2);
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
obj* l_RBTree_find___at_RBTree_seteq___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_find___at_RBTree_seteq___spec__2___rarg), 3, 0);
return x_2;
}
}
uint8 l_RBNode_all___main___at_RBTree_seteq___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_6; obj* x_8; obj* x_10; obj* x_15; uint8 x_16; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 3);
lean::inc(x_10);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_15 = l_RBTree_find___at_RBTree_seteq___spec__2___rarg(x_0, x_1, x_8);
x_16 = l_Option_toBool___main___rarg(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
lean::dec(x_6);
if (x_16 == 0)
{
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_0);
return x_16;
}
else
{
x_2 = x_10;
goto _start;
}
}
else
{
uint8 x_25; 
lean::inc(x_1);
lean::inc(x_0);
x_25 = l_RBNode_all___main___at_RBTree_seteq___spec__5___rarg(x_0, x_1, x_6);
if (x_25 == 0)
{
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_0);
return x_25;
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
obj* l_RBNode_all___main___at_RBTree_seteq___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_all___main___at_RBTree_seteq___spec__5___rarg___boxed), 3, 0);
return x_2;
}
}
uint8 l_RBTree_subset___at_RBTree_seteq___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_all___main___at_RBTree_seteq___spec__5___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_RBTree_subset___at_RBTree_seteq___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_subset___at_RBTree_seteq___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBNode_findCore___main___at_RBTree_seteq___spec__9___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* l_RBNode_findCore___main___at_RBTree_seteq___spec__9(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_findCore___main___at_RBTree_seteq___spec__9___rarg), 3, 0);
return x_2;
}
}
obj* l_RBMap_findCore___main___at_RBTree_seteq___spec__8___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at_RBTree_seteq___spec__9___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_RBMap_findCore___main___at_RBTree_seteq___spec__8(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_findCore___main___at_RBTree_seteq___spec__8___rarg), 3, 0);
return x_2;
}
}
obj* l_RBTree_find___at_RBTree_seteq___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at_RBTree_seteq___spec__9___rarg(x_0, x_1, x_2);
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
obj* l_RBTree_find___at_RBTree_seteq___spec__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_find___at_RBTree_seteq___spec__7___rarg), 3, 0);
return x_2;
}
}
uint8 l_RBNode_all___main___at_RBTree_seteq___spec__10___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_6; obj* x_8; obj* x_10; obj* x_15; uint8 x_16; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 3);
lean::inc(x_10);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_15 = l_RBTree_find___at_RBTree_seteq___spec__7___rarg(x_0, x_1, x_8);
x_16 = l_Option_toBool___main___rarg(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
lean::dec(x_6);
if (x_16 == 0)
{
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_0);
return x_16;
}
else
{
x_2 = x_10;
goto _start;
}
}
else
{
uint8 x_25; 
lean::inc(x_1);
lean::inc(x_0);
x_25 = l_RBNode_all___main___at_RBTree_seteq___spec__10___rarg(x_0, x_1, x_6);
if (x_25 == 0)
{
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_0);
return x_25;
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
obj* l_RBNode_all___main___at_RBTree_seteq___spec__10(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_all___main___at_RBTree_seteq___spec__10___rarg___boxed), 3, 0);
return x_2;
}
}
uint8 l_RBTree_subset___at_RBTree_seteq___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_all___main___at_RBTree_seteq___spec__10___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_RBTree_subset___at_RBTree_seteq___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_subset___at_RBTree_seteq___spec__6___rarg___boxed), 3, 0);
return x_2;
}
}
uint8 l_RBTree_seteq___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_6; 
lean::inc(x_1);
lean::inc(x_2);
lean::inc(x_0);
x_6 = l_RBNode_all___main___at_RBTree_seteq___spec__5___rarg(x_0, x_2, x_1);
if (x_6 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_6;
}
else
{
uint8 x_10; 
x_10 = l_RBNode_all___main___at_RBTree_seteq___spec__10___rarg(x_0, x_1, x_2);
return x_10;
}
}
}
obj* l_RBTree_seteq(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_seteq___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_RBNode_findCore___main___at_RBTree_seteq___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_findCore___main___at_RBTree_seteq___spec__4(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_findCore___main___at_RBTree_seteq___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_findCore___main___at_RBTree_seteq___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_find___at_RBTree_seteq___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_find___at_RBTree_seteq___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_all___main___at_RBTree_seteq___spec__5___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBNode_all___main___at_RBTree_seteq___spec__5___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBNode_all___main___at_RBTree_seteq___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_all___main___at_RBTree_seteq___spec__5(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_subset___at_RBTree_seteq___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBTree_subset___at_RBTree_seteq___spec__1___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBTree_subset___at_RBTree_seteq___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_subset___at_RBTree_seteq___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_findCore___main___at_RBTree_seteq___spec__9___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_findCore___main___at_RBTree_seteq___spec__9(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_findCore___main___at_RBTree_seteq___spec__8___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_findCore___main___at_RBTree_seteq___spec__8(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_find___at_RBTree_seteq___spec__7___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_find___at_RBTree_seteq___spec__7(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_all___main___at_RBTree_seteq___spec__10___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBNode_all___main___at_RBTree_seteq___spec__10___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBNode_all___main___at_RBTree_seteq___spec__10___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_all___main___at_RBTree_seteq___spec__10(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_subset___at_RBTree_seteq___spec__6___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_RBTree_subset___at_RBTree_seteq___spec__6___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_RBTree_subset___at_RBTree_seteq___spec__6___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_subset___at_RBTree_seteq___spec__6(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
obj* l_RBTree_seteq___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_seteq(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_ins___main___at_rbtreeOf___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_33 = l_RBNode_ins___main___at_rbtreeOf___spec__5___rarg(x_0, x_15, x_2, x_3);
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
x_36 = l_RBNode_ins___main___at_rbtreeOf___spec__5___rarg(x_0, x_9, x_2, x_3);
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
x_64 = l_RBNode_ins___main___at_rbtreeOf___spec__5___rarg(x_0, x_45, x_2, x_3);
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
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_rbtreeOf___spec__5___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_rbtreeOf___spec__5___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_rbtreeOf___spec__5___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_rbtreeOf___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_rbtreeOf___spec__5___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_ins___main___at_rbtreeOf___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_33 = l_RBNode_ins___main___at_rbtreeOf___spec__6___rarg(x_0, x_15, x_2, x_3);
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
x_36 = l_RBNode_ins___main___at_rbtreeOf___spec__6___rarg(x_0, x_9, x_2, x_3);
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
x_64 = l_RBNode_ins___main___at_rbtreeOf___spec__6___rarg(x_0, x_45, x_2, x_3);
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
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_67 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_68 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_68 = x_47;
}
lean::cnstr_set(x_68, 0, x_39);
lean::cnstr_set(x_68, 1, x_41);
lean::cnstr_set(x_68, 2, x_43);
lean::cnstr_set(x_68, 3, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*4, x_8);
x_69 = x_68;
x_70 = l_RBNode_ins___main___at_rbtreeOf___spec__6___rarg(x_0, x_45, x_2, x_3);
x_71 = l_RBNode_balance2___main___rarg(x_69, x_70);
return x_71;
}
}
}
else
{
uint8 x_72; 
x_72 = l_RBNode_isRed___main___rarg(x_39);
if (x_72 == 0)
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = l_RBNode_ins___main___at_rbtreeOf___spec__6___rarg(x_0, x_39, x_2, x_3);
if (lean::is_scalar(x_47)) {
 x_74 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_74 = x_47;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_41);
lean::cnstr_set(x_74, 2, x_43);
lean::cnstr_set(x_74, 3, x_45);
lean::cnstr_set_scalar(x_74, sizeof(void*)*4, x_8);
x_75 = x_74;
return x_75;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_76 = lean::box(0);
if (lean::is_scalar(x_47)) {
 x_77 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_77 = x_47;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_41);
lean::cnstr_set(x_77, 2, x_43);
lean::cnstr_set(x_77, 3, x_45);
lean::cnstr_set_scalar(x_77, sizeof(void*)*4, x_8);
x_78 = x_77;
x_79 = l_RBNode_ins___main___at_rbtreeOf___spec__6___rarg(x_0, x_39, x_2, x_3);
x_80 = l_RBNode_balance1___main___rarg(x_78, x_79);
return x_80;
}
}
}
}
}
}
obj* l_RBNode_ins___main___at_rbtreeOf___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_ins___main___at_rbtreeOf___spec__6___rarg), 4, 0);
return x_2;
}
}
obj* l_RBNode_insert___at_rbtreeOf___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_RBNode_isRed___main___rarg(x_1);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_RBNode_ins___main___at_rbtreeOf___spec__5___rarg(x_0, x_1, x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = l_RBNode_ins___main___at_rbtreeOf___spec__6___rarg(x_0, x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___main___rarg(x_6);
return x_7;
}
}
}
obj* l_RBNode_insert___at_rbtreeOf___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_insert___at_rbtreeOf___spec__4___rarg), 4, 0);
return x_2;
}
}
obj* l_RBMap_insert___main___at_rbtreeOf___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_RBNode_insert___at_rbtreeOf___spec__4___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBMap_insert___main___at_rbtreeOf___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_insert___main___at_rbtreeOf___spec__3___rarg), 4, 0);
return x_2;
}
}
obj* l_RBTree_insert___at_rbtreeOf___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_RBNode_insert___at_rbtreeOf___spec__4___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_RBTree_insert___at_rbtreeOf___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_insert___at_rbtreeOf___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_List_foldl___main___at_rbtreeOf___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_9 = lean::box(0);
lean::inc(x_0);
x_11 = l_RBNode_insert___at_rbtreeOf___spec__4___rarg(x_0, x_1, x_4, x_9);
x_1 = x_11;
x_2 = x_6;
goto _start;
}
}
}
obj* l_List_foldl___main___at_rbtreeOf___spec__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_foldl___main___at_rbtreeOf___spec__7___rarg), 3, 0);
return x_2;
}
}
obj* l_RBTree_fromList___at_rbtreeOf___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_List_foldl___main___at_rbtreeOf___spec__7___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_RBTree_fromList___at_rbtreeOf___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBTree_fromList___at_rbtreeOf___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_rbtreeOf___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBTree_fromList___at_rbtreeOf___spec__1___rarg(x_2, x_0);
return x_3;
}
}
obj* l_rbtreeOf(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtreeOf___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_RBNode_ins___main___at_rbtreeOf___spec__5___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_ins___main___at_rbtreeOf___spec__5(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_ins___main___at_rbtreeOf___spec__6___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_ins___main___at_rbtreeOf___spec__6(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_insert___at_rbtreeOf___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_insert___at_rbtreeOf___spec__4(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_insert___main___at_rbtreeOf___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_insert___main___at_rbtreeOf___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_insert___at_rbtreeOf___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_insert___at_rbtreeOf___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_foldl___main___at_rbtreeOf___spec__7___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_foldl___main___at_rbtreeOf___spec__7(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBTree_fromList___at_rbtreeOf___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBTree_fromList___at_rbtreeOf___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbtreeOf___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbtreeOf___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
