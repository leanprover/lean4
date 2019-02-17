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
obj* l_rbtree_min(obj*, obj*);
obj* l_rbnode_all___main___at_rbtree_seteq___spec__5___rarg(obj*, obj*, obj*);
obj* l_rbnode_all___main___at_rbtree_seteq___spec__10___rarg(obj*, obj*, obj*);
obj* l_rbtree_fold(obj*, obj*, obj*);
obj* l_list_repr___main___rarg(obj*, obj*);
obj* l_rbnode_rev__fold___main___at_rbtree_to__list___spec__1(obj*);
obj* l_rbtree_find___at_rbtree_seteq___spec__2(obj*, obj*);
obj* l_rbmap_find__core___main___at_rbtree_find___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbtree_subset___rarg(obj*, obj*, obj*);
obj* l_rbmap_find__core___main___at_rbtree_subset___spec__2(obj*, obj*);
obj* l_rbtree_depth(obj*, obj*);
obj* l_rbtree_seteq___rarg(obj*, obj*, obj*);
obj* l_rbnode_all___main___at_rbtree_seteq___spec__10(obj*, obj*);
obj* l_rbtree_mfold(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbtree_insert___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_rev__fold___main___at_rbtree_rev__fold___spec__1(obj*, obj*);
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbtree_find___at_rbtree_contains___spec__1(obj*, obj*);
obj* l_rbmap_find__core___main___at_rbtree_contains___spec__2(obj*, obj*);
obj* l_rbtree_find(obj*, obj*);
obj* l_rbnode_all___main___at_rbtree_all___spec__1___rarg(obj*, obj*);
obj* l_list_foldl___main___at_rbtree_from__list___spec__5(obj*, obj*);
obj* l_rbnode_rev__fold___main___at_rbtree_rev__fold___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbtree_max___rarg(obj*);
obj* l_rbnode_find__core___main___at_rbtree_contains___spec__3(obj*, obj*);
obj* l_rbnode_all___main___at_rbtree_seteq___spec__5(obj*, obj*);
obj* l_rbnode_mfold___main___at_rbtree_mfold___spec__1(obj*, obj*, obj*);
obj* l_rbnode_mfold___main___at_rbtree_mfold___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbtree__of___rarg(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbtree_insert___spec__3(obj*, obj*);
obj* l_rbnode_find__core___main___at_rbtree_find___spec__2(obj*, obj*);
obj* l_rbtree_from__list___at_rbtree__of___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbnode_min___main___rarg(obj*);
obj* l_rbtree_of__list___main___rarg(obj*, obj*);
obj* l_rbmap_insert___main___at_rbtree_from__list___spec__2(obj*, obj*);
obj* l_rbnode_find__core___main___at_rbtree_seteq___spec__4(obj*, obj*);
obj* l_rbtree_from__list___at_rbtree__of___spec__1(obj*);
obj* l_rbtree_insert(obj*, obj*);
obj* l_rbtree_from__list___rarg(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbtree_insert___spec__1(obj*, obj*);
obj* l_rbnode_insert___at_rbtree_from__list___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_find__core___main___at_rbtree_subset___spec__2___rarg(obj*, obj*, obj*);
obj* l_rbtree_insert___at_rbtree_from__list___spec__1(obj*, obj*);
obj* l_rbmap_find__core___main___at_rbtree_seteq___spec__3(obj*, obj*);
obj* l_rbtree_find___rarg(obj*, obj*, obj*);
obj* l_rbnode_find__core___main___at_rbtree_find___spec__2___rarg(obj*, obj*, obj*);
obj* l_rbnode_depth___main___rarg(obj*, obj*);
obj* l_rbmap_find__core___main___at_rbtree_contains___spec__2___rarg(obj*, obj*, obj*);
obj* l_rbnode_all___main___at_rbtree_subset___spec__4(obj*, obj*);
obj* l_rbtree_empty___rarg___boxed(obj*);
obj* l_rbnode_insert___at_rbtree_of__list___main___spec__2(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
uint8 l_option_to__bool___main___rarg(obj*);
obj* l_rbtree_subset___at_rbtree_seteq___spec__6(obj*, obj*);
obj* l_rbtree_find___at_rbtree_seteq___spec__7(obj*, obj*);
obj* l_rbtree_empty(obj*, obj*);
obj* l_rbnode_ins___main___at_rbtree_of__list___main___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbtree__of___spec__5(obj*, obj*);
obj* l_rbnode_mk__insert__result___main___rarg(uint8, obj*);
obj* l_rbtree_contains(obj*, obj*);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_rbnode_all___main___at_rbtree_subset___spec__4___rarg(obj*, obj*, obj*);
obj* l_rbtree_of__list___rarg(obj*, obj*);
uint8 l_rbtree_contains___rarg(obj*, obj*, obj*);
obj* l_rbtree_of__list___main(obj*, obj*);
obj* l_rbtree_find___at_rbtree_seteq___spec__7___rarg(obj*, obj*, obj*);
obj* l_rbtree_insert___at_rbtree__of___spec__2___rarg(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_rbtree_of__list___main___spec__1(obj*, obj*);
obj* l_mk__rbtree(obj*, obj*);
obj* l_rbtree__of(obj*);
obj* l_rbnode_find__core___main___at_rbtree_seteq___spec__9(obj*, obj*);
obj* l_rbnode_find__core___main___at_rbtree_contains___spec__3___rarg(obj*, obj*, obj*);
obj* l_rbmap_find__core___main___at_rbtree_seteq___spec__8(obj*, obj*);
obj* l_rbmap_find__core___main___at_rbtree_find___spec__1(obj*, obj*);
obj* l_rbtree;
obj* l_rbtree_to__list(obj*, obj*);
obj* l_rbtree_find___at_rbtree_seteq___spec__2___rarg(obj*, obj*, obj*);
obj* l_rbnode_mfold___main___at_rbtree_mfor___spec__1(obj*, obj*, obj*);
obj* l_rbtree_insert___at_rbtree_from__list___spec__1___rarg(obj*, obj*, obj*);
obj* l_list_foldl___main___at_rbtree__of___spec__6(obj*, obj*);
obj* l_rbtree_depth___rarg(obj*, obj*);
obj* l_rbnode_rev__fold___main___at_rbtree_to__list___spec__1___rarg(obj*, obj*);
obj* l_rbtree_subset___at_rbtree_seteq___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbtree_insert___rarg(obj*, obj*, obj*);
obj* l_rbmap_find__core___main___at_rbtree_seteq___spec__3___rarg(obj*, obj*, obj*);
obj* l_rbnode_any___main___at_rbtree_any___spec__1___rarg(obj*, obj*);
obj* l_rbtree_has__repr(obj*, obj*);
obj* l_rbtree_subset___at_rbtree_seteq___spec__1(obj*, obj*);
obj* l_rbnode_find__core___main___at_rbtree_subset___spec__3(obj*, obj*);
obj* l_rbtree_min___rarg(obj*);
obj* l_rbmap_insert___main___at_rbtree_from__list___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbtree_insert___spec__2(obj*, obj*);
obj* l_rbnode_find__core___main___at_rbtree_seteq___spec__9___rarg(obj*, obj*, obj*);
obj* l_rbtree_find___at_rbtree_subset___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbtree_from__list(obj*);
obj* l_rbnode_ins___main___at_rbtree_insert___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_fold___main___at_rbtree_fold___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbnode_any___main___at_rbtree_any___spec__1(obj*);
obj* l_rbtree_subset(obj*, obj*);
obj* l_rbtree_all___rarg(obj*, obj*);
obj* l_rbtree_rev__fold(obj*, obj*, obj*);
obj* l_rbmap_find__core___main___at_rbtree_seteq___spec__8___rarg(obj*, obj*, obj*);
obj* l_rbtree_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_rbtree_any___rarg(obj*, obj*);
obj* l_rbnode_find__core___main___at_rbtree_subset___spec__3___rarg(obj*, obj*, obj*);
uint8 l_rbnode_get__color___main___rarg(obj*);
obj* l_rbnode_insert___at_rbtree__of___spec__4(obj*, obj*);
obj* l_rbmap_insert___main___at_rbtree__of___spec__3(obj*, obj*);
obj* l_rbmap_insert___main___at_rbtree_insert___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_rbtree_from__list___spec__5___rarg(obj*, obj*, obj*);
obj* l_list_foldl___main___at_rbtree__of___spec__6___rarg(obj*, obj*, obj*);
obj* l_rbtree_mfor___rarg(obj*, obj*, obj*);
obj* l_rbtree_any(obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbtree_from__list___spec__3(obj*, obj*);
obj* l_rbtree_find___at_rbtree_contains___spec__1___rarg(obj*, obj*, obj*);
obj* l_rbnode_mfold___main___at_rbtree_mfor___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbtree_has__repr___rarg___closed__1;
obj* l_rbtree_find___at_rbtree_subset___spec__1(obj*, obj*);
obj* l_rbnode_mfold___main___at_rbtree_mfor___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbtree_all(obj*, obj*, obj*);
obj* l_rbnode_fold___main___at_rbtree_fold___spec__1(obj*, obj*);
obj* l_rbnode_mfold___main___at_rbtree_mfold___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbtree_to__list___rarg(obj*);
obj* l_rbmap_insert___main___at_rbtree__of___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_rbtree__of___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbtree__of___spec__5___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_max___main___rarg(obj*);
obj* l_rbtree_has__repr___rarg(obj*, obj*);
obj* l_rbtree_seteq(obj*, obj*);
obj* l_rbnode_ins___main___at_rbtree_of__list___main___spec__3(obj*, obj*);
obj* l_rbnode_insert___at_rbtree_of__list___main___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_rbtree_max(obj*, obj*);
obj* l_rbtree_mfor(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_rbtree_from__list___spec__4(obj*, obj*);
obj* l_rbnode_ins___main___at_rbtree_from__list___spec__4___rarg(obj*, obj*, obj*, obj*);
obj* l_rbtree_subset___at_rbtree_seteq___spec__6___rarg(obj*, obj*, obj*);
obj* l_rbtree_insert___at_rbtree__of___spec__2(obj*, obj*);
uint8 l_rbtree_empty___rarg(obj*);
obj* l_rbtree_contains___rarg___boxed(obj*, obj*, obj*);
obj* l_rbtree_of__list(obj*, obj*);
obj* l_rbmap_insert___main___at_rbtree_of__list___main___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_rbtree_rev__fold___rarg(obj*, obj*, obj*);
obj* l_rbnode_find__core___main___at_rbtree_seteq___spec__4___rarg(obj*, obj*, obj*);
obj* l_rbnode_all___main___at_rbtree_all___spec__1(obj*);
obj* l_rbtree_fold___rarg(obj*, obj*, obj*);
obj* _init_l_rbtree() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_mk__rbtree(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
}
obj* l_rbtree_depth___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_depth___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbtree_depth(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_depth___rarg), 2, 0);
return x_4;
}
}
obj* l_rbnode_fold___main___at_rbtree_fold___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
lean::dec(x_0);
return x_2;
}
default:
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
x_12 = l_rbnode_fold___main___at_rbtree_fold___spec__1___rarg(x_0, x_4, x_2);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_6, x_12);
x_1 = x_8;
x_2 = x_14;
goto _start;
}
}
}
}
obj* l_rbnode_fold___main___at_rbtree_fold___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_fold___main___at_rbtree_fold___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_rbtree_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_fold___main___at_rbtree_fold___spec__1___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbtree_fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_fold___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_rev__fold___main___at_rbtree_rev__fold___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
lean::dec(x_0);
return x_2;
}
default:
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
x_12 = l_rbnode_rev__fold___main___at_rbtree_rev__fold___spec__1___rarg(x_0, x_8, x_2);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_6, x_12);
x_1 = x_4;
x_2 = x_14;
goto _start;
}
}
}
}
obj* l_rbnode_rev__fold___main___at_rbtree_rev__fold___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_rev__fold___main___at_rbtree_rev__fold___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_rbtree_rev__fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_rev__fold___main___at_rbtree_rev__fold___spec__1___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbtree_rev__fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_rev__fold___rarg), 3, 0);
return x_6;
}
}
obj* l_rbnode_mfold___main___at_rbtree_mfold___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_0);
x_7 = lean::apply_2(x_0, x_1, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___at_rbtree_mfold___spec__1___rarg), 4, 3);
lean::closure_set(x_8, 0, x_2);
lean::closure_set(x_8, 1, x_0);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_rbnode_mfold___main___at_rbtree_mfold___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
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
default:
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
x_23 = l_rbnode_mfold___main___at_rbtree_mfold___spec__1___rarg(x_0, x_1, x_12, x_3);
lean::inc(x_19);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___at_rbtree_mfold___spec__1___rarg___lambda__1), 6, 5);
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
}
obj* l_rbnode_mfold___main___at_rbtree_mfold___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___at_rbtree_mfold___spec__1___rarg), 4, 0);
return x_6;
}
}
obj* l_rbtree_mfold___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_mfold___main___at_rbtree_mfold___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbtree_mfold(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_mfold___rarg), 4, 0);
return x_8;
}
}
obj* l_rbnode_mfold___main___at_rbtree_mfor___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_5);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 4);
lean::inc(x_9);
lean::inc(x_1);
x_12 = lean::apply_1(x_1, x_2);
x_13 = lean::cnstr_get(x_7, 1);
lean::inc(x_13);
lean::dec(x_7);
x_16 = lean::box(0);
x_17 = lean::apply_2(x_13, lean::box(0), x_16);
x_18 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_12, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___at_rbtree_mfor___spec__1___rarg), 4, 3);
lean::closure_set(x_19, 0, x_0);
lean::closure_set(x_19, 1, x_1);
lean::closure_set(x_19, 2, x_3);
x_20 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_18, x_19);
return x_20;
}
}
obj* l_rbnode_mfold___main___at_rbtree_mfor___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
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
default:
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
x_23 = l_rbnode_mfold___main___at_rbtree_mfor___spec__1___rarg(x_0, x_1, x_12, x_3);
lean::inc(x_19);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___at_rbtree_mfor___spec__1___rarg___lambda__1), 6, 5);
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
}
obj* l_rbnode_mfold___main___at_rbtree_mfor___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_mfold___main___at_rbtree_mfor___spec__1___rarg), 4, 0);
return x_6;
}
}
obj* l_rbtree_mfor___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_rbnode_mfold___main___at_rbtree_mfor___spec__1___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbtree_mfor(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_mfor___rarg), 3, 0);
return x_8;
}
}
uint8 l_rbtree_empty___rarg(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
default:
{
uint8 x_3; 
lean::dec(x_0);
x_3 = 0;
return x_3;
}
}
}
}
obj* l_rbtree_empty(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_empty___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_rbtree_empty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_rbtree_empty___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_rbnode_rev__fold___main___at_rbtree_to__list___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
return x_1;
}
default:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 3);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_rbnode_rev__fold___main___at_rbtree_to__list___spec__1___rarg(x_6, x_1);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_9);
x_0 = x_2;
x_1 = x_10;
goto _start;
}
}
}
}
obj* l_rbnode_rev__fold___main___at_rbtree_to__list___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_rev__fold___main___at_rbtree_to__list___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_rbtree_to__list___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l_rbnode_rev__fold___main___at_rbtree_to__list___spec__1___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbtree_to__list(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_to__list___rarg), 1, 0);
return x_4;
}
}
obj* l_rbtree_min___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_min___main___rarg(x_0);
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
lean::inc(x_3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_5 = x_1;
} else {
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
obj* l_rbtree_min(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_min___rarg), 1, 0);
return x_4;
}
}
obj* l_rbtree_max___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_max___main___rarg(x_0);
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
lean::inc(x_3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_5 = x_1;
} else {
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
obj* l_rbtree_max(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_max___rarg), 1, 0);
return x_4;
}
}
obj* _init_l_rbtree_has__repr___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("rbtree_of ");
return x_0;
}
}
obj* l_rbtree_has__repr___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; 
x_2 = l_rbtree_to__list___rarg(x_1);
x_3 = l_list_repr___main___rarg(x_0, x_2);
x_4 = l_rbtree_has__repr___rarg___closed__1;
lean::inc(x_4);
x_6 = lean::string_append(x_4, x_3);
lean::dec(x_3);
return x_6;
}
}
obj* l_rbtree_has__repr(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_has__repr___rarg), 2, 0);
return x_4;
}
}
obj* l_rbnode_ins___main___at_rbtree_insert___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_5; 
lean::dec(x_0);
x_5 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
return x_5;
}
case 1:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_14 = x_1;
} else {
 lean::dec(x_1);
 x_14 = lean::box(0);
}
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_24; uint8 x_25; 
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_8, x_2);
x_25 = lean::unbox(x_24);
lean::dec(x_24);
if (x_25 == 0)
{
obj* x_30; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_0);
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_6);
lean::cnstr_set(x_30, 1, x_2);
lean::cnstr_set(x_30, 2, x_3);
lean::cnstr_set(x_30, 3, x_12);
return x_30;
}
else
{
obj* x_31; obj* x_32; 
x_31 = l_rbnode_ins___main___at_rbtree_insert___spec__3___rarg(x_0, x_12, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_32 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_32 = x_14;
}
lean::cnstr_set(x_32, 0, x_6);
lean::cnstr_set(x_32, 1, x_8);
lean::cnstr_set(x_32, 2, x_10);
lean::cnstr_set(x_32, 3, x_31);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; 
x_33 = l_rbnode_ins___main___at_rbtree_insert___spec__3___rarg(x_0, x_6, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_34 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_34 = x_14;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_8);
lean::cnstr_set(x_34, 2, x_10);
lean::cnstr_set(x_34, 3, x_12);
return x_34;
}
}
default:
{
obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_47; uint8 x_48; 
x_35 = lean::cnstr_get(x_1, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_1, 1);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_1, 2);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_1, 3);
lean::inc(x_41);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_43 = x_1;
} else {
 lean::dec(x_1);
 x_43 = lean::box(0);
}
lean::inc(x_37);
lean::inc(x_2);
lean::inc(x_0);
x_47 = lean::apply_2(x_0, x_2, x_37);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_53; uint8 x_54; 
lean::inc(x_2);
lean::inc(x_37);
lean::inc(x_0);
x_53 = lean::apply_2(x_0, x_37, x_2);
x_54 = lean::unbox(x_53);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_59; 
lean::dec(x_0);
lean::dec(x_39);
lean::dec(x_37);
if (lean::is_scalar(x_43)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_43;
}
lean::cnstr_set(x_59, 0, x_35);
lean::cnstr_set(x_59, 1, x_2);
lean::cnstr_set(x_59, 2, x_3);
lean::cnstr_set(x_59, 3, x_41);
return x_59;
}
else
{
uint8 x_61; 
lean::inc(x_41);
x_61 = l_rbnode_get__color___main___rarg(x_41);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_43);
x_63 = l_rbnode_ins___main___at_rbtree_insert___spec__3___rarg(x_0, x_41, x_2, x_3);
x_64 = l_rbnode_balance2__node___main___rarg(x_63, x_37, x_39, x_35);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_rbtree_insert___spec__3___rarg(x_0, x_41, x_2, x_3);
if (lean::is_scalar(x_43)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_43;
}
lean::cnstr_set(x_66, 0, x_35);
lean::cnstr_set(x_66, 1, x_37);
lean::cnstr_set(x_66, 2, x_39);
lean::cnstr_set(x_66, 3, x_65);
return x_66;
}
}
}
else
{
uint8 x_68; 
lean::inc(x_35);
x_68 = l_rbnode_get__color___main___rarg(x_35);
if (x_68 == 0)
{
obj* x_70; obj* x_71; 
lean::dec(x_43);
x_70 = l_rbnode_ins___main___at_rbtree_insert___spec__3___rarg(x_0, x_35, x_2, x_3);
x_71 = l_rbnode_balance1__node___main___rarg(x_70, x_37, x_39, x_41);
return x_71;
}
else
{
obj* x_72; obj* x_73; 
x_72 = l_rbnode_ins___main___at_rbtree_insert___spec__3___rarg(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_43)) {
 x_73 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_73 = x_43;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_37);
lean::cnstr_set(x_73, 2, x_39);
lean::cnstr_set(x_73, 3, x_41);
return x_73;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbtree_insert___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbtree_insert___spec__3___rarg), 4, 0);
return x_4;
}
}
obj* l_rbnode_insert___at_rbtree_insert___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_5 = l_rbnode_get__color___main___rarg(x_1);
x_6 = l_rbnode_ins___main___at_rbtree_insert___spec__3___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_mk__insert__result___main___rarg(x_5, x_6);
return x_7;
}
}
obj* l_rbnode_insert___at_rbtree_insert___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbtree_insert___spec__2___rarg), 4, 0);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbtree_insert___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_rbtree_insert___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbtree_insert___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_rbtree_insert___spec__1___rarg), 4, 0);
return x_4;
}
}
obj* l_rbtree_insert___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_rbnode_insert___at_rbtree_insert___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbtree_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_insert___rarg), 3, 0);
return x_4;
}
}
obj* l_rbnode_ins___main___at_rbtree_of__list___main___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_5; 
lean::dec(x_0);
x_5 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
return x_5;
}
case 1:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_14 = x_1;
} else {
 lean::dec(x_1);
 x_14 = lean::box(0);
}
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_24; uint8 x_25; 
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_8, x_2);
x_25 = lean::unbox(x_24);
lean::dec(x_24);
if (x_25 == 0)
{
obj* x_30; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_0);
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_6);
lean::cnstr_set(x_30, 1, x_2);
lean::cnstr_set(x_30, 2, x_3);
lean::cnstr_set(x_30, 3, x_12);
return x_30;
}
else
{
obj* x_31; obj* x_32; 
x_31 = l_rbnode_ins___main___at_rbtree_of__list___main___spec__3___rarg(x_0, x_12, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_32 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_32 = x_14;
}
lean::cnstr_set(x_32, 0, x_6);
lean::cnstr_set(x_32, 1, x_8);
lean::cnstr_set(x_32, 2, x_10);
lean::cnstr_set(x_32, 3, x_31);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; 
x_33 = l_rbnode_ins___main___at_rbtree_of__list___main___spec__3___rarg(x_0, x_6, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_34 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_34 = x_14;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_8);
lean::cnstr_set(x_34, 2, x_10);
lean::cnstr_set(x_34, 3, x_12);
return x_34;
}
}
default:
{
obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_47; uint8 x_48; 
x_35 = lean::cnstr_get(x_1, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_1, 1);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_1, 2);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_1, 3);
lean::inc(x_41);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_43 = x_1;
} else {
 lean::dec(x_1);
 x_43 = lean::box(0);
}
lean::inc(x_37);
lean::inc(x_2);
lean::inc(x_0);
x_47 = lean::apply_2(x_0, x_2, x_37);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_53; uint8 x_54; 
lean::inc(x_2);
lean::inc(x_37);
lean::inc(x_0);
x_53 = lean::apply_2(x_0, x_37, x_2);
x_54 = lean::unbox(x_53);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_59; 
lean::dec(x_0);
lean::dec(x_39);
lean::dec(x_37);
if (lean::is_scalar(x_43)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_43;
}
lean::cnstr_set(x_59, 0, x_35);
lean::cnstr_set(x_59, 1, x_2);
lean::cnstr_set(x_59, 2, x_3);
lean::cnstr_set(x_59, 3, x_41);
return x_59;
}
else
{
uint8 x_61; 
lean::inc(x_41);
x_61 = l_rbnode_get__color___main___rarg(x_41);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_43);
x_63 = l_rbnode_ins___main___at_rbtree_of__list___main___spec__3___rarg(x_0, x_41, x_2, x_3);
x_64 = l_rbnode_balance2__node___main___rarg(x_63, x_37, x_39, x_35);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_rbtree_of__list___main___spec__3___rarg(x_0, x_41, x_2, x_3);
if (lean::is_scalar(x_43)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_43;
}
lean::cnstr_set(x_66, 0, x_35);
lean::cnstr_set(x_66, 1, x_37);
lean::cnstr_set(x_66, 2, x_39);
lean::cnstr_set(x_66, 3, x_65);
return x_66;
}
}
}
else
{
uint8 x_68; 
lean::inc(x_35);
x_68 = l_rbnode_get__color___main___rarg(x_35);
if (x_68 == 0)
{
obj* x_70; obj* x_71; 
lean::dec(x_43);
x_70 = l_rbnode_ins___main___at_rbtree_of__list___main___spec__3___rarg(x_0, x_35, x_2, x_3);
x_71 = l_rbnode_balance1__node___main___rarg(x_70, x_37, x_39, x_41);
return x_71;
}
else
{
obj* x_72; obj* x_73; 
x_72 = l_rbnode_ins___main___at_rbtree_of__list___main___spec__3___rarg(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_43)) {
 x_73 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_73 = x_43;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_37);
lean::cnstr_set(x_73, 2, x_39);
lean::cnstr_set(x_73, 3, x_41);
return x_73;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbtree_of__list___main___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbtree_of__list___main___spec__3___rarg), 4, 0);
return x_4;
}
}
obj* l_rbnode_insert___at_rbtree_of__list___main___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_5 = l_rbnode_get__color___main___rarg(x_1);
x_6 = l_rbnode_ins___main___at_rbtree_of__list___main___spec__3___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_mk__insert__result___main___rarg(x_5, x_6);
return x_7;
}
}
obj* l_rbnode_insert___at_rbtree_of__list___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbtree_of__list___main___spec__2___rarg), 4, 0);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbtree_of__list___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_rbtree_of__list___main___spec__2___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbtree_of__list___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_rbtree_of__list___main___spec__1___rarg), 4, 0);
return x_4;
}
}
obj* l_rbtree_of__list___main___rarg(obj* x_0, obj* x_1) {
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
x_10 = l_rbtree_of__list___main___rarg(x_0, x_6);
x_11 = lean::box(0);
x_12 = l_rbnode_insert___at_rbtree_of__list___main___spec__2___rarg(x_0, x_10, x_4, x_11);
return x_12;
}
}
}
obj* l_rbtree_of__list___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_of__list___main___rarg), 2, 0);
return x_4;
}
}
obj* l_rbtree_of__list___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbtree_of__list___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbtree_of__list(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_of__list___rarg), 2, 0);
return x_4;
}
}
obj* l_rbnode_find__core___main___at_rbtree_find___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_5; 
lean::dec(x_0);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
case 1:
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
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_25; uint8 x_26; 
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_8, x_2);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_8);
lean::cnstr_set(x_31, 1, x_10);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
return x_32;
}
else
{
lean::dec(x_10);
lean::dec(x_8);
x_1 = x_12;
goto _start;
}
}
else
{
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_8);
x_1 = x_6;
goto _start;
}
}
default:
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_52; uint8 x_53; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_1, 2);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_1, 3);
lean::inc(x_46);
lean::dec(x_1);
lean::inc(x_42);
lean::inc(x_2);
lean::inc(x_0);
x_52 = lean::apply_2(x_0, x_2, x_42);
x_53 = lean::unbox(x_52);
lean::dec(x_52);
if (x_53 == 0)
{
obj* x_59; uint8 x_60; 
lean::dec(x_40);
lean::inc(x_2);
lean::inc(x_42);
lean::inc(x_0);
x_59 = lean::apply_2(x_0, x_42, x_2);
x_60 = lean::unbox(x_59);
lean::dec(x_59);
if (x_60 == 0)
{
obj* x_65; obj* x_66; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_46);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_42);
lean::cnstr_set(x_65, 1, x_44);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
return x_66;
}
else
{
lean::dec(x_42);
lean::dec(x_44);
x_1 = x_46;
goto _start;
}
}
else
{
lean::dec(x_42);
lean::dec(x_44);
lean::dec(x_46);
x_1 = x_40;
goto _start;
}
}
}
}
}
obj* l_rbnode_find__core___main___at_rbtree_find___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find__core___main___at_rbtree_find___spec__2___rarg), 3, 0);
return x_4;
}
}
obj* l_rbmap_find__core___main___at_rbtree_find___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___at_rbtree_find___spec__2___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find__core___main___at_rbtree_find___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find__core___main___at_rbtree_find___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_rbtree_find___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___at_rbtree_find___spec__2___rarg(x_0, x_1, x_2);
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
lean::inc(x_5);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_7 = x_3;
} else {
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
obj* l_rbtree_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_find___rarg), 3, 0);
return x_4;
}
}
obj* l_rbnode_find__core___main___at_rbtree_contains___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_5; 
lean::dec(x_0);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
case 1:
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
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_25; uint8 x_26; 
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_8, x_2);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_8);
lean::cnstr_set(x_31, 1, x_10);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
return x_32;
}
else
{
lean::dec(x_10);
lean::dec(x_8);
x_1 = x_12;
goto _start;
}
}
else
{
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_8);
x_1 = x_6;
goto _start;
}
}
default:
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_52; uint8 x_53; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_1, 2);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_1, 3);
lean::inc(x_46);
lean::dec(x_1);
lean::inc(x_42);
lean::inc(x_2);
lean::inc(x_0);
x_52 = lean::apply_2(x_0, x_2, x_42);
x_53 = lean::unbox(x_52);
lean::dec(x_52);
if (x_53 == 0)
{
obj* x_59; uint8 x_60; 
lean::dec(x_40);
lean::inc(x_2);
lean::inc(x_42);
lean::inc(x_0);
x_59 = lean::apply_2(x_0, x_42, x_2);
x_60 = lean::unbox(x_59);
lean::dec(x_59);
if (x_60 == 0)
{
obj* x_65; obj* x_66; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_46);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_42);
lean::cnstr_set(x_65, 1, x_44);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
return x_66;
}
else
{
lean::dec(x_42);
lean::dec(x_44);
x_1 = x_46;
goto _start;
}
}
else
{
lean::dec(x_42);
lean::dec(x_44);
lean::dec(x_46);
x_1 = x_40;
goto _start;
}
}
}
}
}
obj* l_rbnode_find__core___main___at_rbtree_contains___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find__core___main___at_rbtree_contains___spec__3___rarg), 3, 0);
return x_4;
}
}
obj* l_rbmap_find__core___main___at_rbtree_contains___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___at_rbtree_contains___spec__3___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find__core___main___at_rbtree_contains___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find__core___main___at_rbtree_contains___spec__2___rarg), 3, 0);
return x_4;
}
}
obj* l_rbtree_find___at_rbtree_contains___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___at_rbtree_contains___spec__3___rarg(x_0, x_1, x_2);
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
lean::inc(x_5);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_7 = x_3;
} else {
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
obj* l_rbtree_find___at_rbtree_contains___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_find___at_rbtree_contains___spec__1___rarg), 3, 0);
return x_4;
}
}
uint8 l_rbtree_contains___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_rbtree_find___at_rbtree_contains___spec__1___rarg(x_0, x_1, x_2);
x_4 = l_option_is__some___main___rarg(x_3);
return x_4;
}
}
obj* l_rbtree_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_contains___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_rbtree_contains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_rbtree_contains___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_rbnode_ins___main___at_rbtree_from__list___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_5; 
lean::dec(x_0);
x_5 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
return x_5;
}
case 1:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_14 = x_1;
} else {
 lean::dec(x_1);
 x_14 = lean::box(0);
}
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_24; uint8 x_25; 
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_8, x_2);
x_25 = lean::unbox(x_24);
lean::dec(x_24);
if (x_25 == 0)
{
obj* x_30; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_0);
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_6);
lean::cnstr_set(x_30, 1, x_2);
lean::cnstr_set(x_30, 2, x_3);
lean::cnstr_set(x_30, 3, x_12);
return x_30;
}
else
{
obj* x_31; obj* x_32; 
x_31 = l_rbnode_ins___main___at_rbtree_from__list___spec__4___rarg(x_0, x_12, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_32 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_32 = x_14;
}
lean::cnstr_set(x_32, 0, x_6);
lean::cnstr_set(x_32, 1, x_8);
lean::cnstr_set(x_32, 2, x_10);
lean::cnstr_set(x_32, 3, x_31);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; 
x_33 = l_rbnode_ins___main___at_rbtree_from__list___spec__4___rarg(x_0, x_6, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_34 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_34 = x_14;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_8);
lean::cnstr_set(x_34, 2, x_10);
lean::cnstr_set(x_34, 3, x_12);
return x_34;
}
}
default:
{
obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_47; uint8 x_48; 
x_35 = lean::cnstr_get(x_1, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_1, 1);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_1, 2);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_1, 3);
lean::inc(x_41);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_43 = x_1;
} else {
 lean::dec(x_1);
 x_43 = lean::box(0);
}
lean::inc(x_37);
lean::inc(x_2);
lean::inc(x_0);
x_47 = lean::apply_2(x_0, x_2, x_37);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_53; uint8 x_54; 
lean::inc(x_2);
lean::inc(x_37);
lean::inc(x_0);
x_53 = lean::apply_2(x_0, x_37, x_2);
x_54 = lean::unbox(x_53);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_59; 
lean::dec(x_0);
lean::dec(x_39);
lean::dec(x_37);
if (lean::is_scalar(x_43)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_43;
}
lean::cnstr_set(x_59, 0, x_35);
lean::cnstr_set(x_59, 1, x_2);
lean::cnstr_set(x_59, 2, x_3);
lean::cnstr_set(x_59, 3, x_41);
return x_59;
}
else
{
uint8 x_61; 
lean::inc(x_41);
x_61 = l_rbnode_get__color___main___rarg(x_41);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_43);
x_63 = l_rbnode_ins___main___at_rbtree_from__list___spec__4___rarg(x_0, x_41, x_2, x_3);
x_64 = l_rbnode_balance2__node___main___rarg(x_63, x_37, x_39, x_35);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_rbtree_from__list___spec__4___rarg(x_0, x_41, x_2, x_3);
if (lean::is_scalar(x_43)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_43;
}
lean::cnstr_set(x_66, 0, x_35);
lean::cnstr_set(x_66, 1, x_37);
lean::cnstr_set(x_66, 2, x_39);
lean::cnstr_set(x_66, 3, x_65);
return x_66;
}
}
}
else
{
uint8 x_68; 
lean::inc(x_35);
x_68 = l_rbnode_get__color___main___rarg(x_35);
if (x_68 == 0)
{
obj* x_70; obj* x_71; 
lean::dec(x_43);
x_70 = l_rbnode_ins___main___at_rbtree_from__list___spec__4___rarg(x_0, x_35, x_2, x_3);
x_71 = l_rbnode_balance1__node___main___rarg(x_70, x_37, x_39, x_41);
return x_71;
}
else
{
obj* x_72; obj* x_73; 
x_72 = l_rbnode_ins___main___at_rbtree_from__list___spec__4___rarg(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_43)) {
 x_73 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_73 = x_43;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_37);
lean::cnstr_set(x_73, 2, x_39);
lean::cnstr_set(x_73, 3, x_41);
return x_73;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbtree_from__list___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbtree_from__list___spec__4___rarg), 4, 0);
return x_4;
}
}
obj* l_rbnode_insert___at_rbtree_from__list___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_5 = l_rbnode_get__color___main___rarg(x_1);
x_6 = l_rbnode_ins___main___at_rbtree_from__list___spec__4___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_mk__insert__result___main___rarg(x_5, x_6);
return x_7;
}
}
obj* l_rbnode_insert___at_rbtree_from__list___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbtree_from__list___spec__3___rarg), 4, 0);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbtree_from__list___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_rbtree_from__list___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbtree_from__list___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_rbtree_from__list___spec__2___rarg), 4, 0);
return x_4;
}
}
obj* l_rbtree_insert___at_rbtree_from__list___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_rbnode_insert___at_rbtree_from__list___spec__3___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbtree_insert___at_rbtree_from__list___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_insert___at_rbtree_from__list___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_list_foldl___main___at_rbtree_from__list___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
x_11 = l_rbnode_insert___at_rbtree_from__list___spec__3___rarg(x_0, x_1, x_4, x_9);
x_1 = x_11;
x_2 = x_6;
goto _start;
}
}
}
obj* l_list_foldl___main___at_rbtree_from__list___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldl___main___at_rbtree_from__list___spec__5___rarg), 3, 0);
return x_4;
}
}
obj* l_rbtree_from__list___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = l_list_foldl___main___at_rbtree_from__list___spec__5___rarg(x_2, x_4, x_0);
return x_5;
}
}
obj* l_rbtree_from__list(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_from__list___rarg), 3, 0);
return x_2;
}
}
obj* l_rbnode_all___main___at_rbtree_all___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_3; obj* x_4; 
lean::dec(x_0);
x_3 = 1;
x_4 = lean::box(x_3);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_13; uint8 x_14; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 3);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_0);
x_13 = lean::apply_1(x_0, x_7);
x_14 = lean::unbox(x_13);
if (x_14 == 0)
{
lean::dec(x_5);
if (x_14 == 0)
{
lean::dec(x_9);
lean::dec(x_0);
return x_13;
}
else
{
lean::dec(x_13);
x_1 = x_9;
goto _start;
}
}
else
{
obj* x_22; uint8 x_23; 
lean::dec(x_13);
lean::inc(x_0);
x_22 = l_rbnode_all___main___at_rbtree_all___spec__1___rarg(x_0, x_5);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
lean::dec(x_9);
lean::dec(x_0);
return x_22;
}
else
{
lean::dec(x_22);
x_1 = x_9;
goto _start;
}
}
}
default:
{
obj* x_28; obj* x_30; obj* x_32; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_1, 1);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_1, 3);
lean::inc(x_32);
lean::dec(x_1);
lean::inc(x_0);
x_36 = lean::apply_1(x_0, x_30);
x_37 = lean::unbox(x_36);
if (x_37 == 0)
{
lean::dec(x_28);
if (x_37 == 0)
{
lean::dec(x_0);
lean::dec(x_32);
return x_36;
}
else
{
lean::dec(x_36);
x_1 = x_32;
goto _start;
}
}
else
{
obj* x_45; uint8 x_46; 
lean::dec(x_36);
lean::inc(x_0);
x_45 = l_rbnode_all___main___at_rbtree_all___spec__1___rarg(x_0, x_28);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
lean::dec(x_0);
lean::dec(x_32);
return x_45;
}
else
{
lean::dec(x_45);
x_1 = x_32;
goto _start;
}
}
}
}
}
}
obj* l_rbnode_all___main___at_rbtree_all___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_all___main___at_rbtree_all___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_rbtree_all___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_all___main___at_rbtree_all___spec__1___rarg(x_1, x_0);
return x_2;
}
}
obj* l_rbtree_all(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_all___rarg), 2, 0);
return x_6;
}
}
obj* l_rbnode_any___main___at_rbtree_any___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_3; obj* x_4; 
lean::dec(x_0);
x_3 = 0;
x_4 = lean::box(x_3);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_13; uint8 x_14; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 3);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_0);
x_13 = lean::apply_1(x_0, x_7);
x_14 = lean::unbox(x_13);
if (x_14 == 0)
{
obj* x_17; uint8 x_18; 
lean::dec(x_13);
lean::inc(x_0);
x_17 = l_rbnode_any___main___at_rbtree_any___spec__1___rarg(x_0, x_5);
x_18 = lean::unbox(x_17);
if (x_18 == 0)
{
lean::dec(x_17);
x_1 = x_9;
goto _start;
}
else
{
lean::dec(x_9);
lean::dec(x_0);
return x_17;
}
}
else
{
lean::dec(x_5);
if (x_14 == 0)
{
lean::dec(x_13);
x_1 = x_9;
goto _start;
}
else
{
lean::dec(x_9);
lean::dec(x_0);
return x_13;
}
}
}
default:
{
obj* x_28; obj* x_30; obj* x_32; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_1, 1);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_1, 3);
lean::inc(x_32);
lean::dec(x_1);
lean::inc(x_0);
x_36 = lean::apply_1(x_0, x_30);
x_37 = lean::unbox(x_36);
if (x_37 == 0)
{
obj* x_40; uint8 x_41; 
lean::dec(x_36);
lean::inc(x_0);
x_40 = l_rbnode_any___main___at_rbtree_any___spec__1___rarg(x_0, x_28);
x_41 = lean::unbox(x_40);
if (x_41 == 0)
{
lean::dec(x_40);
x_1 = x_32;
goto _start;
}
else
{
lean::dec(x_0);
lean::dec(x_32);
return x_40;
}
}
else
{
lean::dec(x_28);
if (x_37 == 0)
{
lean::dec(x_36);
x_1 = x_32;
goto _start;
}
else
{
lean::dec(x_0);
lean::dec(x_32);
return x_36;
}
}
}
}
}
}
obj* l_rbnode_any___main___at_rbtree_any___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_any___main___at_rbtree_any___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_rbtree_any___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_any___main___at_rbtree_any___spec__1___rarg(x_1, x_0);
return x_2;
}
}
obj* l_rbtree_any(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_any___rarg), 2, 0);
return x_6;
}
}
obj* l_rbnode_find__core___main___at_rbtree_subset___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_5; 
lean::dec(x_0);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
case 1:
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
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_25; uint8 x_26; 
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_8, x_2);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_8);
lean::cnstr_set(x_31, 1, x_10);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
return x_32;
}
else
{
lean::dec(x_10);
lean::dec(x_8);
x_1 = x_12;
goto _start;
}
}
else
{
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_8);
x_1 = x_6;
goto _start;
}
}
default:
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_52; uint8 x_53; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_1, 2);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_1, 3);
lean::inc(x_46);
lean::dec(x_1);
lean::inc(x_42);
lean::inc(x_2);
lean::inc(x_0);
x_52 = lean::apply_2(x_0, x_2, x_42);
x_53 = lean::unbox(x_52);
lean::dec(x_52);
if (x_53 == 0)
{
obj* x_59; uint8 x_60; 
lean::dec(x_40);
lean::inc(x_2);
lean::inc(x_42);
lean::inc(x_0);
x_59 = lean::apply_2(x_0, x_42, x_2);
x_60 = lean::unbox(x_59);
lean::dec(x_59);
if (x_60 == 0)
{
obj* x_65; obj* x_66; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_46);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_42);
lean::cnstr_set(x_65, 1, x_44);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
return x_66;
}
else
{
lean::dec(x_42);
lean::dec(x_44);
x_1 = x_46;
goto _start;
}
}
else
{
lean::dec(x_42);
lean::dec(x_44);
lean::dec(x_46);
x_1 = x_40;
goto _start;
}
}
}
}
}
obj* l_rbnode_find__core___main___at_rbtree_subset___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find__core___main___at_rbtree_subset___spec__3___rarg), 3, 0);
return x_4;
}
}
obj* l_rbmap_find__core___main___at_rbtree_subset___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___at_rbtree_subset___spec__3___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find__core___main___at_rbtree_subset___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find__core___main___at_rbtree_subset___spec__2___rarg), 3, 0);
return x_4;
}
}
obj* l_rbtree_find___at_rbtree_subset___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___at_rbtree_subset___spec__3___rarg(x_0, x_1, x_2);
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
lean::inc(x_5);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_7 = x_3;
} else {
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
obj* l_rbtree_find___at_rbtree_subset___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_find___at_rbtree_subset___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_rbnode_all___main___at_rbtree_subset___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
uint8 x_5; obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = 1;
x_6 = lean::box(x_5);
return x_6;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_16; uint8 x_17; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 3);
lean::inc(x_11);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_16 = l_rbtree_find___at_rbtree_subset___spec__1___rarg(x_0, x_1, x_9);
x_17 = l_option_to__bool___main___rarg(x_16);
if (x_17 == 0)
{
lean::dec(x_7);
if (x_17 == 0)
{
obj* x_22; 
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_0);
x_22 = lean::box(x_17);
return x_22;
}
else
{
x_2 = x_11;
goto _start;
}
}
else
{
obj* x_26; uint8 x_27; 
lean::inc(x_1);
lean::inc(x_0);
x_26 = l_rbnode_all___main___at_rbtree_subset___spec__4___rarg(x_0, x_1, x_7);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_0);
return x_26;
}
else
{
lean::dec(x_26);
x_2 = x_11;
goto _start;
}
}
}
default:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_42; uint8 x_43; 
x_33 = lean::cnstr_get(x_2, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_2, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_2, 3);
lean::inc(x_37);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_42 = l_rbtree_find___at_rbtree_subset___spec__1___rarg(x_0, x_1, x_35);
x_43 = l_option_to__bool___main___rarg(x_42);
if (x_43 == 0)
{
lean::dec(x_33);
if (x_43 == 0)
{
obj* x_48; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
x_48 = lean::box(x_43);
return x_48;
}
else
{
x_2 = x_37;
goto _start;
}
}
else
{
obj* x_52; uint8 x_53; 
lean::inc(x_1);
lean::inc(x_0);
x_52 = l_rbnode_all___main___at_rbtree_subset___spec__4___rarg(x_0, x_1, x_33);
x_53 = lean::unbox(x_52);
if (x_53 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
return x_52;
}
else
{
lean::dec(x_52);
x_2 = x_37;
goto _start;
}
}
}
}
}
}
obj* l_rbnode_all___main___at_rbtree_subset___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_all___main___at_rbtree_subset___spec__4___rarg), 3, 0);
return x_4;
}
}
obj* l_rbtree_subset___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_all___main___at_rbtree_subset___spec__4___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_rbtree_subset(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_subset___rarg), 3, 0);
return x_4;
}
}
obj* l_rbnode_find__core___main___at_rbtree_seteq___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_5; 
lean::dec(x_0);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
case 1:
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
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_25; uint8 x_26; 
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_8, x_2);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_8);
lean::cnstr_set(x_31, 1, x_10);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
return x_32;
}
else
{
lean::dec(x_10);
lean::dec(x_8);
x_1 = x_12;
goto _start;
}
}
else
{
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_8);
x_1 = x_6;
goto _start;
}
}
default:
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_52; uint8 x_53; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_1, 2);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_1, 3);
lean::inc(x_46);
lean::dec(x_1);
lean::inc(x_42);
lean::inc(x_2);
lean::inc(x_0);
x_52 = lean::apply_2(x_0, x_2, x_42);
x_53 = lean::unbox(x_52);
lean::dec(x_52);
if (x_53 == 0)
{
obj* x_59; uint8 x_60; 
lean::dec(x_40);
lean::inc(x_2);
lean::inc(x_42);
lean::inc(x_0);
x_59 = lean::apply_2(x_0, x_42, x_2);
x_60 = lean::unbox(x_59);
lean::dec(x_59);
if (x_60 == 0)
{
obj* x_65; obj* x_66; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_46);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_42);
lean::cnstr_set(x_65, 1, x_44);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
return x_66;
}
else
{
lean::dec(x_42);
lean::dec(x_44);
x_1 = x_46;
goto _start;
}
}
else
{
lean::dec(x_42);
lean::dec(x_44);
lean::dec(x_46);
x_1 = x_40;
goto _start;
}
}
}
}
}
obj* l_rbnode_find__core___main___at_rbtree_seteq___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find__core___main___at_rbtree_seteq___spec__4___rarg), 3, 0);
return x_4;
}
}
obj* l_rbmap_find__core___main___at_rbtree_seteq___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___at_rbtree_seteq___spec__4___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find__core___main___at_rbtree_seteq___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find__core___main___at_rbtree_seteq___spec__3___rarg), 3, 0);
return x_4;
}
}
obj* l_rbtree_find___at_rbtree_seteq___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___at_rbtree_seteq___spec__4___rarg(x_0, x_1, x_2);
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
lean::inc(x_5);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_7 = x_3;
} else {
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
obj* l_rbtree_find___at_rbtree_seteq___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_find___at_rbtree_seteq___spec__2___rarg), 3, 0);
return x_4;
}
}
obj* l_rbnode_all___main___at_rbtree_seteq___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
uint8 x_5; obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = 1;
x_6 = lean::box(x_5);
return x_6;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_16; uint8 x_17; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 3);
lean::inc(x_11);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_16 = l_rbtree_find___at_rbtree_seteq___spec__2___rarg(x_0, x_1, x_9);
x_17 = l_option_to__bool___main___rarg(x_16);
if (x_17 == 0)
{
lean::dec(x_7);
if (x_17 == 0)
{
obj* x_22; 
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_0);
x_22 = lean::box(x_17);
return x_22;
}
else
{
x_2 = x_11;
goto _start;
}
}
else
{
obj* x_26; uint8 x_27; 
lean::inc(x_1);
lean::inc(x_0);
x_26 = l_rbnode_all___main___at_rbtree_seteq___spec__5___rarg(x_0, x_1, x_7);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_0);
return x_26;
}
else
{
lean::dec(x_26);
x_2 = x_11;
goto _start;
}
}
}
default:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_42; uint8 x_43; 
x_33 = lean::cnstr_get(x_2, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_2, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_2, 3);
lean::inc(x_37);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_42 = l_rbtree_find___at_rbtree_seteq___spec__2___rarg(x_0, x_1, x_35);
x_43 = l_option_to__bool___main___rarg(x_42);
if (x_43 == 0)
{
lean::dec(x_33);
if (x_43 == 0)
{
obj* x_48; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
x_48 = lean::box(x_43);
return x_48;
}
else
{
x_2 = x_37;
goto _start;
}
}
else
{
obj* x_52; uint8 x_53; 
lean::inc(x_1);
lean::inc(x_0);
x_52 = l_rbnode_all___main___at_rbtree_seteq___spec__5___rarg(x_0, x_1, x_33);
x_53 = lean::unbox(x_52);
if (x_53 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
return x_52;
}
else
{
lean::dec(x_52);
x_2 = x_37;
goto _start;
}
}
}
}
}
}
obj* l_rbnode_all___main___at_rbtree_seteq___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_all___main___at_rbtree_seteq___spec__5___rarg), 3, 0);
return x_4;
}
}
obj* l_rbtree_subset___at_rbtree_seteq___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_all___main___at_rbtree_seteq___spec__5___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_rbtree_subset___at_rbtree_seteq___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_subset___at_rbtree_seteq___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_rbnode_find__core___main___at_rbtree_seteq___spec__9___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_5; 
lean::dec(x_0);
lean::dec(x_2);
x_5 = lean::box(0);
return x_5;
}
case 1:
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
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_25; uint8 x_26; 
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_25 = lean::apply_2(x_0, x_8, x_2);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_31; obj* x_32; 
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_8);
lean::cnstr_set(x_31, 1, x_10);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
return x_32;
}
else
{
lean::dec(x_10);
lean::dec(x_8);
x_1 = x_12;
goto _start;
}
}
else
{
lean::dec(x_10);
lean::dec(x_12);
lean::dec(x_8);
x_1 = x_6;
goto _start;
}
}
default:
{
obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_52; uint8 x_53; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_1, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_1, 2);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_1, 3);
lean::inc(x_46);
lean::dec(x_1);
lean::inc(x_42);
lean::inc(x_2);
lean::inc(x_0);
x_52 = lean::apply_2(x_0, x_2, x_42);
x_53 = lean::unbox(x_52);
lean::dec(x_52);
if (x_53 == 0)
{
obj* x_59; uint8 x_60; 
lean::dec(x_40);
lean::inc(x_2);
lean::inc(x_42);
lean::inc(x_0);
x_59 = lean::apply_2(x_0, x_42, x_2);
x_60 = lean::unbox(x_59);
lean::dec(x_59);
if (x_60 == 0)
{
obj* x_65; obj* x_66; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_46);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_42);
lean::cnstr_set(x_65, 1, x_44);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
return x_66;
}
else
{
lean::dec(x_42);
lean::dec(x_44);
x_1 = x_46;
goto _start;
}
}
else
{
lean::dec(x_42);
lean::dec(x_44);
lean::dec(x_46);
x_1 = x_40;
goto _start;
}
}
}
}
}
obj* l_rbnode_find__core___main___at_rbtree_seteq___spec__9(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find__core___main___at_rbtree_seteq___spec__9___rarg), 3, 0);
return x_4;
}
}
obj* l_rbmap_find__core___main___at_rbtree_seteq___spec__8___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___at_rbtree_seteq___spec__9___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_find__core___main___at_rbtree_seteq___spec__8(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find__core___main___at_rbtree_seteq___spec__8___rarg), 3, 0);
return x_4;
}
}
obj* l_rbtree_find___at_rbtree_seteq___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find__core___main___at_rbtree_seteq___spec__9___rarg(x_0, x_1, x_2);
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
lean::inc(x_5);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_7 = x_3;
} else {
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
obj* l_rbtree_find___at_rbtree_seteq___spec__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_find___at_rbtree_seteq___spec__7___rarg), 3, 0);
return x_4;
}
}
obj* l_rbnode_all___main___at_rbtree_seteq___spec__10___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
uint8 x_5; obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = 1;
x_6 = lean::box(x_5);
return x_6;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_16; uint8 x_17; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 3);
lean::inc(x_11);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_16 = l_rbtree_find___at_rbtree_seteq___spec__7___rarg(x_0, x_1, x_9);
x_17 = l_option_to__bool___main___rarg(x_16);
if (x_17 == 0)
{
lean::dec(x_7);
if (x_17 == 0)
{
obj* x_22; 
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_0);
x_22 = lean::box(x_17);
return x_22;
}
else
{
x_2 = x_11;
goto _start;
}
}
else
{
obj* x_26; uint8 x_27; 
lean::inc(x_1);
lean::inc(x_0);
x_26 = l_rbnode_all___main___at_rbtree_seteq___spec__10___rarg(x_0, x_1, x_7);
x_27 = lean::unbox(x_26);
if (x_27 == 0)
{
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_0);
return x_26;
}
else
{
lean::dec(x_26);
x_2 = x_11;
goto _start;
}
}
}
default:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_42; uint8 x_43; 
x_33 = lean::cnstr_get(x_2, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_2, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_2, 3);
lean::inc(x_37);
lean::dec(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_42 = l_rbtree_find___at_rbtree_seteq___spec__7___rarg(x_0, x_1, x_35);
x_43 = l_option_to__bool___main___rarg(x_42);
if (x_43 == 0)
{
lean::dec(x_33);
if (x_43 == 0)
{
obj* x_48; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
x_48 = lean::box(x_43);
return x_48;
}
else
{
x_2 = x_37;
goto _start;
}
}
else
{
obj* x_52; uint8 x_53; 
lean::inc(x_1);
lean::inc(x_0);
x_52 = l_rbnode_all___main___at_rbtree_seteq___spec__10___rarg(x_0, x_1, x_33);
x_53 = lean::unbox(x_52);
if (x_53 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
return x_52;
}
else
{
lean::dec(x_52);
x_2 = x_37;
goto _start;
}
}
}
}
}
}
obj* l_rbnode_all___main___at_rbtree_seteq___spec__10(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_all___main___at_rbtree_seteq___spec__10___rarg), 3, 0);
return x_4;
}
}
obj* l_rbtree_subset___at_rbtree_seteq___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_all___main___at_rbtree_seteq___spec__10___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_rbtree_subset___at_rbtree_seteq___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_subset___at_rbtree_seteq___spec__6___rarg), 3, 0);
return x_4;
}
}
obj* l_rbtree_seteq___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; uint8 x_7; 
lean::inc(x_1);
lean::inc(x_2);
lean::inc(x_0);
x_6 = l_rbnode_all___main___at_rbtree_seteq___spec__5___rarg(x_0, x_2, x_1);
x_7 = lean::unbox(x_6);
if (x_7 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_6;
}
else
{
obj* x_12; 
lean::dec(x_6);
x_12 = l_rbnode_all___main___at_rbtree_seteq___spec__10___rarg(x_0, x_1, x_2);
return x_12;
}
}
}
obj* l_rbtree_seteq(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_seteq___rarg), 3, 0);
return x_4;
}
}
obj* l_rbnode_ins___main___at_rbtree__of___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_5; 
lean::dec(x_0);
x_5 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_1);
return x_5;
}
case 1:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 3);
lean::inc(x_12);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_14 = x_1;
} else {
 lean::dec(x_1);
 x_14 = lean::box(0);
}
lean::inc(x_8);
lean::inc(x_2);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_2, x_8);
x_19 = lean::unbox(x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_24; uint8 x_25; 
lean::inc(x_2);
lean::inc(x_8);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_8, x_2);
x_25 = lean::unbox(x_24);
lean::dec(x_24);
if (x_25 == 0)
{
obj* x_30; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_0);
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_6);
lean::cnstr_set(x_30, 1, x_2);
lean::cnstr_set(x_30, 2, x_3);
lean::cnstr_set(x_30, 3, x_12);
return x_30;
}
else
{
obj* x_31; obj* x_32; 
x_31 = l_rbnode_ins___main___at_rbtree__of___spec__5___rarg(x_0, x_12, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_32 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_32 = x_14;
}
lean::cnstr_set(x_32, 0, x_6);
lean::cnstr_set(x_32, 1, x_8);
lean::cnstr_set(x_32, 2, x_10);
lean::cnstr_set(x_32, 3, x_31);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; 
x_33 = l_rbnode_ins___main___at_rbtree__of___spec__5___rarg(x_0, x_6, x_2, x_3);
if (lean::is_scalar(x_14)) {
 x_34 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_34 = x_14;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_8);
lean::cnstr_set(x_34, 2, x_10);
lean::cnstr_set(x_34, 3, x_12);
return x_34;
}
}
default:
{
obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_43; obj* x_47; uint8 x_48; 
x_35 = lean::cnstr_get(x_1, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_1, 1);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_1, 2);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_1, 3);
lean::inc(x_41);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 lean::cnstr_release(x_1, 3);
 x_43 = x_1;
} else {
 lean::dec(x_1);
 x_43 = lean::box(0);
}
lean::inc(x_37);
lean::inc(x_2);
lean::inc(x_0);
x_47 = lean::apply_2(x_0, x_2, x_37);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_53; uint8 x_54; 
lean::inc(x_2);
lean::inc(x_37);
lean::inc(x_0);
x_53 = lean::apply_2(x_0, x_37, x_2);
x_54 = lean::unbox(x_53);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_59; 
lean::dec(x_0);
lean::dec(x_39);
lean::dec(x_37);
if (lean::is_scalar(x_43)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_43;
}
lean::cnstr_set(x_59, 0, x_35);
lean::cnstr_set(x_59, 1, x_2);
lean::cnstr_set(x_59, 2, x_3);
lean::cnstr_set(x_59, 3, x_41);
return x_59;
}
else
{
uint8 x_61; 
lean::inc(x_41);
x_61 = l_rbnode_get__color___main___rarg(x_41);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_43);
x_63 = l_rbnode_ins___main___at_rbtree__of___spec__5___rarg(x_0, x_41, x_2, x_3);
x_64 = l_rbnode_balance2__node___main___rarg(x_63, x_37, x_39, x_35);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_rbtree__of___spec__5___rarg(x_0, x_41, x_2, x_3);
if (lean::is_scalar(x_43)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_43;
}
lean::cnstr_set(x_66, 0, x_35);
lean::cnstr_set(x_66, 1, x_37);
lean::cnstr_set(x_66, 2, x_39);
lean::cnstr_set(x_66, 3, x_65);
return x_66;
}
}
}
else
{
uint8 x_68; 
lean::inc(x_35);
x_68 = l_rbnode_get__color___main___rarg(x_35);
if (x_68 == 0)
{
obj* x_70; obj* x_71; 
lean::dec(x_43);
x_70 = l_rbnode_ins___main___at_rbtree__of___spec__5___rarg(x_0, x_35, x_2, x_3);
x_71 = l_rbnode_balance1__node___main___rarg(x_70, x_37, x_39, x_41);
return x_71;
}
else
{
obj* x_72; obj* x_73; 
x_72 = l_rbnode_ins___main___at_rbtree__of___spec__5___rarg(x_0, x_35, x_2, x_3);
if (lean::is_scalar(x_43)) {
 x_73 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_73 = x_43;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_37);
lean::cnstr_set(x_73, 2, x_39);
lean::cnstr_set(x_73, 3, x_41);
return x_73;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_rbtree__of___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_rbtree__of___spec__5___rarg), 4, 0);
return x_4;
}
}
obj* l_rbnode_insert___at_rbtree__of___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_5 = l_rbnode_get__color___main___rarg(x_1);
x_6 = l_rbnode_ins___main___at_rbtree__of___spec__5___rarg(x_0, x_1, x_2, x_3);
x_7 = l_rbnode_mk__insert__result___main___rarg(x_5, x_6);
return x_7;
}
}
obj* l_rbnode_insert___at_rbtree__of___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_rbtree__of___spec__4___rarg), 4, 0);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbtree__of___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_rbnode_insert___at_rbtree__of___spec__4___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbmap_insert___main___at_rbtree__of___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_rbtree__of___spec__3___rarg), 4, 0);
return x_4;
}
}
obj* l_rbtree_insert___at_rbtree__of___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_rbnode_insert___at_rbtree__of___spec__4___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_rbtree_insert___at_rbtree__of___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_insert___at_rbtree__of___spec__2___rarg), 3, 0);
return x_4;
}
}
obj* l_list_foldl___main___at_rbtree__of___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
x_11 = l_rbnode_insert___at_rbtree__of___spec__4___rarg(x_0, x_1, x_4, x_9);
x_1 = x_11;
x_2 = x_6;
goto _start;
}
}
}
obj* l_list_foldl___main___at_rbtree__of___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldl___main___at_rbtree__of___spec__6___rarg), 3, 0);
return x_4;
}
}
obj* l_rbtree_from__list___at_rbtree__of___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = l_list_foldl___main___at_rbtree__of___spec__6___rarg(x_2, x_4, x_0);
return x_5;
}
}
obj* l_rbtree_from__list___at_rbtree__of___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree_from__list___at_rbtree__of___spec__1___rarg), 3, 0);
return x_2;
}
}
obj* l_rbtree__of___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_1);
x_4 = l_rbtree_from__list___at_rbtree__of___spec__1___rarg(x_0, lean::box(0), x_2);
return x_4;
}
}
obj* l_rbtree__of(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbtree__of___rarg), 3, 0);
return x_2;
}
}
void initialize_init_data_rbmap_basic();
static bool _G_initialized = false;
void initialize_init_data_rbtree_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_rbmap_basic();
 l_rbtree = _init_l_rbtree();
lean::mark_persistent(l_rbtree);
 l_rbtree_has__repr___rarg___closed__1 = _init_l_rbtree_has__repr___rarg___closed__1();
lean::mark_persistent(l_rbtree_has__repr___rarg___closed__1);
}
