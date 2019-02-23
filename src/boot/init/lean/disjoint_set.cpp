// Lean compiler output
// Module: init.lean.disjoint_set
// Imports: init.data.hashmap.basic
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
obj* l_mk__hashmap__imp___rarg(obj*);
obj* l_lean_disjoint__set_merge(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_merge___boxed(obj*);
obj* l_lean_disjoint__set_rank___boxed(obj*);
obj* l_hashmap__imp_insert___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_find___rarg(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l___private_init_lean_disjoint__set_1__find__aux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_disjoint__set_1__find__aux___main(obj*);
obj* l_lean_disjoint__set_rank___main___rarg(obj*, obj*, obj*, obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1___boxed(obj*);
obj* l_lean_disjoint__set_merge___main___boxed(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_rank(obj*);
obj* l_lean_disjoint__set_merge___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_disjoint__set_1__find__aux(obj*);
obj* l_lean_mk__disjoint__set___rarg___boxed(obj*, obj*);
obj* l_lean_disjoint__set_merge___main(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_lean_mk__disjoint__set___rarg(obj*, obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_d__hashmap_size___rarg(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1(obj*);
obj* l_lean_mk__disjoint__set(obj*);
obj* l_lean_disjoint__set_rank___main(obj*);
obj* l_lean_mk__disjoint__set___boxed(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2___boxed(obj*);
obj* l_lean_disjoint__set_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_disjoint__set_1__find__aux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_mk__d__hashmap___at_lean_mk__disjoint__set___spec__1___boxed(obj*, obj*, obj*);
obj* l_mk__d__hashmap___at_lean_mk__disjoint__set___spec__1___rarg(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_disjoint__set_1__find__aux___boxed(obj*);
obj* l_lean_disjoint__set_rank___main___boxed(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_mk__d__hashmap___at_lean_mk__disjoint__set___spec__1(obj*, obj*, obj*);
obj* l_lean_disjoint__set_find___main___boxed(obj*);
obj* l_lean_disjoint__set_merge___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_rank___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_find(obj*);
obj* l___private_init_lean_disjoint__set_1__find__aux___main___boxed(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__4(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__4___boxed(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_lean_disjoint__set_find___boxed(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__3___boxed(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_find___rarg(obj*, obj*, obj*, obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_find___main(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__3(obj*);
obj* l_mk__d__hashmap___at_lean_mk__disjoint__set___spec__1___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mk__hashmap__imp___rarg(x_0);
return x_1;
}
}
obj* l_mk__d__hashmap___at_lean_mk__disjoint__set___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_mk__d__hashmap___at_lean_mk__disjoint__set___spec__1___rarg), 1, 0);
return x_3;
}
}
obj* l_lean_mk__disjoint__set___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(8u);
x_3 = l_mk__hashmap__imp___rarg(x_2);
return x_3;
}
}
obj* l_lean_mk__disjoint__set(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_mk__disjoint__set___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_mk__d__hashmap___at_lean_mk__disjoint__set___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_mk__d__hashmap___at_lean_mk__disjoint__set___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_mk__disjoint__set___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_mk__disjoint__set___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_mk__disjoint__set___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_mk__disjoint__set(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_disjoint__set_1__find__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
obj* x_11; 
lean::inc(x_3);
lean::inc(x_4);
lean::inc(x_1);
lean::inc(x_0);
x_11 = l_hashmap__imp_find___rarg(x_0, x_1, x_4, x_3);
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_3);
lean::cnstr_set(x_16, 1, x_5);
return x_16;
}
else
{
obj* x_17; obj* x_20; obj* x_24; uint8 x_25; 
x_17 = lean::cnstr_get(x_11, 0);
lean::inc(x_17);
lean::dec(x_11);
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
lean::inc(x_20);
lean::inc(x_0);
x_24 = lean::apply_2(x_0, x_20, x_3);
x_25 = lean::unbox(x_24);
if (x_25 == 0)
{
obj* x_27; obj* x_28; 
lean::dec(x_17);
x_27 = lean::mk_nat_obj(1u);
x_28 = lean::nat_sub(x_2, x_27);
lean::dec(x_2);
x_2 = x_28;
x_3 = x_20;
goto _start;
}
else
{
lean::dec(x_20);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_17;
}
}
}
else
{
obj* x_40; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_3);
lean::cnstr_set(x_40, 1, x_5);
return x_40;
}
}
}
obj* l___private_init_lean_disjoint__set_1__find__aux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_disjoint__set_1__find__aux___main___rarg), 5, 0);
return x_1;
}
}
obj* l___private_init_lean_disjoint__set_1__find__aux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_disjoint__set_1__find__aux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_disjoint__set_1__find__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_disjoint__set_1__find__aux___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_lean_disjoint__set_1__find__aux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_disjoint__set_1__find__aux___rarg), 5, 0);
return x_1;
}
}
obj* l___private_init_lean_disjoint__set_1__find__aux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_disjoint__set_1__find__aux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_disjoint__set_find___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_d__hashmap_size___rarg(x_2);
x_5 = l___private_init_lean_disjoint__set_1__find__aux___main___rarg(x_0, x_1, x_4, x_3, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
return x_6;
}
}
obj* l_lean_disjoint__set_find___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_disjoint__set_find___main___rarg), 4, 0);
return x_1;
}
}
obj* l_lean_disjoint__set_find___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_disjoint__set_find___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_disjoint__set_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_disjoint__set_find___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_disjoint__set_find(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_disjoint__set_find___rarg), 4, 0);
return x_1;
}
}
obj* l_lean_disjoint__set_find___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_disjoint__set_find(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_disjoint__set_rank___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_d__hashmap_size___rarg(x_2);
x_5 = l___private_init_lean_disjoint__set_1__find__aux___main___rarg(x_0, x_1, x_4, x_3, x_2);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
return x_6;
}
}
obj* l_lean_disjoint__set_rank___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_disjoint__set_rank___main___rarg), 4, 0);
return x_1;
}
}
obj* l_lean_disjoint__set_rank___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_disjoint__set_rank___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_disjoint__set_rank___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_disjoint__set_rank___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_disjoint__set_rank(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_disjoint__set_rank___rarg), 4, 0);
return x_1;
}
}
obj* l_lean_disjoint__set_rank___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_disjoint__set_rank(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_hashmap__imp_insert___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_hashmap__imp_insert___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_hashmap__imp_insert___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__3___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_hashmap__imp_insert___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__4___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_lean_disjoint__set_merge___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_11; obj* x_16; obj* x_17; obj* x_19; obj* x_22; uint8 x_23; 
x_5 = l_d__hashmap_size___rarg(x_2);
lean::inc(x_2);
lean::inc(x_3);
lean::inc(x_5);
lean::inc(x_1);
lean::inc(x_0);
x_11 = l___private_init_lean_disjoint__set_1__find__aux___main___rarg(x_0, x_1, x_5, x_3, x_2);
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_1);
lean::inc(x_0);
x_16 = l___private_init_lean_disjoint__set_1__find__aux___main___rarg(x_0, x_1, x_5, x_4, x_2);
x_17 = lean::cnstr_get(x_11, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 0);
lean::inc(x_19);
lean::inc(x_0);
x_22 = lean::apply_2(x_0, x_17, x_19);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_27; uint8 x_30; 
x_24 = lean::cnstr_get(x_11, 1);
lean::inc(x_24);
lean::dec(x_11);
x_27 = lean::cnstr_get(x_16, 1);
lean::inc(x_27);
lean::dec(x_16);
x_30 = lean::nat_dec_lt(x_24, x_27);
if (x_30 == 0)
{
uint8 x_31; 
x_31 = lean::nat_dec_eq(x_24, x_27);
lean::dec(x_24);
if (x_31 == 0)
{
obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_27);
x_34 = lean::mk_nat_obj(0u);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_3);
lean::cnstr_set(x_35, 1, x_34);
x_36 = l_hashmap__imp_insert___rarg(x_0, x_1, x_2, x_4, x_35);
lean::dec(x_35);
return x_36;
}
else
{
obj* x_38; obj* x_40; obj* x_43; obj* x_45; obj* x_46; obj* x_49; obj* x_50; 
x_38 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_4);
lean::cnstr_set(x_40, 1, x_38);
lean::inc(x_1);
lean::inc(x_0);
x_43 = l_hashmap__imp_insert___rarg(x_0, x_1, x_2, x_3, x_40);
lean::dec(x_40);
x_45 = lean::mk_nat_obj(1u);
x_46 = lean::nat_add(x_27, x_45);
lean::dec(x_27);
lean::inc(x_4);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_4);
lean::cnstr_set(x_49, 1, x_46);
x_50 = l_hashmap__imp_insert___rarg(x_0, x_1, x_43, x_4, x_49);
lean::dec(x_49);
return x_50;
}
}
else
{
obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_24);
lean::dec(x_27);
x_54 = lean::mk_nat_obj(0u);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_4);
lean::cnstr_set(x_55, 1, x_54);
x_56 = l_hashmap__imp_insert___rarg(x_0, x_1, x_2, x_3, x_55);
lean::dec(x_55);
return x_56;
}
}
else
{
lean::dec(x_16);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_3);
lean::dec(x_0);
return x_2;
}
}
}
obj* l_lean_disjoint__set_merge___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_disjoint__set_merge___main___rarg), 5, 0);
return x_1;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__3___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__4___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_disjoint__set_merge___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_disjoint__set_merge___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_disjoint__set_merge___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_disjoint__set_merge___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_lean_disjoint__set_merge(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_disjoint__set_merge___rarg), 5, 0);
return x_1;
}
}
obj* l_lean_disjoint__set_merge___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_disjoint__set_merge(x_0);
lean::dec(x_0);
return x_1;
}
}
void initialize_init_data_hashmap_basic();
static bool _G_initialized = false;
void initialize_init_lean_disjoint__set() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_hashmap_basic();
}
