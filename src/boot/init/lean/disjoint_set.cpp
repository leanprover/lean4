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
obj* l_hashmap__imp_insert___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_find___rarg(obj*, obj*, obj*, obj*);
obj* l_nat_add(obj*, obj*);
obj* l___private_init_lean_disjoint__set_1__find__aux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_disjoint__set_1__find__aux___main(obj*);
obj* l_lean_disjoint__set_rank___main___rarg(obj*, obj*, obj*, obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_rank(obj*);
obj* l_lean_disjoint__set_merge___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_disjoint__set_1__find__aux(obj*);
obj* l_lean_disjoint__set_merge___main(obj*);
uint8 l_nat_dec__eq(obj*, obj*);
obj* l_lean_mk__disjoint__set___rarg(obj*, obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_d__hashmap_size___rarg(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1(obj*);
obj* l_lean_mk__disjoint__set(obj*);
obj* l_lean_disjoint__set_rank___main(obj*);
obj* l_lean_disjoint__set_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_disjoint__set_1__find__aux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_mk__d__hashmap___at_lean_mk__disjoint__set___spec__1___rarg(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_mk__d__hashmap___at_lean_mk__disjoint__set___spec__1(obj*, obj*, obj*);
obj* l_lean_disjoint__set_merge___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_rank___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_find(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__4(obj*);
obj* l_nat_sub(obj*, obj*);
obj* l_hashmap__imp_find___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_find___main(obj*);
uint8 l_nat_dec__lt(obj*, obj*);
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
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_mk__d__hashmap___at_lean_mk__disjoint__set___spec__1___rarg), 1, 0);
return x_6;
}
}
obj* l_lean_mk__disjoint__set___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::mk_nat_obj(8u);
x_5 = l_mk__hashmap__imp___rarg(x_4);
return x_5;
}
}
obj* l_lean_mk__disjoint__set(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_mk__disjoint__set___rarg), 2, 0);
return x_2;
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
obj* x_17; 
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_3);
lean::cnstr_set(x_17, 1, x_5);
return x_17;
}
else
{
obj* x_19; obj* x_22; obj* x_26; uint8 x_27; 
lean::dec(x_5);
x_19 = lean::cnstr_get(x_11, 0);
lean::inc(x_19);
lean::dec(x_11);
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
lean::inc(x_22);
lean::inc(x_0);
x_26 = lean::apply_2(x_0, x_22, x_3);
x_27 = lean::unbox(x_26);
lean::dec(x_26);
if (x_27 == 0)
{
obj* x_30; obj* x_31; 
lean::dec(x_19);
x_30 = lean::mk_nat_obj(1u);
x_31 = lean::nat_sub(x_2, x_30);
lean::dec(x_30);
lean::dec(x_2);
x_2 = x_31;
x_3 = x_22;
goto _start;
}
else
{
lean::dec(x_22);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_19;
}
}
}
else
{
obj* x_44; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_3);
lean::cnstr_set(x_44, 1, x_5);
return x_44;
}
}
}
obj* l___private_init_lean_disjoint__set_1__find__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_disjoint__set_1__find__aux___main___rarg), 5, 0);
return x_2;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_disjoint__set_1__find__aux___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_disjoint__set_find___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_2);
x_5 = l_d__hashmap_size___rarg(x_2);
x_6 = l___private_init_lean_disjoint__set_1__find__aux___main___rarg(x_0, x_1, x_5, x_3, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
return x_7;
}
}
obj* l_lean_disjoint__set_find___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_disjoint__set_find___main___rarg), 4, 0);
return x_2;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_disjoint__set_find___rarg), 4, 0);
return x_2;
}
}
obj* l_lean_disjoint__set_rank___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_2);
x_5 = l_d__hashmap_size___rarg(x_2);
x_6 = l___private_init_lean_disjoint__set_1__find__aux___main___rarg(x_0, x_1, x_5, x_3, x_2);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
return x_7;
}
}
obj* l_lean_disjoint__set_rank___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_disjoint__set_rank___main___rarg), 4, 0);
return x_2;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_disjoint__set_rank___rarg), 4, 0);
return x_2;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1___rarg), 5, 0);
return x_2;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2___rarg), 5, 0);
return x_2;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__3___rarg), 5, 0);
return x_2;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__4___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_disjoint__set_merge___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_12; obj* x_17; obj* x_18; obj* x_20; obj* x_23; uint8 x_24; 
lean::inc(x_2);
x_6 = l_d__hashmap_size___rarg(x_2);
lean::inc(x_2);
lean::inc(x_3);
lean::inc(x_6);
lean::inc(x_1);
lean::inc(x_0);
x_12 = l___private_init_lean_disjoint__set_1__find__aux___main___rarg(x_0, x_1, x_6, x_3, x_2);
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_1);
lean::inc(x_0);
x_17 = l___private_init_lean_disjoint__set_1__find__aux___main___rarg(x_0, x_1, x_6, x_4, x_2);
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
lean::inc(x_0);
x_23 = lean::apply_2(x_0, x_18, x_20);
x_24 = lean::unbox(x_23);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_26; obj* x_29; uint8 x_32; 
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_29 = lean::cnstr_get(x_17, 1);
lean::inc(x_29);
lean::dec(x_17);
x_32 = lean::nat_dec_lt(x_26, x_29);
if (x_32 == 0)
{
uint8 x_33; 
x_33 = lean::nat_dec_eq(x_26, x_29);
lean::dec(x_26);
if (x_33 == 0)
{
obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_29);
x_36 = lean::mk_nat_obj(0u);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_3);
lean::cnstr_set(x_37, 1, x_36);
x_38 = l_hashmap__imp_insert___rarg(x_0, x_1, x_2, x_4, x_37);
return x_38;
}
else
{
obj* x_39; obj* x_41; obj* x_44; obj* x_45; obj* x_46; obj* x_50; obj* x_51; 
x_39 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_4);
lean::cnstr_set(x_41, 1, x_39);
lean::inc(x_1);
lean::inc(x_0);
x_44 = l_hashmap__imp_insert___rarg(x_0, x_1, x_2, x_3, x_41);
x_45 = lean::mk_nat_obj(1u);
x_46 = lean::nat_add(x_29, x_45);
lean::dec(x_45);
lean::dec(x_29);
lean::inc(x_4);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_4);
lean::cnstr_set(x_50, 1, x_46);
x_51 = l_hashmap__imp_insert___rarg(x_0, x_1, x_44, x_4, x_50);
return x_51;
}
}
else
{
obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_26);
lean::dec(x_29);
x_54 = lean::mk_nat_obj(0u);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_4);
lean::cnstr_set(x_55, 1, x_54);
x_56 = l_hashmap__imp_insert___rarg(x_0, x_1, x_2, x_3, x_55);
return x_56;
}
}
else
{
lean::dec(x_17);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
return x_2;
}
}
}
obj* l_lean_disjoint__set_merge___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_disjoint__set_merge___main___rarg), 5, 0);
return x_2;
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_disjoint__set_merge___rarg), 5, 0);
return x_2;
}
}
void initialize_init_data_hashmap_basic();
static bool _G_initialized = false;
void initialize_init_lean_disjoint__set() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_hashmap_basic();
}
