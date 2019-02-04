// Lean compiler output
// Module: init.lean.disjoint_set
// Imports: init.data.hashmap.basic
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_hashmap__imp_find___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_merge___main(obj*);
obj* l_mk__d__hashmap___at_lean_mk__disjoint__set___spec__1(obj*, obj*, obj*);
obj* l___private_3363165505__find__aux___main(obj*);
obj* l___private_3363165505__find__aux(obj*);
obj* l_lean_disjoint__set_rank___main(obj*);
obj* l_hashmap__imp_insert___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_merge(obj*);
obj* l_mk__hashmap__imp___rarg(obj*);
obj* l_lean_disjoint__set_merge___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_find___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_mk__disjoint__set___rarg(obj*, obj*);
obj* l___private_3363165505__find__aux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1(obj*);
obj* l_lean_disjoint__set_find___main(obj*);
obj* l_lean_mk__disjoint__set(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_d__hashmap_size___rarg(obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__4(obj*);
obj* l_lean_disjoint__set_rank___rarg(obj*, obj*, obj*, obj*);
obj* l___private_3363165505__find__aux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__2(obj*);
obj* l_lean_disjoint__set_rank___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_find(obj*);
obj* l_lean_disjoint__set_merge___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_d__hashmap_insert___at_lean_disjoint__set_merge___main___spec__3(obj*);
obj* l_lean_disjoint__set_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_disjoint__set_rank(obj*);
obj* l_mk__d__hashmap___at_lean_mk__disjoint__set___spec__1___rarg(obj*);
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
obj* l___private_3363165505__find__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_12; 
lean::dec(x_6);
lean::inc(x_3);
lean::inc(x_4);
lean::inc(x_1);
lean::inc(x_0);
x_12 = l_hashmap__imp_find___rarg(x_0, x_1, x_4, x_3);
if (lean::obj_tag(x_12) == 0)
{
obj* x_18; 
lean::dec(x_4);
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_3);
lean::cnstr_set(x_18, 1, x_5);
return x_18;
}
else
{
obj* x_20; obj* x_23; obj* x_27; 
lean::dec(x_5);
x_20 = lean::cnstr_get(x_12, 0);
lean::inc(x_20);
lean::dec(x_12);
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
lean::inc(x_23);
lean::inc(x_0);
x_27 = lean::apply_2(x_0, x_23, x_3);
if (lean::obj_tag(x_27) == 0)
{
obj* x_30; obj* x_31; 
lean::dec(x_20);
lean::dec(x_27);
x_30 = lean::mk_nat_obj(1u);
x_31 = lean::nat_sub(x_2, x_30);
lean::dec(x_30);
lean::dec(x_2);
x_2 = x_31;
x_3 = x_23;
goto _start;
}
else
{
lean::dec(x_23);
lean::dec(x_27);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_20;
}
}
}
else
{
obj* x_46; 
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_3);
lean::cnstr_set(x_46, 1, x_5);
return x_46;
}
}
}
obj* l___private_3363165505__find__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3363165505__find__aux___main___rarg), 5, 0);
return x_2;
}
}
obj* l___private_3363165505__find__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_3363165505__find__aux___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_3363165505__find__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3363165505__find__aux___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_disjoint__set_find___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_2);
x_5 = l_d__hashmap_size___rarg(x_2);
x_6 = l___private_3363165505__find__aux___main___rarg(x_0, x_1, x_5, x_3, x_2);
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
x_6 = l___private_3363165505__find__aux___main___rarg(x_0, x_1, x_5, x_3, x_2);
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
obj* l_lean_disjoint__set_merge___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_12; obj* x_17; obj* x_18; obj* x_20; obj* x_23; 
lean::inc(x_2);
x_6 = l_d__hashmap_size___rarg(x_2);
lean::inc(x_2);
lean::inc(x_3);
lean::inc(x_6);
lean::inc(x_1);
lean::inc(x_0);
x_12 = l___private_3363165505__find__aux___main___rarg(x_0, x_1, x_6, x_3, x_2);
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_1);
lean::inc(x_0);
x_17 = l___private_3363165505__find__aux___main___rarg(x_0, x_1, x_6, x_4, x_2);
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_17, 0);
lean::inc(x_20);
lean::inc(x_0);
x_23 = lean::apply_2(x_0, x_18, x_20);
if (lean::obj_tag(x_23) == 0)
{
obj* x_25; obj* x_28; obj* x_31; 
lean::dec(x_23);
x_25 = lean::cnstr_get(x_12, 1);
lean::inc(x_25);
lean::dec(x_12);
x_28 = lean::cnstr_get(x_17, 1);
lean::inc(x_28);
lean::dec(x_17);
x_31 = lean::nat_dec_lt(x_25, x_28);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; 
lean::dec(x_31);
x_33 = lean::nat_dec_eq(x_25, x_28);
lean::dec(x_25);
if (lean::obj_tag(x_33) == 0)
{
obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_28);
lean::dec(x_33);
x_37 = lean::mk_nat_obj(0u);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_3);
lean::cnstr_set(x_38, 1, x_37);
x_39 = l_hashmap__imp_insert___rarg(x_0, x_1, x_2, x_4, x_38);
return x_39;
}
else
{
obj* x_41; obj* x_43; obj* x_46; obj* x_47; obj* x_48; obj* x_52; obj* x_53; 
lean::dec(x_33);
x_41 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_4);
lean::cnstr_set(x_43, 1, x_41);
lean::inc(x_1);
lean::inc(x_0);
x_46 = l_hashmap__imp_insert___rarg(x_0, x_1, x_2, x_3, x_43);
x_47 = lean::mk_nat_obj(1u);
x_48 = lean::nat_add(x_28, x_47);
lean::dec(x_47);
lean::dec(x_28);
lean::inc(x_4);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_4);
lean::cnstr_set(x_52, 1, x_48);
x_53 = l_hashmap__imp_insert___rarg(x_0, x_1, x_46, x_4, x_52);
return x_53;
}
}
else
{
obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_25);
lean::dec(x_28);
lean::dec(x_31);
x_57 = lean::mk_nat_obj(0u);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_4);
lean::cnstr_set(x_58, 1, x_57);
x_59 = l_hashmap__imp_insert___rarg(x_0, x_1, x_2, x_3, x_58);
return x_59;
}
}
else
{
lean::dec(x_23);
lean::dec(x_4);
lean::dec(x_12);
lean::dec(x_17);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
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
