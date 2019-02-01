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
#endif
obj* _l_s12_hashmap__imp_s4_find_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s13_disjoint__set_s5_merge_s6___main(obj*);
obj* _l_s14_mk__d__hashmap_s4___at_s4_lean_s17_mk__disjoint__set_s9___spec__1(obj*, obj*, obj*);
obj* _l_s9___private_3363165505__s9_find__aux_s6___main(obj*);
obj* _l_s9___private_3363165505__s9_find__aux(obj*);
obj* _l_s4_lean_s13_disjoint__set_s4_rank_s6___main(obj*);
obj* _l_s12_hashmap__imp_s6_insert_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s13_disjoint__set_s5_merge(obj*);
obj* _l_s16_mk__hashmap__imp_s6___rarg(obj*);
obj* _l_s4_lean_s13_disjoint__set_s5_merge_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s13_disjoint__set_s4_find_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s17_mk__disjoint__set_s6___rarg(obj*, obj*);
obj* _l_s9___private_3363165505__s9_find__aux_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__4_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__1(obj*);
obj* _l_s4_lean_s13_disjoint__set_s4_find_s6___main(obj*);
obj* _l_s4_lean_s17_mk__disjoint__set(obj*);
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__3_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s4_size_s6___rarg(obj*);
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__4(obj*);
obj* _l_s4_lean_s13_disjoint__set_s4_rank_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s9___private_3363165505__s9_find__aux_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__2(obj*);
obj* _l_s4_lean_s13_disjoint__set_s4_rank_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s13_disjoint__set_s4_find(obj*);
obj* _l_s4_lean_s13_disjoint__set_s5_merge_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__3(obj*);
obj* _l_s4_lean_s13_disjoint__set_s4_find_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s13_disjoint__set_s4_rank(obj*);
obj* _l_s14_mk__d__hashmap_s4___at_s4_lean_s17_mk__disjoint__set_s9___spec__1_s6___rarg(obj*);
obj* _l_s4_lean_s17_mk__disjoint__set_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::mk_nat_obj(8u);
x_5 = _l_s16_mk__hashmap__imp_s6___rarg(x_4);
return x_5;
}
}
obj* _l_s4_lean_s17_mk__disjoint__set(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s17_mk__disjoint__set_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s14_mk__d__hashmap_s4___at_s4_lean_s17_mk__disjoint__set_s9___spec__1_s6___rarg(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s16_mk__hashmap__imp_s6___rarg(x_0);
return x_1;
}
}
obj* _l_s14_mk__d__hashmap_s4___at_s4_lean_s17_mk__disjoint__set_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s14_mk__d__hashmap_s4___at_s4_lean_s17_mk__disjoint__set_s9___spec__1_s6___rarg), 1, 0);
return x_6;
}
}
obj* _l_s9___private_3363165505__s9_find__aux_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_12 = _l_s12_hashmap__imp_s4_find_s6___rarg(x_0, x_1, x_4, x_3);
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
obj* x_30; obj* x_31; obj* x_34; 
lean::dec(x_20);
lean::dec(x_27);
x_30 = lean::mk_nat_obj(1u);
x_31 = lean::nat_sub(x_2, x_30);
lean::dec(x_30);
lean::dec(x_2);
x_34 = _l_s9___private_3363165505__s9_find__aux_s6___main_s6___rarg(x_0, x_1, x_31, x_23, x_4);
return x_34;
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
obj* _l_s9___private_3363165505__s9_find__aux_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_3363165505__s9_find__aux_s6___main_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s9___private_3363165505__s9_find__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; 
x_5 = _l_s9___private_3363165505__s9_find__aux_s6___main_s6___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* _l_s9___private_3363165505__s9_find__aux(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_3363165505__s9_find__aux_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s4_lean_s13_disjoint__set_s4_find_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_2);
x_5 = _l_s10_d__hashmap_s4_size_s6___rarg(x_2);
x_6 = _l_s9___private_3363165505__s9_find__aux_s6___main_s6___rarg(x_0, x_1, x_5, x_3, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
return x_7;
}
}
obj* _l_s4_lean_s13_disjoint__set_s4_find_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s13_disjoint__set_s4_find_s6___main_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_lean_s13_disjoint__set_s4_find_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; 
x_4 = _l_s4_lean_s13_disjoint__set_s4_find_s6___main_s6___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s4_lean_s13_disjoint__set_s4_find(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s13_disjoint__set_s4_find_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_lean_s13_disjoint__set_s4_rank_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_2);
x_5 = _l_s10_d__hashmap_s4_size_s6___rarg(x_2);
x_6 = _l_s9___private_3363165505__s9_find__aux_s6___main_s6___rarg(x_0, x_1, x_5, x_3, x_2);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
return x_7;
}
}
obj* _l_s4_lean_s13_disjoint__set_s4_rank_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s13_disjoint__set_s4_rank_s6___main_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_lean_s13_disjoint__set_s4_rank_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; 
x_4 = _l_s4_lean_s13_disjoint__set_s4_rank_s6___main_s6___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s4_lean_s13_disjoint__set_s4_rank(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s13_disjoint__set_s4_rank_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_lean_s13_disjoint__set_s5_merge_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_12; obj* x_17; obj* x_18; obj* x_20; obj* x_23; 
lean::inc(x_2);
x_6 = _l_s10_d__hashmap_s4_size_s6___rarg(x_2);
lean::inc(x_2);
lean::inc(x_3);
lean::inc(x_6);
lean::inc(x_1);
lean::inc(x_0);
x_12 = _l_s9___private_3363165505__s9_find__aux_s6___main_s6___rarg(x_0, x_1, x_6, x_3, x_2);
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_1);
lean::inc(x_0);
x_17 = _l_s9___private_3363165505__s9_find__aux_s6___main_s6___rarg(x_0, x_1, x_6, x_4, x_2);
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
x_39 = _l_s12_hashmap__imp_s6_insert_s6___rarg(x_0, x_1, x_2, x_4, x_38);
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
x_46 = _l_s12_hashmap__imp_s6_insert_s6___rarg(x_0, x_1, x_2, x_3, x_43);
x_47 = lean::mk_nat_obj(1u);
x_48 = lean::nat_add(x_28, x_47);
lean::dec(x_47);
lean::dec(x_28);
lean::inc(x_4);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_4);
lean::cnstr_set(x_52, 1, x_48);
x_53 = _l_s12_hashmap__imp_s6_insert_s6___rarg(x_0, x_1, x_46, x_4, x_52);
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
x_59 = _l_s12_hashmap__imp_s6_insert_s6___rarg(x_0, x_1, x_2, x_3, x_58);
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
obj* _l_s4_lean_s13_disjoint__set_s5_merge_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s13_disjoint__set_s5_merge_s6___main_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; 
x_5 = _l_s12_hashmap__imp_s6_insert_s6___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__1(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__1_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; 
x_5 = _l_s12_hashmap__imp_s6_insert_s6___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__2(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__2_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__3_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; 
x_5 = _l_s12_hashmap__imp_s6_insert_s6___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__3(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__3_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__4_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; 
x_5 = _l_s12_hashmap__imp_s6_insert_s6___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* _l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__4(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s10_d__hashmap_s6_insert_s4___at_s4_lean_s13_disjoint__set_s5_merge_s6___main_s9___spec__4_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s4_lean_s13_disjoint__set_s5_merge_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; 
x_5 = _l_s4_lean_s13_disjoint__set_s5_merge_s6___main_s6___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* _l_s4_lean_s13_disjoint__set_s5_merge(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s13_disjoint__set_s5_merge_s6___rarg), 5, 0);
return x_2;
}
}
void _l_initialize__l_s4_init_s4_data_s7_hashmap_s5_basic();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s13_disjoint__set() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s7_hashmap_s5_basic();
}
