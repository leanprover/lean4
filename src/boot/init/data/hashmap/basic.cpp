// Lean compiler output
// Module: init.data.hashmap.basic
// Imports: init.data.array.basic init.data.list.basic init.data.option.basic init.data.hashable
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* _l_s12_hashmap__imp_s4_find_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s6_insert(obj*, obj*);
obj* _l_s16_mk__hashmap__imp(obj*, obj*);
obj* _l_s10_d__hashmap_s4_find(obj*, obj*);
obj* _l_s12_hashmap__imp_s13_fold__buckets(obj*, obj*, obj*);
obj* _l_s12_hashmap__imp_s10_erase__aux_s6___main_s6___rarg(obj*, obj*, obj*);
obj* _l_s16_mk__hashmap__imp_s6___rarg_s11___closed__1;
obj* _l_s12_hashmap__imp_s4_find(obj*, obj*);
obj* _l_s7_hashmap_s8_contains(obj*, obj*);
obj* _l_s12_hashmap__imp_s9_find__aux(obj*, obj*);
obj* _l_s12_hashmap__imp_s6_insert(obj*, obj*);
obj* _l_s12_hashmap__imp_s9_find__aux_s6___rarg(obj*, obj*, obj*);
obj* _l_s11_mk__hashmap(obj*, obj*, obj*, obj*);
obj* _l_s9_mk__array_s6___rarg(obj*, obj*);
obj* _l_s7_hashmap;
obj* _l_s12_hashmap__imp_s13_contains__aux_s6___rarg_s7___boxed(obj*, obj*, obj*);
size_t _l_s12_hashmap__imp_s7_mk__idx(obj*, obj*, size_t);
obj* _l_s5_array_s5_foldl_s6___rarg(obj*, obj*, obj*);
obj* _l_s7_hashmap_s5_erase_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s12_hashmap__imp_s9_find__aux_s6___main(obj*, obj*);
obj* _l_s10_d__hashmap;
obj* _l_s12_hashmap__imp_s6_insert_s6___rarg(obj*, obj*, obj*, obj*, obj*);
unsigned char _l_s6_option_s8_is__some_s6___main_s6___rarg(obj*);
unsigned char _l_s10_d__hashmap_s5_empty_s6___rarg(obj*);
unsigned char _l_s12_hashmap__imp_s13_contains__aux_s6___rarg(obj*, obj*, obj*);
obj* _l_s12_hashmap__imp_s10_erase__aux(obj*, obj*);
obj* _l_s12_hashmap__imp_s10_erase__aux_s6___rarg(obj*, obj*, obj*);
obj* _l_s16_mk__hashmap__imp_s6___rarg(obj*);
obj* _l_s12_hashmap__imp_s5_erase(obj*, obj*);
obj* _l_s7_hashmap_s4_fold_s6___rarg(obj*, obj*, obj*);
obj* _l_s7_hashmap_s5_empty(obj*, obj*, obj*, obj*);
obj* _l_s12_hashmap__imp_s12_replace__aux_s6___main(obj*, obj*);
obj* _l_s4_list_s5_foldl_s6___main_s4___at_s12_hashmap__imp_s13_fold__buckets_s9___spec__1_s6___rarg(obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s4_size(obj*, obj*, obj*, obj*);
obj* _l_s12_hashmap__imp_s12_replace__aux(obj*, obj*);
obj* _l_s10_d__hashmap_s4_find_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s6_insert_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s7_hashmap_s4_size_s6___rarg(obj*);
unsigned char _l_s7_hashmap_s8_contains_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s5_empty(obj*, obj*, obj*, obj*);
unsigned char _l_s10_d__hashmap_s8_contains_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s4_fold(obj*, obj*, obj*, obj*, obj*);
obj* _l_s12_hashmap__imp_s13_fold__buckets_s6___rarg(obj*, obj*, obj*);
obj* _l_s12_hashmap__imp_s13_contains__aux(obj*, obj*);
obj* _l_s10_d__hashmap_s4_fold_s6___rarg(obj*, obj*, obj*);
obj* _l_s7_hashmap_s4_size(obj*, obj*, obj*, obj*);
obj* _l_s12_hashmap__imp_s13_fold__buckets_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s13_bucket__array_s6_uwrite_s6___rarg(obj*, size_t, obj*, obj*);
obj* _l_s12_hashmap__imp_s4_fold_s6___rarg(obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s4_size_s6___rarg(obj*);
obj* _l_s12_hashmap__imp_s7_mk__idx_s7___boxed(obj*, obj*, obj*);
obj* _l_s12_hashmap__imp_s13_reinsert__aux(obj*, obj*);
obj* _l_s7_hashmap_s4_find(obj*, obj*);
obj* _l_s12_hashmap__imp_s12_replace__aux_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s12_hashmap__imp_s13_reinsert__aux_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s12_hashmap__imp_s9_find__aux_s6___main_s6___rarg(obj*, obj*, obj*);
obj* _l_s13_bucket__array;
obj* _l_s12_hashmap__imp_s12_replace__aux_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s12_hashmap__imp_s10_erase__aux_s6___main(obj*, obj*);
obj* _l_s12_hashmap__imp_s5_erase_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s7_hashmap_s5_empty_s6___rarg_s7___boxed(obj*);
obj* _l_s7_hashmap_s4_fold(obj*, obj*, obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s8_contains_s6___rarg_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s8_contains(obj*, obj*);
obj* _l_s5_array_s6_uwrite_s6___rarg(obj*, size_t, obj*, obj*);
obj* _l_s13_bucket__array_s6_uwrite(obj*, obj*);
obj* _l_s14_mk__d__hashmap(obj*, obj*, obj*, obj*);
obj* _l_s7_hashmap_s5_erase(obj*, obj*);
obj* _l_s10_d__hashmap_s5_empty_s6___rarg_s7___boxed(obj*);
obj* _l_s7_hashmap_s8_contains_s6___rarg_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s13_bucket__array_s6_uwrite_s6___rarg_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s7_hashmap_s6_insert(obj*, obj*);
obj* _l_s10_d__hashmap_s5_erase(obj*, obj*);
obj* _l_s12_hashmap__imp_s4_fold(obj*, obj*, obj*);
obj* _l_s7_hashmap_s4_find_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_list_s5_foldl_s6___main_s4___at_s12_hashmap__imp_s13_fold__buckets_s9___spec__1(obj*, obj*, obj*);
obj* _l_s10_d__hashmap_s5_erase_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s7_hashmap_s6_insert_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s14_mk__d__hashmap_s6___rarg(obj*);
obj* _l_s5_array_s5_uread_s6___rarg(obj*, size_t, obj*);
unsigned char _l_s7_hashmap_s5_empty_s6___rarg(obj*);
obj* _l_s11_mk__hashmap_s6___rarg(obj*);
obj* _init__l_s13_bucket__array() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s13_bucket__array_s6_uwrite_s6___rarg(obj* x_0, size_t x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_3);
x_5 = _l_s5_array_s6_uwrite_s6___rarg(x_0, x_1, x_2, lean::box(0));
return x_5;
}
}
obj* _l_s13_bucket__array_s6_uwrite(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s13_bucket__array_s6_uwrite_s6___rarg_s7___boxed), 4, 0);
return x_4;
}
}
obj* _l_s13_bucket__array_s6_uwrite_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
size_t x_4; obj* x_5; 
x_4 = lean::unbox_size_t(x_1);
x_5 = _l_s13_bucket__array_s6_uwrite_s6___rarg(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _l_s16_mk__hashmap__imp_s6___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::nat_dec_eq(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_2);
x_4 = lean::alloc_cnstr(0, 0, 0);
;
x_5 = _l_s9_mk__array_s6___rarg(x_0, x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
else
{
obj* x_10; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
x_10 = _l_s16_mk__hashmap__imp_s6___rarg_s11___closed__1;
lean::inc(x_10);
return x_10;
}
}
}
obj* _init__l_s16_mk__hashmap__imp_s6___rarg_s11___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
x_1 = lean::mk_nat_obj(8u);
x_2 = _l_s9_mk__array_s6___rarg(x_1, x_0);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* _l_s16_mk__hashmap__imp(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s16_mk__hashmap__imp_s6___rarg), 1, 0);
return x_4;
}
}
size_t _l_s12_hashmap__imp_s7_mk__idx(obj* x_0, obj* x_1, size_t x_2) {
_start:
{
size_t x_4; 
lean::dec(x_1);
x_4 = lean::usize_modn(x_2, x_0);
lean::dec(x_0);
return x_4;
}
}
obj* _l_s12_hashmap__imp_s7_mk__idx_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
size_t x_3; size_t x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_2);
x_4 = _l_s12_hashmap__imp_s7_mk__idx(x_0, x_1, x_3);
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* _l_s12_hashmap__imp_s13_reinsert__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; size_t x_8; size_t x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::inc(x_2);
x_7 = lean::apply_1(x_0, x_2);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_10 = lean::usize_modn(x_8, x_4);
lean::dec(x_4);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_3);
lean::inc(x_1);
x_14 = _l_s5_array_s5_uread_s6___rarg(x_1, x_10, lean::box(0));
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_14);
x_16 = _l_s5_array_s6_uwrite_s6___rarg(x_1, x_10, x_15, lean::box(0));
return x_16;
}
}
obj* _l_s12_hashmap__imp_s13_reinsert__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s12_hashmap__imp_s13_reinsert__aux_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s12_hashmap__imp_s13_fold__buckets_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s12_hashmap__imp_s13_fold__buckets_s6___rarg_s11___lambda__1), 3, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = _l_s5_array_s5_foldl_s6___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s12_hashmap__imp_s13_fold__buckets_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = _l_s4_list_s5_foldl_s6___main_s4___at_s12_hashmap__imp_s13_fold__buckets_s9___spec__1_s6___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* _l_s12_hashmap__imp_s13_fold__buckets(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s12_hashmap__imp_s13_fold__buckets_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s4_list_s5_foldl_s6___main_s4___at_s12_hashmap__imp_s13_fold__buckets_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{

if (lean::obj_tag(x_2) == 0)
{

lean::dec(x_0);
lean::dec(x_2);
return x_1;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::dec(x_5);
lean::inc(x_0);
x_16 = lean::apply_3(x_0, x_1, x_10, x_12);
x_17 = _l_s4_list_s5_foldl_s6___main_s4___at_s12_hashmap__imp_s13_fold__buckets_s9___spec__1_s6___rarg(x_0, x_16, x_7);
x_1 = x_16;
x_2 = x_7;
goto _start;
}
}
}
obj* _l_s4_list_s5_foldl_s6___main_s4___at_s12_hashmap__imp_s13_fold__buckets_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s5_foldl_s6___main_s4___at_s12_hashmap__imp_s13_fold__buckets_s9___spec__1_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s12_hashmap__imp_s9_find__aux_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{

if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::alloc_cnstr(0, 0, 0);
;
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_14; obj* x_19; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
lean::dec(x_7);
lean::inc(x_1);
lean::inc(x_0);
x_19 = lean::apply_2(x_0, x_12, x_1);
if (lean::obj_tag(x_19) == 0)
{
obj* x_22; 
lean::dec(x_19);
lean::dec(x_14);
x_22 = _l_s12_hashmap__imp_s9_find__aux_s6___main_s6___rarg(x_0, x_1, x_9);
x_2 = x_9;
goto _start;
}
else
{
obj* x_27; 
lean::dec(x_19);
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_1);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_14);
return x_27;
}
}
}
}
obj* _l_s12_hashmap__imp_s9_find__aux_s6___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s12_hashmap__imp_s9_find__aux_s6___main_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s12_hashmap__imp_s9_find__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = _l_s12_hashmap__imp_s9_find__aux_s6___main_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s12_hashmap__imp_s9_find__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s12_hashmap__imp_s9_find__aux_s6___rarg), 3, 0);
return x_4;
}
}
unsigned char _l_s12_hashmap__imp_s13_contains__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = _l_s12_hashmap__imp_s9_find__aux_s6___main_s6___rarg(x_0, x_1, x_2);
x_4 = _l_s6_option_s8_is__some_s6___main_s6___rarg(x_3);
return x_4;
}
}
obj* _l_s12_hashmap__imp_s13_contains__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s12_hashmap__imp_s13_contains__aux_s6___rarg_s7___boxed), 3, 0);
return x_4;
}
}
obj* _l_s12_hashmap__imp_s13_contains__aux_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = _l_s12_hashmap__imp_s13_contains__aux_s6___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _l_s12_hashmap__imp_s4_find_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; size_t x_11; size_t x_13; obj* x_15; obj* x_16; 
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::inc(x_3);
x_10 = lean::apply_1(x_1, x_3);
x_11 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_13 = lean::usize_modn(x_11, x_7);
lean::dec(x_7);
x_15 = _l_s5_array_s5_uread_s6___rarg(x_4, x_13, lean::box(0));
x_16 = _l_s12_hashmap__imp_s9_find__aux_s6___main_s6___rarg(x_0, x_3, x_15);
return x_16;
}
}
obj* _l_s12_hashmap__imp_s4_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s12_hashmap__imp_s4_find_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s12_hashmap__imp_s4_fold_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = _l_s12_hashmap__imp_s13_fold__buckets_s6___rarg(x_3, x_1, x_2);
return x_6;
}
}
obj* _l_s12_hashmap__imp_s4_fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s12_hashmap__imp_s4_fold_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s12_hashmap__imp_s12_replace__aux_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{

if (lean::obj_tag(x_3) == 0)
{

lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_16; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_3, 1);
lean::inc(x_9);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_11 = x_3;
}
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
lean::inc(x_1);
lean::inc(x_0);
x_16 = lean::apply_2(x_0, x_12, x_1);
if (lean::obj_tag(x_16) == 0)
{
obj* x_18; obj* x_19; 
lean::dec(x_16);
x_18 = _l_s12_hashmap__imp_s12_replace__aux_s6___main_s6___rarg(x_0, x_1, x_2, x_9);
if (lean::is_scalar(x_11)) {
 x_19 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_19 = x_11;
}
lean::cnstr_set(x_19, 0, x_7);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
else
{
obj* x_23; obj* x_24; 
lean::dec(x_16);
lean::dec(x_7);
lean::dec(x_0);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_1);
lean::cnstr_set(x_23, 1, x_2);
if (lean::is_scalar(x_11)) {
 x_24 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_24 = x_11;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_9);
return x_24;
}
}
}
}
obj* _l_s12_hashmap__imp_s12_replace__aux_s6___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s12_hashmap__imp_s12_replace__aux_s6___main_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s12_hashmap__imp_s12_replace__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = _l_s12_hashmap__imp_s12_replace__aux_s6___main_s6___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s12_hashmap__imp_s12_replace__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s12_hashmap__imp_s12_replace__aux_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s12_hashmap__imp_s10_erase__aux_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{

if (lean::obj_tag(x_2) == 0)
{

lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_14; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_9 = x_2;
}
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::inc(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_10, x_1);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; obj* x_17; 
lean::dec(x_14);
x_16 = _l_s12_hashmap__imp_s10_erase__aux_s6___main_s6___rarg(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_9;
}
lean::cnstr_set(x_17, 0, x_5);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
else
{

lean::dec(x_9);
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_5);
return x_7;
}
}
}
}
obj* _l_s12_hashmap__imp_s10_erase__aux_s6___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s12_hashmap__imp_s10_erase__aux_s6___main_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s12_hashmap__imp_s10_erase__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = _l_s12_hashmap__imp_s10_erase__aux_s6___main_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s12_hashmap__imp_s10_erase__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s12_hashmap__imp_s10_erase__aux_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s12_hashmap__imp_s6_insert_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_14; size_t x_15; size_t x_17; obj* x_19; unsigned char x_23; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_9 = x_2;
}
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
lean::inc(x_3);
lean::inc(x_1);
x_14 = lean::apply_1(x_1, x_3);
x_15 = lean::unbox_size_t(x_14);
lean::dec(x_14);
x_17 = lean::usize_modn(x_15, x_10);
lean::inc(x_7);
x_19 = _l_s5_array_s5_uread_s6___rarg(x_7, x_17, lean::box(0));
lean::inc(x_19);
lean::inc(x_3);
lean::inc(x_0);
x_23 = _l_s12_hashmap__imp_s13_contains__aux_s6___rarg(x_0, x_3, x_19);
if (x_23 == 0)
{
obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_0);
x_25 = lean::mk_nat_obj(1u);
x_26 = lean::nat_add(x_5, x_25);
lean::dec(x_25);
lean::dec(x_5);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_3);
lean::cnstr_set(x_29, 1, x_4);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_19);
x_31 = _l_s5_array_s6_uwrite_s6___rarg(x_7, x_17, x_30, lean::box(0));
x_32 = lean::nat_dec_le(x_26, x_10);
if (lean::obj_tag(x_32) == 0)
{
obj* x_34; obj* x_35; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_32);
x_34 = lean::mk_nat_obj(2u);
x_35 = lean::nat_mul(x_10, x_34);
lean::dec(x_34);
lean::dec(x_10);
x_38 = lean::alloc_cnstr(0, 0, 0);
;
x_39 = _l_s9_mk__array_s6___rarg(x_35, x_38);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(_l_s12_hashmap__imp_s13_reinsert__aux_s6___rarg), 4, 1);
lean::closure_set(x_40, 0, x_1);
x_41 = _l_s12_hashmap__imp_s13_fold__buckets_s6___rarg(x_31, x_39, x_40);
if (lean::is_scalar(x_9)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_9;
}
lean::cnstr_set(x_42, 0, x_26);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
else
{
obj* x_46; 
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_32);
if (lean::is_scalar(x_9)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_9;
}
lean::cnstr_set(x_46, 0, x_26);
lean::cnstr_set(x_46, 1, x_31);
return x_46;
}
}
else
{
obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_10);
lean::dec(x_1);
x_49 = _l_s12_hashmap__imp_s12_replace__aux_s6___main_s6___rarg(x_0, x_3, x_4, x_19);
x_50 = _l_s5_array_s6_uwrite_s6___rarg(x_7, x_17, x_49, lean::box(0));
if (lean::is_scalar(x_9)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_9;
}
lean::cnstr_set(x_51, 0, x_5);
lean::cnstr_set(x_51, 1, x_50);
return x_51;
}
}
}
obj* _l_s12_hashmap__imp_s6_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s12_hashmap__imp_s6_insert_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s12_hashmap__imp_s5_erase_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_11; size_t x_12; size_t x_14; obj* x_17; unsigned char x_21; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
lean::inc(x_3);
x_11 = lean::apply_1(x_1, x_3);
x_12 = lean::unbox_size_t(x_11);
lean::dec(x_11);
x_14 = lean::usize_modn(x_12, x_8);
lean::dec(x_8);
lean::inc(x_6);
x_17 = _l_s5_array_s5_uread_s6___rarg(x_6, x_14, lean::box(0));
lean::inc(x_17);
lean::inc(x_3);
lean::inc(x_0);
x_21 = _l_s12_hashmap__imp_s13_contains__aux_s6___rarg(x_0, x_3, x_17);
if (x_21 == 0)
{

lean::dec(x_17);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_3);
return x_2;
}
else
{
obj* x_28; obj* x_29; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_2);
x_28 = lean::mk_nat_obj(1u);
x_29 = lean::nat_sub(x_4, x_28);
lean::dec(x_28);
lean::dec(x_4);
x_32 = _l_s12_hashmap__imp_s10_erase__aux_s6___main_s6___rarg(x_0, x_3, x_17);
x_33 = _l_s5_array_s6_uwrite_s6___rarg(x_6, x_14, x_32, lean::box(0));
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_29);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
}
}
obj* _l_s12_hashmap__imp_s5_erase(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s12_hashmap__imp_s5_erase_s6___rarg), 4, 0);
return x_4;
}
}
obj* _init__l_s10_d__hashmap() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s14_mk__d__hashmap_s6___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = _l_s16_mk__hashmap__imp_s6___rarg(x_0);
return x_1;
}
}
obj* _l_s14_mk__d__hashmap(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s14_mk__d__hashmap_s6___rarg), 1, 0);
return x_8;
}
}
obj* _l_s10_d__hashmap_s6_insert_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = _l_s12_hashmap__imp_s6_insert_s6___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* _l_s10_d__hashmap_s6_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s10_d__hashmap_s6_insert_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s10_d__hashmap_s5_erase_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = _l_s12_hashmap__imp_s5_erase_s6___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s10_d__hashmap_s5_erase(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s10_d__hashmap_s5_erase_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s10_d__hashmap_s4_find_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = _l_s12_hashmap__imp_s4_find_s6___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s10_d__hashmap_s4_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s10_d__hashmap_s4_find_s6___rarg), 4, 0);
return x_4;
}
}
unsigned char _l_s10_d__hashmap_s8_contains_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; unsigned char x_5; 
x_4 = _l_s12_hashmap__imp_s4_find_s6___rarg(x_0, x_1, x_2, x_3);
x_5 = _l_s6_option_s8_is__some_s6___main_s6___rarg(x_4);
return x_5;
}
}
obj* _l_s10_d__hashmap_s8_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s10_d__hashmap_s8_contains_s6___rarg_s7___boxed), 4, 0);
return x_4;
}
}
obj* _l_s10_d__hashmap_s8_contains_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned char x_4; obj* x_5; 
x_4 = _l_s10_d__hashmap_s8_contains_s6___rarg(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* _l_s10_d__hashmap_s4_fold_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = _l_s12_hashmap__imp_s4_fold_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s10_d__hashmap_s4_fold(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s10_d__hashmap_s4_fold_s6___rarg), 3, 0);
return x_10;
}
}
obj* _l_s10_d__hashmap_s4_size_s6___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _l_s10_d__hashmap_s4_size(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s10_d__hashmap_s4_size_s6___rarg), 1, 0);
return x_8;
}
}
unsigned char _l_s10_d__hashmap_s5_empty_s6___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = _l_s10_d__hashmap_s4_size_s6___rarg(x_0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
unsigned char x_7; 
lean::dec(x_3);
x_7 = 0;
return x_7;
}
else
{
unsigned char x_9; 
lean::dec(x_3);
x_9 = 1;
return x_9;
}
}
}
obj* _l_s10_d__hashmap_s5_empty(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s10_d__hashmap_s5_empty_s6___rarg_s7___boxed), 1, 0);
return x_8;
}
}
obj* _l_s10_d__hashmap_s5_empty_s6___rarg_s7___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = _l_s10_d__hashmap_s5_empty_s6___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* _init__l_s7_hashmap() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s11_mk__hashmap_s6___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = _l_s16_mk__hashmap__imp_s6___rarg(x_0);
return x_1;
}
}
obj* _l_s11_mk__hashmap(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s11_mk__hashmap_s6___rarg), 1, 0);
return x_8;
}
}
obj* _l_s7_hashmap_s6_insert_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = _l_s12_hashmap__imp_s6_insert_s6___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* _l_s7_hashmap_s6_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s7_hashmap_s6_insert_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s7_hashmap_s5_erase_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = _l_s12_hashmap__imp_s5_erase_s6___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s7_hashmap_s5_erase(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s7_hashmap_s5_erase_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s7_hashmap_s4_find_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = _l_s12_hashmap__imp_s4_find_s6___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s7_hashmap_s4_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s7_hashmap_s4_find_s6___rarg), 4, 0);
return x_4;
}
}
unsigned char _l_s7_hashmap_s8_contains_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; unsigned char x_5; 
x_4 = _l_s12_hashmap__imp_s4_find_s6___rarg(x_0, x_1, x_2, x_3);
x_5 = _l_s6_option_s8_is__some_s6___main_s6___rarg(x_4);
return x_5;
}
}
obj* _l_s7_hashmap_s8_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s7_hashmap_s8_contains_s6___rarg_s7___boxed), 4, 0);
return x_4;
}
}
obj* _l_s7_hashmap_s8_contains_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned char x_4; obj* x_5; 
x_4 = _l_s7_hashmap_s8_contains_s6___rarg(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* _l_s7_hashmap_s4_fold_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = _l_s12_hashmap__imp_s4_fold_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s7_hashmap_s4_fold(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s7_hashmap_s4_fold_s6___rarg), 3, 0);
return x_10;
}
}
obj* _l_s7_hashmap_s4_size_s6___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = _l_s10_d__hashmap_s4_size_s6___rarg(x_0);
return x_1;
}
}
obj* _l_s7_hashmap_s4_size(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s7_hashmap_s4_size_s6___rarg), 1, 0);
return x_8;
}
}
unsigned char _l_s7_hashmap_s5_empty_s6___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = _l_s10_d__hashmap_s4_size_s6___rarg(x_0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
unsigned char x_7; 
lean::dec(x_3);
x_7 = 0;
return x_7;
}
else
{
unsigned char x_9; 
lean::dec(x_3);
x_9 = 1;
return x_9;
}
}
}
obj* _l_s7_hashmap_s5_empty(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s7_hashmap_s5_empty_s6___rarg_s7___boxed), 1, 0);
return x_8;
}
}
obj* _l_s7_hashmap_s5_empty_s6___rarg_s7___boxed(obj* x_0) {
_start:
{
unsigned char x_1; obj* x_2; 
x_1 = _l_s7_hashmap_s5_empty_s6___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
void _l_initialize__l_s4_init_s4_data_s5_array_s5_basic();
void _l_initialize__l_s4_init_s4_data_s4_list_s5_basic();
void _l_initialize__l_s4_init_s4_data_s6_option_s5_basic();
void _l_initialize__l_s4_init_s4_data_s8_hashable();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s7_hashmap_s5_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s5_array_s5_basic();
 _l_initialize__l_s4_init_s4_data_s4_list_s5_basic();
 _l_initialize__l_s4_init_s4_data_s6_option_s5_basic();
 _l_initialize__l_s4_init_s4_data_s8_hashable();
 _l_s13_bucket__array = _init__l_s13_bucket__array();
 _l_s16_mk__hashmap__imp_s6___rarg_s11___closed__1 = _init__l_s16_mk__hashmap__imp_s6___rarg_s11___closed__1();
 _l_s10_d__hashmap = _init__l_s10_d__hashmap();
 _l_s7_hashmap = _init__l_s7_hashmap();
}
