// Lean compiler output
// Module: init.data.hashmap.basic
// Imports: init.data.array.basic init.data.list.basic init.data.option.basic init.data.hashable
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
obj* l_list_foldl___main___at_hashmap__imp_fold__buckets___spec__1(obj*, obj*, obj*);
obj* l_hashmap__imp_fold__buckets___rarg(obj*, obj*, obj*);
obj* l_d__hashmap_find___rarg(obj*, obj*, obj*, obj*);
obj* l_hashmap_erase(obj*, obj*);
obj* l_mk__hashmap___rarg(obj*);
obj* l_d__hashmap_erase___boxed(obj*, obj*);
obj* l_list_foldl___main___at_hashmap__imp_fold__buckets___spec__1___rarg(obj*, obj*, obj*);
obj* l_hashmap_size___boxed(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_insert___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_mk__hashmap__imp___rarg___closed__1;
obj* l_hashmap_size___rarg(obj*);
obj* l_hashmap__imp_find__aux___main___rarg(obj*, obj*, obj*);
obj* l_hashmap_size(obj*, obj*, obj*, obj*);
obj* l_d__hashmap_insert___rarg(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_hashmap__imp_replace__aux___main(obj*, obj*);
obj* l_d__hashmap_contains___boxed(obj*, obj*);
obj* l_hashmap_size___rarg___boxed(obj*);
obj* l_hashmap__imp_erase__aux___main___boxed(obj*, obj*);
obj* l_hashmap_empty(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_contains__aux___boxed(obj*, obj*);
obj* l_hashmap__imp_erase___rarg(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_hashmap__imp_fold__buckets___spec__1___boxed(obj*, obj*, obj*);
obj* l_hashmap__imp_replace__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_hashmap_insert___boxed(obj*, obj*);
uint8 l_d__hashmap_contains___rarg(obj*, obj*, obj*, obj*);
obj* l_d__hashmap_empty___rarg___boxed(obj*);
obj* l_hashmap_insert___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_d__hashmap_size___rarg___boxed(obj*);
obj* l_d__hashmap_erase(obj*, obj*);
obj* l_hashmap__imp_fold___rarg(obj*, obj*, obj*);
obj* l_d__hashmap_insert(obj*, obj*);
obj* l_hashmap__imp_find___boxed(obj*, obj*);
obj* l_d__hashmap_fold___rarg(obj*, obj*, obj*);
obj* l_hashmap__imp_erase__aux___main(obj*, obj*);
obj* l_hashmap__imp_find__aux(obj*, obj*);
obj* l_hashmap__imp_erase__aux___rarg(obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__iterate__aux___main___at_hashmap__imp_fold__buckets___spec__2(obj*, obj*, obj*);
uint8 l_hashmap_contains___rarg(obj*, obj*, obj*, obj*);
obj* l_d__hashmap_empty(obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__iterate__aux___main___at_hashmap__imp_fold__buckets___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_d__hashmap_fold___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_bucket__array_uwrite___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_mk__d__hashmap___rarg(obj*);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_d__hashmap_find___boxed(obj*, obj*);
obj* l_mk__hashmap___boxed(obj*, obj*, obj*, obj*);
obj* l_bucket__array_uwrite(obj*, obj*);
obj* l_d__hashmap_size(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_contains__aux___rarg___boxed(obj*, obj*, obj*);
obj* l_hashmap_contains___boxed(obj*, obj*);
obj* l_hashmap__imp_replace__aux___main___boxed(obj*, obj*);
obj* l_hashmap_find(obj*, obj*);
obj* l_mk__hashmap__imp(obj*, obj*);
obj* l_d__hashmap_empty___boxed(obj*, obj*, obj*, obj*);
obj* l_mk__hashmap(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_find(obj*, obj*);
obj* l_hashmap__imp_find__aux___rarg(obj*, obj*, obj*);
obj* l_mk__d__hashmap(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_erase___boxed(obj*, obj*);
obj* l_mk__d__hashmap___boxed(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_d__hashmap_insert___boxed(obj*, obj*);
obj* l_bucket__array_uwrite___boxed(obj*, obj*);
obj* l_hashmap__imp_insert___boxed(obj*, obj*);
obj* l_hashmap_fold___rarg(obj*, obj*, obj*);
obj* l_d__hashmap_find(obj*, obj*);
obj* l_d__hashmap_size___rarg(obj*);
obj* l_hashmap__imp_reinsert__aux___boxed(obj*, obj*);
obj* l_hashmap_fold___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_mk__hashmap__imp___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_bucket__array_uwrite___rarg(obj*, usize, obj*, obj*);
obj* l_hashmap_insert(obj*, obj*);
uint8 l_hashmap_empty___rarg(obj*);
obj* l_hashmap__imp_erase(obj*, obj*);
obj* l_d__hashmap_size___boxed(obj*, obj*, obj*, obj*);
obj* l_d__hashmap_fold(obj*, obj*, obj*, obj*, obj*);
obj* l_d__hashmap_erase___rarg(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_mk__idx___boxed(obj*, obj*, obj*);
obj* l_hashmap__imp_erase__aux(obj*, obj*);
obj* l_hashmap_empty___boxed(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_erase__aux___main___rarg(obj*, obj*, obj*);
obj* l_hashmap_fold(obj*, obj*, obj*, obj*, obj*);
obj* l_hashmap_erase___boxed(obj*, obj*);
obj* l_hashmap_contains___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_d__hashmap_contains(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterate__aux___main___at_hashmap__imp_fold__buckets___spec__2___boxed(obj*, obj*, obj*);
obj* l_hashmap__imp_insert(obj*, obj*);
uint8 l_hashmap__imp_contains__aux___rarg(obj*, obj*, obj*);
uint8 l_d__hashmap_empty___rarg(obj*);
obj* l_hashmap_empty___rarg___boxed(obj*);
obj* l_hashmap__imp_replace__aux___boxed(obj*, obj*);
obj* l_hashmap__imp_reinsert__aux(obj*, obj*);
obj* l_hashmap__imp_fold(obj*, obj*, obj*);
obj* l_hashmap__imp_replace__aux(obj*, obj*);
obj* l_hashmap__imp_erase__aux___boxed(obj*, obj*);
obj* l_hashmap_contains(obj*, obj*);
obj* l_hashmap_find___boxed(obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_hashmap__imp_fold__buckets___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_hashmap_erase___rarg(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_fold___boxed(obj*, obj*, obj*);
obj* l_hashmap__imp_find__aux___boxed(obj*, obj*);
obj* l_d__hashmap_contains___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_find___rarg(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_find__aux___main(obj*, obj*);
obj* l_hashmap_find___rarg(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_contains__aux(obj*, obj*);
obj* l_hashmap__imp_find__aux___main___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_hashmap__imp_reinsert__aux___rarg(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_replace__aux___rarg(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_fold__buckets(obj*, obj*, obj*);
usize l_hashmap__imp_mk__idx(obj*, obj*, usize);
obj* l_bucket__array_uwrite___rarg(obj* x_0, usize x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::array_uwrite(x_0, x_1, x_2);
return x_4;
}
}
obj* l_bucket__array_uwrite(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_bucket__array_uwrite___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_bucket__array_uwrite___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; obj* x_5; 
x_4 = lean::unbox_size_t(x_1);
x_5 = l_bucket__array_uwrite___rarg(x_0, x_4, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_bucket__array_uwrite___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_bucket__array_uwrite(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_mk__hashmap__imp___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(8u);
x_2 = lean::mk_array(x_1, x_0);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_mk__hashmap__imp___rarg(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::nat_dec_eq(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::box(0);
x_4 = lean::mk_array(x_0, x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
else
{
obj* x_7; 
lean::dec(x_0);
x_7 = l_mk__hashmap__imp___rarg___closed__1;
return x_7;
}
}
}
obj* l_mk__hashmap__imp(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_mk__hashmap__imp___rarg), 1, 0);
return x_2;
}
}
obj* l_mk__hashmap__imp___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mk__hashmap__imp(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
usize l_hashmap__imp_mk__idx(obj* x_0, obj* x_1, usize x_2) {
_start:
{
usize x_3; 
x_3 = lean::usize_modn(x_2, x_0);
return x_3;
}
}
obj* l_hashmap__imp_mk__idx___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_2);
x_4 = l_hashmap__imp_mk__idx(x_0, x_1, x_3);
x_5 = lean::box_size_t(x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_5;
}
}
obj* l_hashmap__imp_reinsert__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; usize x_8; usize x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::inc(x_1);
x_5 = lean::array_sz(x_1);
lean::inc(x_2);
x_7 = lean::apply_1(x_0, x_2);
x_8 = lean::unbox_size_t(x_7);
x_9 = lean::usize_modn(x_8, x_5);
lean::dec(x_5);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_3);
x_12 = lean::array_uread(x_1, x_9);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::array_uwrite(x_1, x_9, x_13);
lean::dec(x_13);
lean::dec(x_1);
return x_14;
}
}
obj* l_hashmap__imp_reinsert__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_reinsert__aux___rarg), 4, 0);
return x_2;
}
}
obj* l_hashmap__imp_reinsert__aux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap__imp_reinsert__aux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_foldl___main___at_hashmap__imp_fold__buckets___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
x_15 = lean::apply_3(x_0, x_1, x_9, x_11);
x_1 = x_15;
x_2 = x_6;
goto _start;
}
}
}
obj* l_list_foldl___main___at_hashmap__imp_fold__buckets___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldl___main___at_hashmap__imp_fold__buckets___spec__1___rarg), 3, 0);
return x_3;
}
}
obj* l___private_init_data_array_basic_1__iterate__aux___main___at_hashmap__imp_fold__buckets___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; uint8 x_6; 
lean::inc(x_0);
x_5 = lean::array_sz(x_0);
x_6 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_2, x_11);
x_13 = lean::array_read(x_0, x_2);
lean::dec(x_2);
lean::inc(x_1);
x_16 = l_list_foldl___main___at_hashmap__imp_fold__buckets___spec__1___rarg(x_1, x_3, x_13);
x_2 = x_12;
x_3 = x_16;
goto _start;
}
}
}
obj* l___private_init_data_array_basic_1__iterate__aux___main___at_hashmap__imp_fold__buckets___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__iterate__aux___main___at_hashmap__imp_fold__buckets___spec__2___rarg), 4, 0);
return x_3;
}
}
obj* l_hashmap__imp_fold__buckets___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l___private_init_data_array_basic_1__iterate__aux___main___at_hashmap__imp_fold__buckets___spec__2___rarg(x_0, x_2, x_3, x_1);
return x_4;
}
}
obj* l_hashmap__imp_fold__buckets(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_fold__buckets___rarg), 3, 0);
return x_3;
}
}
obj* l_list_foldl___main___at_hashmap__imp_fold__buckets___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_foldl___main___at_hashmap__imp_fold__buckets___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_data_array_basic_1__iterate__aux___main___at_hashmap__imp_fold__buckets___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_data_array_basic_1__iterate__aux___main___at_hashmap__imp_fold__buckets___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_hashmap__imp_fold__buckets___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_hashmap__imp_fold__buckets(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_hashmap__imp_find__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_18; uint8 x_19; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
lean::dec(x_6);
lean::inc(x_1);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_11, x_1);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
lean::dec(x_13);
x_2 = x_8;
goto _start;
}
else
{
obj* x_25; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_0);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_13);
return x_25;
}
}
}
}
obj* l_hashmap__imp_find__aux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_find__aux___main___rarg), 3, 0);
return x_2;
}
}
obj* l_hashmap__imp_find__aux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap__imp_find__aux___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_hashmap__imp_find__aux___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_hashmap__imp_find__aux___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_hashmap__imp_find__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_find__aux___rarg), 3, 0);
return x_2;
}
}
obj* l_hashmap__imp_find__aux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap__imp_find__aux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_hashmap__imp_contains__aux___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_hashmap__imp_find__aux___main___rarg(x_0, x_1, x_2);
x_4 = l_option_is__some___main___rarg(x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_hashmap__imp_contains__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_contains__aux___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_hashmap__imp_contains__aux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_hashmap__imp_contains__aux___rarg(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_hashmap__imp_contains__aux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap__imp_contains__aux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_hashmap__imp_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_8; obj* x_10; usize x_11; usize x_12; obj* x_14; obj* x_16; 
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::dec(x_2);
lean::inc(x_4);
x_8 = lean::array_sz(x_4);
lean::inc(x_3);
x_10 = lean::apply_1(x_1, x_3);
x_11 = lean::unbox_size_t(x_10);
x_12 = lean::usize_modn(x_11, x_8);
lean::dec(x_8);
x_14 = lean::array_uread(x_4, x_12);
lean::dec(x_4);
x_16 = l_hashmap__imp_find__aux___main___rarg(x_0, x_3, x_14);
return x_16;
}
}
obj* l_hashmap__imp_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_find___rarg), 4, 0);
return x_2;
}
}
obj* l_hashmap__imp_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap__imp_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_hashmap__imp_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::mk_nat_obj(0u);
x_7 = l___private_init_data_array_basic_1__iterate__aux___main___at_hashmap__imp_fold__buckets___spec__2___rarg(x_3, x_2, x_6, x_1);
return x_7;
}
}
obj* l_hashmap__imp_fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_fold___rarg), 3, 0);
return x_3;
}
}
obj* l_hashmap__imp_fold___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_hashmap__imp_fold(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_hashmap__imp_replace__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_16; uint8 x_17; 
x_7 = lean::cnstr_get(x_3, 0);
x_9 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_11 = x_3;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_3);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
lean::inc(x_1);
lean::inc(x_0);
x_16 = lean::apply_2(x_0, x_12, x_1);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; 
x_18 = l_hashmap__imp_replace__aux___main___rarg(x_0, x_1, x_2, x_9);
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
obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_21 = x_7;
} else {
 lean::dec(x_7);
 x_21 = lean::box(0);
}
if (lean::is_scalar(x_21)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_21;
}
lean::cnstr_set(x_22, 0, x_1);
lean::cnstr_set(x_22, 1, x_2);
if (lean::is_scalar(x_11)) {
 x_23 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_23 = x_11;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_9);
return x_23;
}
}
}
}
obj* l_hashmap__imp_replace__aux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_replace__aux___main___rarg), 4, 0);
return x_2;
}
}
obj* l_hashmap__imp_replace__aux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap__imp_replace__aux___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_hashmap__imp_replace__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_hashmap__imp_replace__aux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_hashmap__imp_replace__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_replace__aux___rarg), 4, 0);
return x_2;
}
}
obj* l_hashmap__imp_replace__aux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap__imp_replace__aux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_hashmap__imp_erase__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_14; uint8 x_15; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_9 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::inc(x_1);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_10, x_1);
x_15 = lean::unbox(x_14);
if (x_15 == 0)
{
obj* x_16; obj* x_17; 
x_16 = l_hashmap__imp_erase__aux___main___rarg(x_0, x_1, x_7);
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
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
return x_7;
}
}
}
}
obj* l_hashmap__imp_erase__aux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_erase__aux___main___rarg), 3, 0);
return x_2;
}
}
obj* l_hashmap__imp_erase__aux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap__imp_erase__aux___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_hashmap__imp_erase__aux___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_hashmap__imp_erase__aux___main___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_hashmap__imp_erase__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_erase__aux___rarg), 3, 0);
return x_2;
}
}
obj* l_hashmap__imp_erase__aux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap__imp_erase__aux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_hashmap__imp_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_14; usize x_15; usize x_16; obj* x_17; uint8 x_21; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_9 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
lean::inc(x_7);
x_11 = lean::array_sz(x_7);
lean::inc(x_3);
lean::inc(x_1);
x_14 = lean::apply_1(x_1, x_3);
x_15 = lean::unbox_size_t(x_14);
x_16 = lean::usize_modn(x_15, x_11);
x_17 = lean::array_uread(x_7, x_16);
lean::inc(x_17);
lean::inc(x_3);
lean::inc(x_0);
x_21 = l_hashmap__imp_contains__aux___rarg(x_0, x_3, x_17);
if (x_21 == 0)
{
obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; uint8 x_31; 
lean::dec(x_0);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::nat_add(x_5, x_23);
lean::dec(x_5);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_3);
lean::cnstr_set(x_26, 1, x_4);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_17);
x_28 = lean::array_uwrite(x_7, x_16, x_27);
lean::dec(x_27);
lean::dec(x_7);
x_31 = lean::nat_dec_le(x_24, x_11);
if (x_31 == 0)
{
obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_32 = lean::mk_nat_obj(2u);
x_33 = lean::nat_mul(x_11, x_32);
lean::dec(x_11);
x_35 = lean::box(0);
x_36 = lean::mk_array(x_33, x_35);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_reinsert__aux___rarg), 4, 1);
lean::closure_set(x_37, 0, x_1);
x_38 = lean::mk_nat_obj(0u);
x_39 = l___private_init_data_array_basic_1__iterate__aux___main___at_hashmap__imp_fold__buckets___spec__2___rarg(x_28, x_37, x_38, x_36);
if (lean::is_scalar(x_9)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_9;
}
lean::cnstr_set(x_40, 0, x_24);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
else
{
obj* x_43; 
lean::dec(x_11);
lean::dec(x_1);
if (lean::is_scalar(x_9)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_9;
}
lean::cnstr_set(x_43, 0, x_24);
lean::cnstr_set(x_43, 1, x_28);
return x_43;
}
}
else
{
obj* x_46; obj* x_47; obj* x_50; 
lean::dec(x_11);
lean::dec(x_1);
x_46 = l_hashmap__imp_replace__aux___main___rarg(x_0, x_3, x_4, x_17);
x_47 = lean::array_uwrite(x_7, x_16, x_46);
lean::dec(x_46);
lean::dec(x_7);
if (lean::is_scalar(x_9)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_9;
}
lean::cnstr_set(x_50, 0, x_5);
lean::cnstr_set(x_50, 1, x_47);
return x_50;
}
}
}
obj* l_hashmap__imp_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_insert___rarg), 5, 0);
return x_2;
}
}
obj* l_hashmap__imp_insert___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap__imp_insert(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_hashmap__imp_erase___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; usize x_12; usize x_13; obj* x_15; uint8 x_19; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::inc(x_6);
x_9 = lean::array_sz(x_6);
lean::inc(x_3);
x_11 = lean::apply_1(x_1, x_3);
x_12 = lean::unbox_size_t(x_11);
x_13 = lean::usize_modn(x_12, x_9);
lean::dec(x_9);
x_15 = lean::array_uread(x_6, x_13);
lean::inc(x_15);
lean::inc(x_3);
lean::inc(x_0);
x_19 = l_hashmap__imp_contains__aux___rarg(x_0, x_3, x_15);
if (x_19 == 0)
{
lean::dec(x_6);
lean::dec(x_15);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_33; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_25 = x_2;
} else {
 lean::dec(x_2);
 x_25 = lean::box(0);
}
x_26 = lean::mk_nat_obj(1u);
x_27 = lean::nat_sub(x_4, x_26);
lean::dec(x_4);
x_29 = l_hashmap__imp_erase__aux___main___rarg(x_0, x_3, x_15);
x_30 = lean::array_uwrite(x_6, x_13, x_29);
lean::dec(x_29);
lean::dec(x_6);
if (lean::is_scalar(x_25)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_25;
}
lean::cnstr_set(x_33, 0, x_27);
lean::cnstr_set(x_33, 1, x_30);
return x_33;
}
}
}
obj* l_hashmap__imp_erase(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_erase___rarg), 4, 0);
return x_2;
}
}
obj* l_hashmap__imp_erase___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap__imp_erase(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_mk__d__hashmap___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mk__hashmap__imp___rarg(x_0);
return x_1;
}
}
obj* l_mk__d__hashmap(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_mk__d__hashmap___rarg), 1, 0);
return x_4;
}
}
obj* l_mk__d__hashmap___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_mk__d__hashmap(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_d__hashmap_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_hashmap__imp_insert___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_d__hashmap_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_insert___rarg), 5, 0);
return x_2;
}
}
obj* l_d__hashmap_insert___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_d__hashmap_insert(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_d__hashmap_erase___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_hashmap__imp_erase___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_d__hashmap_erase(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_erase___rarg), 4, 0);
return x_2;
}
}
obj* l_d__hashmap_erase___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_d__hashmap_erase(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_d__hashmap_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_hashmap__imp_find___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_d__hashmap_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_find___rarg), 4, 0);
return x_2;
}
}
obj* l_d__hashmap_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_d__hashmap_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_d__hashmap_contains___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = l_hashmap__imp_find___rarg(x_0, x_1, x_2, x_3);
x_5 = l_option_is__some___main___rarg(x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_d__hashmap_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_contains___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_d__hashmap_contains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_d__hashmap_contains___rarg(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_d__hashmap_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_d__hashmap_contains(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_d__hashmap_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_hashmap__imp_fold___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_d__hashmap_fold(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_fold___rarg), 3, 0);
return x_5;
}
}
obj* l_d__hashmap_fold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_d__hashmap_fold(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_d__hashmap_size___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_d__hashmap_size(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_size___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_d__hashmap_size___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_d__hashmap_size___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_d__hashmap_size___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_d__hashmap_size(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
uint8 l_d__hashmap_empty___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = l_d__hashmap_size___rarg(x_0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_1);
if (x_3 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
}
obj* l_d__hashmap_empty(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_empty___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_d__hashmap_empty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_d__hashmap_empty___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_d__hashmap_empty___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_d__hashmap_empty(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_mk__hashmap___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mk__hashmap__imp___rarg(x_0);
return x_1;
}
}
obj* l_mk__hashmap(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_mk__hashmap___rarg), 1, 0);
return x_4;
}
}
obj* l_mk__hashmap___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_mk__hashmap(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_hashmap_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_hashmap__imp_insert___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_hashmap_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap_insert___rarg), 5, 0);
return x_2;
}
}
obj* l_hashmap_insert___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap_insert(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_hashmap_erase___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_hashmap__imp_erase___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_hashmap_erase(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap_erase___rarg), 4, 0);
return x_2;
}
}
obj* l_hashmap_erase___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap_erase(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_hashmap_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_hashmap__imp_find___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_hashmap_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap_find___rarg), 4, 0);
return x_2;
}
}
obj* l_hashmap_find___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap_find(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
uint8 l_hashmap_contains___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = l_hashmap__imp_find___rarg(x_0, x_1, x_2, x_3);
x_5 = l_option_is__some___main___rarg(x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_hashmap_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap_contains___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_hashmap_contains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_hashmap_contains___rarg(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_hashmap_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap_contains(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_hashmap_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_hashmap__imp_fold___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_hashmap_fold(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap_fold___rarg), 3, 0);
return x_5;
}
}
obj* l_hashmap_fold___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_hashmap_fold(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_hashmap_size___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_d__hashmap_size___rarg(x_0);
return x_1;
}
}
obj* l_hashmap_size(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap_size___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_hashmap_size___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_hashmap_size___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_hashmap_size___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_hashmap_size(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
uint8 l_hashmap_empty___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = l_d__hashmap_size___rarg(x_0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_1);
if (x_3 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
}
obj* l_hashmap_empty(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap_empty___rarg___boxed), 1, 0);
return x_4;
}
}
obj* l_hashmap_empty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_hashmap_empty___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_hashmap_empty___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_hashmap_empty(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
void initialize_init_data_array_basic();
void initialize_init_data_list_basic();
void initialize_init_data_option_basic();
void initialize_init_data_hashable();
static bool _G_initialized = false;
void initialize_init_data_hashmap_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_array_basic();
 initialize_init_data_list_basic();
 initialize_init_data_option_basic();
 initialize_init_data_hashable();
 l_mk__hashmap__imp___rarg___closed__1 = _init_l_mk__hashmap__imp___rarg___closed__1();
lean::mark_persistent(l_mk__hashmap__imp___rarg___closed__1);
}
