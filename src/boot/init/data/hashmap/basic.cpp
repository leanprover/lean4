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
obj* l_list_foldl___main___at_hashmap__imp_fold__buckets___spec__1___rarg(obj*, obj*, obj*);
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
obj* l_hashmap_empty(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_erase___rarg(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_replace__aux___main___rarg(obj*, obj*, obj*, obj*);
uint8 l_d__hashmap_contains___rarg(obj*, obj*, obj*, obj*);
obj* l_d__hashmap_empty___rarg___boxed(obj*);
obj* l_hashmap_insert___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_d__hashmap_erase(obj*, obj*);
obj* l_hashmap__imp_fold___rarg(obj*, obj*, obj*);
obj* l_d__hashmap_insert(obj*, obj*);
obj* l_d__hashmap_fold___rarg(obj*, obj*, obj*);
obj* l_hashmap__imp_erase__aux___main(obj*, obj*);
obj* l_hashmap__imp_find__aux(obj*, obj*);
obj* l_hashmap__imp_erase__aux___rarg(obj*, obj*, obj*);
uint8 l_hashmap_contains___rarg(obj*, obj*, obj*, obj*);
obj* l_d__hashmap_empty(obj*, obj*, obj*, obj*);
obj* l_bucket__array_uwrite___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_mk__d__hashmap___rarg(obj*);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_bucket__array_uwrite(obj*, obj*);
obj* l_d__hashmap_size(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_contains__aux___rarg___boxed(obj*, obj*, obj*);
obj* l_hashmap_find(obj*, obj*);
obj* l_mk__hashmap__imp(obj*, obj*);
obj* l_mk__hashmap(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_find(obj*, obj*);
obj* l_hashmap__imp_find__aux___rarg(obj*, obj*, obj*);
obj* l_mk__d__hashmap(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_hashmap__imp_fold__buckets___rarg___lambda__1(obj*, obj*, obj*);
obj* l_hashmap_fold___rarg(obj*, obj*, obj*);
obj* l_d__hashmap_find(obj*, obj*);
obj* l_d__hashmap_size___rarg(obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
usize usize_modn(usize, obj*);
}
obj* l_array_foldl___rarg(obj*, obj*, obj*);
obj* l_bucket__array_uwrite___rarg(obj*, usize, obj*, obj*);
obj* l_hashmap_insert(obj*, obj*);
uint8 l_hashmap_empty___rarg(obj*);
obj* l_hashmap__imp_erase(obj*, obj*);
obj* l_d__hashmap_fold(obj*, obj*, obj*, obj*, obj*);
obj* l_d__hashmap_erase___rarg(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_mk__idx___boxed(obj*, obj*, obj*);
obj* l_hashmap__imp_erase__aux(obj*, obj*);
obj* l_hashmap__imp_erase__aux___main___rarg(obj*, obj*, obj*);
obj* l_hashmap_fold(obj*, obj*, obj*, obj*, obj*);
obj* l_hashmap_contains___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_d__hashmap_contains(obj*, obj*);
obj* l_hashmap__imp_insert(obj*, obj*);
uint8 l_hashmap__imp_contains__aux___rarg(obj*, obj*, obj*);
uint8 l_d__hashmap_empty___rarg(obj*);
obj* l_hashmap_empty___rarg___boxed(obj*);
obj* l_hashmap__imp_reinsert__aux(obj*, obj*);
obj* l_hashmap__imp_fold(obj*, obj*, obj*);
obj* l_d__hashmap;
obj* l_hashmap__imp_replace__aux(obj*, obj*);
obj* l_hashmap_contains(obj*, obj*);
obj* l_bucket__array;
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_hashmap;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_hashmap_erase___rarg(obj*, obj*, obj*, obj*);
obj* l_d__hashmap_contains___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_find___rarg(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_find__aux___main(obj*, obj*);
obj* l_hashmap_find___rarg(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_contains__aux(obj*, obj*);
obj* l_hashmap__imp_reinsert__aux___rarg(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_replace__aux___rarg(obj*, obj*, obj*, obj*);
obj* l_hashmap__imp_fold__buckets(obj*, obj*, obj*);
usize l_hashmap__imp_mk__idx(obj*, obj*, usize);
obj* _init_l_bucket__array() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_bucket__array_uwrite___rarg(obj* x_0, usize x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_3);
x_5 = lean::array_uwrite(x_0, x_1, x_2);
lean::dec(x_2);
lean::dec(x_0);
return x_5;
}
}
obj* l_bucket__array_uwrite(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_bucket__array_uwrite___rarg___boxed), 4, 0);
return x_4;
}
}
obj* l_bucket__array_uwrite___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; obj* x_5; 
x_4 = lean::unbox_size_t(x_1);
x_5 = l_bucket__array_uwrite___rarg(x_0, x_4, x_2, x_3);
return x_5;
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
obj* x_8; 
lean::dec(x_1);
lean::dec(x_0);
x_8 = l_mk__hashmap__imp___rarg___closed__1;
lean::inc(x_8);
return x_8;
}
}
}
obj* l_mk__hashmap__imp(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_mk__hashmap__imp___rarg), 1, 0);
return x_4;
}
}
usize l_hashmap__imp_mk__idx(obj* x_0, obj* x_1, usize x_2) {
_start:
{
usize x_4; 
lean::dec(x_1);
x_4 = lean::usize_modn(x_2, x_0);
lean::dec(x_0);
return x_4;
}
}
obj* l_hashmap__imp_mk__idx___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; obj* x_5; 
x_3 = lean::unbox_size_t(x_2);
x_4 = l_hashmap__imp_mk__idx(x_0, x_1, x_3);
x_5 = lean::box_size_t(x_4);
return x_5;
}
}
obj* l_hashmap__imp_reinsert__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; usize x_8; usize x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::inc(x_1);
x_5 = lean::array_get_size(x_1);
lean::inc(x_2);
x_7 = lean::apply_1(x_0, x_2);
x_8 = lean::unbox_size_t(x_7);
lean::dec(x_7);
x_10 = lean::usize_modn(x_8, x_5);
lean::dec(x_5);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_3);
x_13 = lean::array_uread(x_1, x_10);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::array_uwrite(x_1, x_10, x_14);
lean::dec(x_14);
lean::dec(x_1);
return x_15;
}
}
obj* l_hashmap__imp_reinsert__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_reinsert__aux___rarg), 4, 0);
return x_4;
}
}
obj* l_list_foldl___main___at_hashmap__imp_fold__buckets___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_16; 
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
x_1 = x_16;
x_2 = x_7;
goto _start;
}
}
}
obj* l_list_foldl___main___at_hashmap__imp_fold__buckets___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_list_foldl___main___at_hashmap__imp_fold__buckets___spec__1___rarg), 3, 0);
return x_6;
}
}
obj* l_hashmap__imp_fold__buckets___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_foldl___main___at_hashmap__imp_fold__buckets___spec__1___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* l_hashmap__imp_fold__buckets___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_fold__buckets___rarg___lambda__1), 3, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_array_foldl___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_hashmap__imp_fold__buckets(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_fold__buckets___rarg), 3, 0);
return x_6;
}
}
obj* l_hashmap__imp_find__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_14; obj* x_19; uint8 x_20; 
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
x_20 = lean::unbox(x_19);
lean::dec(x_19);
if (x_20 == 0)
{
lean::dec(x_14);
x_2 = x_9;
goto _start;
}
else
{
obj* x_27; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_0);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_14);
return x_27;
}
}
}
}
obj* l_hashmap__imp_find__aux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_find__aux___main___rarg), 3, 0);
return x_4;
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
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_find__aux___rarg), 3, 0);
return x_4;
}
}
uint8 l_hashmap__imp_contains__aux___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_hashmap__imp_find__aux___main___rarg(x_0, x_1, x_2);
x_4 = l_option_is__some___main___rarg(x_3);
return x_4;
}
}
obj* l_hashmap__imp_contains__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_contains__aux___rarg___boxed), 3, 0);
return x_4;
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
obj* l_hashmap__imp_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_8; obj* x_10; usize x_11; usize x_13; obj* x_15; obj* x_17; 
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::dec(x_2);
lean::inc(x_4);
x_8 = lean::array_get_size(x_4);
lean::inc(x_3);
x_10 = lean::apply_1(x_1, x_3);
x_11 = lean::unbox_size_t(x_10);
lean::dec(x_10);
x_13 = lean::usize_modn(x_11, x_8);
lean::dec(x_8);
x_15 = lean::array_uread(x_4, x_13);
lean::dec(x_4);
x_17 = l_hashmap__imp_find__aux___main___rarg(x_0, x_3, x_15);
return x_17;
}
}
obj* l_hashmap__imp_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_find___rarg), 4, 0);
return x_4;
}
}
obj* l_hashmap__imp_fold___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_hashmap__imp_fold__buckets___rarg(x_3, x_1, x_2);
return x_6;
}
}
obj* l_hashmap__imp_fold(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_fold___rarg), 3, 0);
return x_6;
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
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_19; obj* x_20; 
x_19 = l_hashmap__imp_replace__aux___main___rarg(x_0, x_1, x_2, x_9);
if (lean::is_scalar(x_11)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_11;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
else
{
obj* x_23; obj* x_24; 
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
obj* l_hashmap__imp_replace__aux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_replace__aux___main___rarg), 4, 0);
return x_4;
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
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_replace__aux___rarg), 4, 0);
return x_4;
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
x_15 = lean::unbox(x_14);
lean::dec(x_14);
if (x_15 == 0)
{
obj* x_17; obj* x_18; 
x_17 = l_hashmap__imp_erase__aux___main___rarg(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_9;
}
lean::cnstr_set(x_18, 0, x_5);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
else
{
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_5);
lean::dec(x_0);
return x_7;
}
}
}
}
obj* l_hashmap__imp_erase__aux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_erase__aux___main___rarg), 3, 0);
return x_4;
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
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_erase__aux___rarg), 3, 0);
return x_4;
}
}
obj* l_hashmap__imp_insert___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_14; usize x_15; usize x_17; obj* x_18; uint8 x_22; 
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
lean::inc(x_7);
x_11 = lean::array_get_size(x_7);
lean::inc(x_3);
lean::inc(x_1);
x_14 = lean::apply_1(x_1, x_3);
x_15 = lean::unbox_size_t(x_14);
lean::dec(x_14);
x_17 = lean::usize_modn(x_15, x_11);
x_18 = lean::array_uread(x_7, x_17);
lean::inc(x_18);
lean::inc(x_3);
lean::inc(x_0);
x_22 = l_hashmap__imp_contains__aux___rarg(x_0, x_3, x_18);
if (x_22 == 0)
{
obj* x_24; obj* x_25; obj* x_28; obj* x_29; obj* x_30; uint8 x_33; 
lean::dec(x_0);
x_24 = lean::mk_nat_obj(1u);
x_25 = lean::nat_add(x_5, x_24);
lean::dec(x_24);
lean::dec(x_5);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_3);
lean::cnstr_set(x_28, 1, x_4);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_18);
x_30 = lean::array_uwrite(x_7, x_17, x_29);
lean::dec(x_29);
lean::dec(x_7);
x_33 = lean::nat_dec_le(x_25, x_11);
if (x_33 == 0)
{
obj* x_34; obj* x_35; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_34 = lean::mk_nat_obj(2u);
x_35 = lean::nat_mul(x_11, x_34);
lean::dec(x_34);
lean::dec(x_11);
x_38 = lean::box(0);
x_39 = lean::mk_array(x_35, x_38);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_reinsert__aux___rarg), 4, 1);
lean::closure_set(x_40, 0, x_1);
x_41 = l_hashmap__imp_fold__buckets___rarg(x_30, x_39, x_40);
if (lean::is_scalar(x_9)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_9;
}
lean::cnstr_set(x_42, 0, x_25);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
else
{
obj* x_45; 
lean::dec(x_11);
lean::dec(x_1);
if (lean::is_scalar(x_9)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_9;
}
lean::cnstr_set(x_45, 0, x_25);
lean::cnstr_set(x_45, 1, x_30);
return x_45;
}
}
else
{
obj* x_48; obj* x_49; obj* x_52; 
lean::dec(x_11);
lean::dec(x_1);
x_48 = l_hashmap__imp_replace__aux___main___rarg(x_0, x_3, x_4, x_18);
x_49 = lean::array_uwrite(x_7, x_17, x_48);
lean::dec(x_48);
lean::dec(x_7);
if (lean::is_scalar(x_9)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_9;
}
lean::cnstr_set(x_52, 0, x_5);
lean::cnstr_set(x_52, 1, x_49);
return x_52;
}
}
}
obj* l_hashmap__imp_insert(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_insert___rarg), 5, 0);
return x_4;
}
}
obj* l_hashmap__imp_erase___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; usize x_12; usize x_14; obj* x_16; uint8 x_20; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::inc(x_6);
x_9 = lean::array_get_size(x_6);
lean::inc(x_3);
x_11 = lean::apply_1(x_1, x_3);
x_12 = lean::unbox_size_t(x_11);
lean::dec(x_11);
x_14 = lean::usize_modn(x_12, x_9);
lean::dec(x_9);
x_16 = lean::array_uread(x_6, x_14);
lean::inc(x_16);
lean::inc(x_3);
lean::inc(x_0);
x_20 = l_hashmap__imp_contains__aux___rarg(x_0, x_3, x_16);
if (x_20 == 0)
{
lean::dec(x_6);
lean::dec(x_16);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_27; obj* x_28; obj* x_31; obj* x_32; obj* x_35; 
lean::dec(x_2);
x_27 = lean::mk_nat_obj(1u);
x_28 = lean::nat_sub(x_4, x_27);
lean::dec(x_27);
lean::dec(x_4);
x_31 = l_hashmap__imp_erase__aux___main___rarg(x_0, x_3, x_16);
x_32 = lean::array_uwrite(x_6, x_14, x_31);
lean::dec(x_31);
lean::dec(x_6);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_28);
lean::cnstr_set(x_35, 1, x_32);
return x_35;
}
}
}
obj* l_hashmap__imp_erase(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_erase___rarg), 4, 0);
return x_4;
}
}
obj* _init_l_d__hashmap() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
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
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_mk__d__hashmap___rarg), 1, 0);
return x_8;
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
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_insert___rarg), 5, 0);
return x_4;
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
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_erase___rarg), 4, 0);
return x_4;
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
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_find___rarg), 4, 0);
return x_4;
}
}
uint8 l_d__hashmap_contains___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = l_hashmap__imp_find___rarg(x_0, x_1, x_2, x_3);
x_5 = l_option_is__some___main___rarg(x_4);
return x_5;
}
}
obj* l_d__hashmap_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_contains___rarg___boxed), 4, 0);
return x_4;
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
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_fold___rarg), 3, 0);
return x_10;
}
}
obj* l_d__hashmap_size___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_d__hashmap_size(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_size___rarg), 1, 0);
return x_8;
}
}
uint8 l_d__hashmap_empty___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = l_d__hashmap_size___rarg(x_0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
if (x_3 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
obj* l_d__hashmap_empty(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_d__hashmap_empty___rarg___boxed), 1, 0);
return x_8;
}
}
obj* l_d__hashmap_empty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_d__hashmap_empty___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* _init_l_hashmap() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
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
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_mk__hashmap___rarg), 1, 0);
return x_8;
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
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap_insert___rarg), 5, 0);
return x_4;
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
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap_erase___rarg), 4, 0);
return x_4;
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
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap_find___rarg), 4, 0);
return x_4;
}
}
uint8 l_hashmap_contains___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = l_hashmap__imp_find___rarg(x_0, x_1, x_2, x_3);
x_5 = l_option_is__some___main___rarg(x_4);
return x_5;
}
}
obj* l_hashmap_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap_contains___rarg___boxed), 4, 0);
return x_4;
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
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap_fold___rarg), 3, 0);
return x_10;
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
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap_size___rarg), 1, 0);
return x_8;
}
}
uint8 l_hashmap_empty___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = l_d__hashmap_size___rarg(x_0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
if (x_3 == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
obj* l_hashmap_empty(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap_empty___rarg___boxed), 1, 0);
return x_8;
}
}
obj* l_hashmap_empty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_hashmap_empty___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
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
 l_bucket__array = _init_l_bucket__array();
 l_mk__hashmap__imp___rarg___closed__1 = _init_l_mk__hashmap__imp___rarg___closed__1();
 l_d__hashmap = _init_l_d__hashmap();
 l_hashmap = _init_l_hashmap();
}
