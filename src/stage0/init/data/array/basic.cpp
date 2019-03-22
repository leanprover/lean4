// Lean compiler output
// Module: init.data.array.basic
// Imports: init.data.nat.basic init.data.fin.basic init.data.uint init.data.repr init.data.tostring
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
obj* l_List_toArrayAux___rarg(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_toList___rarg___boxed(obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__1___boxed(obj*);
obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1(obj*);
obj* l_List_repr___rarg(obj*, obj*);
obj* l_Array_update___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_revFoldl(obj*, obj*);
obj* l_Array_isEmpty___boxed(obj*);
obj* l___private_init_data_array_basic_2__revIterateAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_foreach___rarg(obj*, obj*);
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_2__revIterateAux(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foreach___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_HasRepr(obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Array_iterate___boxed(obj*, obj*);
obj* l_Array_size___boxed(obj*, obj*);
obj* l___private_init_data_array_basic_2__revIterateAux___main___boxed(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at___private_init_data_array_basic_3__foreachAux___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_2__revIterateAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l_Array_foreach___boxed(obj*);
obj* l___private_init_data_array_basic_2__revIterateAux___main(obj*, obj*);
obj* l_Array_pop___boxed(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at___private_init_data_array_basic_3__foreachAux___spec__1(obj*);
obj* l_Array_foreach(obj*);
obj* l_List_toArrayAux___main___boxed(obj*);
obj* l_List_toArrayAux(obj*);
obj* l_Array_toList___boxed(obj*);
obj* l_Array_map___rarg(obj*, obj*);
obj* l___private_init_data_array_basic_3__foreachAux(obj*);
obj* l_Array_empty(obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__2___boxed(obj*);
obj* l_Array_HasEmptyc(obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map___spec__1___boxed(obj*);
obj* l_Array_map_u_2082(obj*);
obj* l_Array_toList___rarg(obj*);
obj* l_Array_get___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_iterate(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_2__revIterateAux___boxed(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foldl___spec__1(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_toString___rarg(obj*, obj*);
obj* l_Array_revIterate___boxed(obj*, obj*);
obj* l_Array_revFoldl___rarg___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l___private_init_data_array_basic_1__iterateAux(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_foldl(obj*, obj*);
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_foldl___boxed(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foreach___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_HasEmptyc___boxed(obj*);
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_map_u_2082___boxed(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__1(obj*);
uint8 l_Array_isEmpty___rarg(obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map___spec__1(obj*);
obj* l_Array_push___boxed(obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___boxed(obj*, obj*);
obj* l_Array_map(obj*);
obj* l_Array_map___boxed(obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foreach___spec__1(obj*);
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1(obj*, obj*);
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__2(obj*);
obj* l_List_toArray(obj*);
obj* l_mkArray___boxed(obj*, obj*, obj*);
obj* l_List_toArrayAux___boxed(obj*);
obj* l_Array_revIterate___rarg(obj*, obj*, obj*);
obj* l_Array_HasRepr___rarg___closed__1;
obj* l_Array_HasToString(obj*);
obj* l_Array_updt___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_toArray___boxed(obj*);
obj* l_Array_isEmpty___rarg___boxed(obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___boxed(obj*, obj*);
obj* l_Array_iterate___rarg(obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foreach___spec__1___boxed(obj*);
obj* l_List_toArray___rarg(obj*);
obj* l_Array_empty___boxed(obj*);
obj* l_Array_HasToString___boxed(obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at___private_init_data_array_basic_3__foreachAux___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at___private_init_data_array_basic_3__foreachAux___spec__1___boxed(obj*);
obj* l_Array_map_u_2082___rarg(obj*, obj*, obj*);
obj* l_Array_isEmpty(obj*);
obj* l_Array_index___boxed(obj*, obj*, obj*);
obj* l_Array_revFoldl___boxed(obj*, obj*);
obj* l_Array_HasRepr___boxed(obj*);
obj* l_Array_HasRepr___rarg(obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Array_revIterate___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_data_array_basic_3__foreachAux___rarg(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_HasToString___rarg(obj*);
obj* l___private_init_data_array_basic_2__revIterateAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___boxed(obj*, obj*);
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___boxed(obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foldl___spec__1___boxed(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_revIterate(obj*, obj*);
obj* l_Array_toList(obj*);
obj* l_Array_set___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_revFoldl___rarg(obj*, obj*, obj*);
obj* l_Array_idx___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_foldl___rarg(obj*, obj*, obj*);
obj* l_List_toArrayAux___main(obj*);
obj* l___private_init_data_array_basic_2__revIterateAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foldl___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mkEmpty___boxed(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foldl___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_3__foreachAux___boxed(obj*);
obj* l_Array_size___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::array_get_size(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_mkArray___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::mk_array(x_1, x_2);
return x_3;
}
}
obj* l_Array_mkEmpty___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::mk_empty_array();
return x_2;
}
}
obj* _init_l_Array_empty___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::mk_empty_array();
return x_1;
}
}
obj* l_Array_empty(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
obj* l_Array_empty___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_empty(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_HasEmptyc(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
obj* l_Array_HasEmptyc___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_HasEmptyc(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Array_isEmpty___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::array_get_size(x_0);
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
obj* l_Array_isEmpty(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_isEmpty___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Array_isEmpty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Array_isEmpty___rarg(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Array_isEmpty___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_isEmpty(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_index___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::array_index(x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_idx___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; obj* x_5; 
x_4 = lean::unbox_size_t(x_2);
x_5 = lean::array_idx(x_1, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_get___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::array_get(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_update___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::array_update(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_updt___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; obj* x_6; 
x_5 = lean::unbox_size_t(x_2);
x_6 = lean::array_updt(x_1, x_5, x_3);
lean::dec(x_1);
lean::dec(x_3);
return x_6;
}
}
obj* l_Array_set___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::array_set(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_push___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::array_push(x_1, x_2);
return x_3;
}
}
obj* l_Array_pop___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::array_pop(x_1);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_11; obj* x_12; obj* x_13; obj* x_15; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_2, x_11);
x_13 = lean::array_index(x_0, x_2);
lean::inc(x_1);
x_15 = lean::apply_3(x_1, x_2, x_13, x_3);
x_2 = x_12;
x_3 = x_15;
goto _start;
}
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__iterateAux___main___rarg), 4, 0);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_array_basic_1__iterateAux___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_data_array_basic_1__iterateAux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_data_array_basic_1__iterateAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__iterateAux___rarg), 4, 0);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_array_basic_1__iterateAux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_iterate___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = l___private_init_data_array_basic_1__iterateAux___main___rarg(x_0, x_2, x_3, x_1);
return x_4;
}
}
obj* l_Array_iterate(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_iterate___rarg), 3, 0);
return x_2;
}
}
obj* l_Array_iterate___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_iterate(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foldl___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; uint8 x_7; 
lean::inc(x_2);
x_6 = lean::array_sz(x_2);
x_7 = lean::nat_dec_lt(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_17; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_3, x_12);
x_14 = lean::array_index(x_2, x_3);
lean::dec(x_3);
lean::inc(x_1);
x_17 = lean::apply_2(x_1, x_14, x_4);
x_3 = x_13;
x_4 = x_17;
goto _start;
}
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foldl___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__iterateAux___main___at_Array_foldl___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_foldl___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = lean::mk_nat_obj(0u);
lean::inc(x_0);
x_5 = l___private_init_data_array_basic_1__iterateAux___main___at_Array_foldl___spec__1___rarg(x_0, x_2, x_0, x_3, x_1);
lean::dec(x_0);
return x_5;
}
}
obj* l_Array_foldl(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_foldl___rarg), 3, 0);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foldl___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_1__iterateAux___main___at_Array_foldl___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foldl___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_array_basic_1__iterateAux___main___at_Array_foldl___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_foldl___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_foldl(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_data_array_basic_2__revIterateAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_13; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_2);
x_10 = lean::array_index(x_0, x_8);
lean::inc(x_8);
lean::inc(x_1);
x_13 = lean::apply_3(x_1, x_8, x_10, x_4);
x_2 = x_8;
x_3 = lean::box(0);
x_4 = x_13;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
}
obj* l___private_init_data_array_basic_2__revIterateAux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_2__revIterateAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l___private_init_data_array_basic_2__revIterateAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_2__revIterateAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_3);
return x_5;
}
}
obj* l___private_init_data_array_basic_2__revIterateAux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_array_basic_2__revIterateAux___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_data_array_basic_2__revIterateAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_2__revIterateAux___main___rarg(x_0, x_1, x_2, lean::box(0), x_4);
return x_5;
}
}
obj* l___private_init_data_array_basic_2__revIterateAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_2__revIterateAux___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l___private_init_data_array_basic_2__revIterateAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_2__revIterateAux___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_3);
return x_5;
}
}
obj* l___private_init_data_array_basic_2__revIterateAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_array_basic_2__revIterateAux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_revIterate___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::array_get_size(x_0);
x_4 = l___private_init_data_array_basic_2__revIterateAux___main___rarg(x_0, x_2, x_3, lean::box(0), x_1);
return x_4;
}
}
obj* l_Array_revIterate(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_revIterate___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Array_revIterate___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_revIterate___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_revIterate___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_revIterate(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_3, x_8);
lean::dec(x_3);
x_11 = lean::array_index(x_2, x_9);
lean::inc(x_1);
x_13 = lean::apply_2(x_1, x_11, x_5);
x_3 = x_9;
x_4 = lean::box(0);
x_5 = x_13;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_3);
return x_5;
}
}
}
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Array_revFoldl___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::array_get_size(x_0);
x_4 = l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(x_0, x_2, x_0, x_3, lean::box(0), x_1);
return x_4;
}
}
obj* l_Array_revFoldl(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_revFoldl___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_4);
return x_6;
}
}
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_array_basic_2__revIterateAux___main___at_Array_revFoldl___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_revFoldl___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_revFoldl___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_revFoldl___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_revFoldl(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_2);
x_10 = lean::array_index(x_1, x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_4);
x_2 = x_8;
x_3 = lean::box(0);
x_4 = x_11;
goto _start;
}
else
{
lean::dec(x_2);
return x_4;
}
}
}
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Array_toList___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::array_get_size(x_0);
x_3 = l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___rarg(x_0, x_0, x_2, lean::box(0), x_1);
return x_3;
}
}
obj* l_Array_toList(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_toList___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
return x_5;
}
}
obj* l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_data_array_basic_2__revIterateAux___main___at_Array_toList___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_toList___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_toList___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_toList___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_toList(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Array_HasRepr___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_toList___rarg___boxed), 1, 0);
return x_0;
}
}
obj* l_Array_HasRepr___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_repr___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = l_Array_HasRepr___rarg___closed__1;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Array_HasRepr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_HasRepr___rarg), 1, 0);
return x_1;
}
}
obj* l_Array_HasRepr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_HasRepr(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_HasToString___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toString___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = l_Array_HasRepr___rarg___closed__1;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Array_HasToString(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_HasToString___rarg), 1, 0);
return x_1;
}
}
obj* l_Array_HasToString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_HasToString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at___private_init_data_array_basic_3__foreachAux___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; uint8 x_7; 
lean::inc(x_2);
x_6 = lean::array_sz(x_2);
x_7 = lean::nat_dec_lt(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_3, x_12);
x_14 = lean::array_index(x_2, x_3);
lean::inc(x_3);
lean::inc(x_1);
x_17 = lean::apply_2(x_1, x_3, x_14);
x_18 = lean::array_update(x_4, x_3, x_17);
lean::dec(x_3);
x_3 = x_13;
x_4 = x_18;
goto _start;
}
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at___private_init_data_array_basic_3__foreachAux___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__iterateAux___main___at___private_init_data_array_basic_3__foreachAux___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l___private_init_data_array_basic_3__foreachAux___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::mk_nat_obj(0u);
lean::inc(x_0);
lean::inc(x_0);
x_5 = l___private_init_data_array_basic_1__iterateAux___main___at___private_init_data_array_basic_3__foreachAux___spec__1___rarg(x_0, x_1, x_0, x_2, x_0);
lean::dec(x_0);
return x_5;
}
}
obj* l___private_init_data_array_basic_3__foreachAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_3__foreachAux___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at___private_init_data_array_basic_3__foreachAux___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_1__iterateAux___main___at___private_init_data_array_basic_3__foreachAux___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at___private_init_data_array_basic_3__foreachAux___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_data_array_basic_1__iterateAux___main___at___private_init_data_array_basic_3__foreachAux___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_data_array_basic_3__foreachAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_data_array_basic_3__foreachAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foreach___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; uint8 x_7; 
lean::inc(x_2);
x_6 = lean::array_sz(x_2);
x_7 = lean::nat_dec_lt(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_3, x_12);
x_14 = lean::array_index(x_2, x_3);
lean::inc(x_3);
lean::inc(x_1);
x_17 = lean::apply_2(x_1, x_3, x_14);
x_18 = lean::array_update(x_4, x_3, x_17);
lean::dec(x_3);
x_3 = x_13;
x_4 = x_18;
goto _start;
}
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foreach___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__iterateAux___main___at_Array_foreach___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Array_foreach___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::mk_nat_obj(0u);
lean::inc(x_0);
lean::inc(x_0);
x_5 = l___private_init_data_array_basic_1__iterateAux___main___at_Array_foreach___spec__1___rarg(x_0, x_1, x_0, x_2, x_0);
lean::dec(x_0);
return x_5;
}
}
obj* l_Array_foreach(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_foreach___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foreach___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_1__iterateAux___main___at_Array_foreach___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_foreach___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_data_array_basic_1__iterateAux___main___at_Array_foreach___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_foreach___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_foreach(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; uint8 x_7; 
lean::inc(x_2);
x_6 = lean::array_sz(x_2);
x_7 = lean::nat_dec_lt(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_3, x_12);
x_14 = lean::array_index(x_2, x_3);
lean::inc(x_0);
x_16 = lean::apply_1(x_0, x_14);
x_17 = lean::array_update(x_4, x_3, x_16);
lean::dec(x_3);
x_3 = x_13;
x_4 = x_17;
goto _start;
}
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__iterateAux___main___at_Array_map___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Array_map___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::mk_nat_obj(0u);
lean::inc(x_1);
lean::inc(x_1);
x_5 = l___private_init_data_array_basic_1__iterateAux___main___at_Array_map___spec__1___rarg(x_0, x_1, x_1, x_2, x_1);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_map(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_map___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_1__iterateAux___main___at_Array_map___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_data_array_basic_1__iterateAux___main___at_Array_map___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_map___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_map(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; uint8 x_8; 
lean::inc(x_3);
x_7 = lean::array_sz(x_3);
x_8 = lean::nat_dec_lt(x_4, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
return x_5;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_4, x_13);
x_15 = lean::array_index(x_3, x_4);
x_16 = lean::array_index(x_1, x_4);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_16, x_15);
x_19 = lean::array_update(x_5, x_4, x_18);
lean::dec(x_4);
x_4 = x_14;
x_5 = x_19;
goto _start;
}
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__1___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; uint8 x_8; 
lean::inc(x_3);
x_7 = lean::array_sz(x_3);
x_8 = lean::nat_dec_lt(x_4, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
return x_5;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_4, x_13);
x_15 = lean::array_index(x_3, x_4);
x_16 = lean::array_index(x_2, x_4);
lean::inc(x_0);
x_18 = lean::apply_2(x_0, x_16, x_15);
x_19 = lean::array_update(x_5, x_4, x_18);
lean::dec(x_4);
x_4 = x_14;
x_5 = x_19;
goto _start;
}
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__2___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Array_map_u_2082___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_le(x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
if (x_5 == 0)
{
obj* x_8; obj* x_11; 
x_8 = lean::mk_nat_obj(0u);
lean::inc(x_2);
lean::inc(x_2);
x_11 = l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__1___rarg(x_0, x_1, x_2, x_2, x_8, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_11;
}
else
{
obj* x_14; obj* x_17; 
x_14 = lean::mk_nat_obj(0u);
lean::inc(x_1);
lean::inc(x_1);
x_17 = l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__2___rarg(x_0, x_1, x_2, x_1, x_14, x_1);
lean::dec(x_2);
lean::dec(x_1);
return x_17;
}
}
}
obj* l_Array_map_u_2082(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_map_u_2082___rarg), 3, 0);
return x_1;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__2___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_data_array_basic_1__iterateAux___main___at_Array_map_u_2082___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_map_u_2082___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_map_u_2082(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_toArrayAux___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::array_push(x_1, x_2);
x_0 = x_4;
x_1 = x_7;
goto _start;
}
}
}
obj* l_List_toArrayAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toArrayAux___main___rarg), 2, 0);
return x_1;
}
}
obj* l_List_toArrayAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_toArrayAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_toArrayAux___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_toArrayAux___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_List_toArrayAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toArrayAux___rarg), 2, 0);
return x_1;
}
}
obj* l_List_toArrayAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_toArrayAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_toArray___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = l_List_toArrayAux___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_List_toArray(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_toArray___rarg), 1, 0);
return x_1;
}
}
obj* l_List_toArray___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_toArray(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* initialize_init_data_nat_basic(obj*);
obj* initialize_init_data_fin_basic(obj*);
obj* initialize_init_data_uint(obj*);
obj* initialize_init_data_repr(obj*);
obj* initialize_init_data_tostring(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_array_basic(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_nat_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_fin_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_repr(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_tostring(w);
 l_Array_empty___closed__1 = _init_l_Array_empty___closed__1();
lean::mark_persistent(l_Array_empty___closed__1);
 l_Array_HasRepr___rarg___closed__1 = _init_l_Array_HasRepr___rarg___closed__1();
lean::mark_persistent(l_Array_HasRepr___rarg___closed__1);
return w;
}
