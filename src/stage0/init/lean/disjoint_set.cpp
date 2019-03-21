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
obj* l___private_init_lean_disjoint__set_1__findAux(obj*);
obj* l_Lean_DisjointSet_merge___main(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l___private_init_lean_disjoint__set_1__findAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_mkDisjointSet(obj*, obj*, obj*);
obj* l_HashmapImp_find___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_DisjointSet_merge___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_DisjointSet_find___main(obj*);
obj* l_mkHashmapImp___rarg(obj*);
obj* l_Lean_DisjointSet_find(obj*);
obj* l_HashmapImp_insert___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_DisjointSet_find___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_DisjointSet_merge___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_DisjointSet_rank(obj*);
obj* l_Lean_DisjointSet_rank___main___rarg(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_DHashmap_size___rarg(obj*);
obj* l_Lean_DisjointSet_find___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_DisjointSet_merge___main___boxed(obj*);
obj* l_Lean_DisjointSet_rank___main___boxed(obj*);
obj* l_Lean_DisjointSet_rank___boxed(obj*);
obj* l_Lean_DisjointSet_rank___main(obj*);
obj* l_Lean_DisjointSet_rank___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_DisjointSet_merge___boxed(obj*);
obj* l_Lean_DisjointSet_find___main___boxed(obj*);
obj* l_Lean_mkDisjointSet___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_disjoint__set_1__findAux___boxed(obj*);
obj* l___private_init_lean_disjoint__set_1__findAux___main___boxed(obj*);
obj* l___private_init_lean_disjoint__set_1__findAux___main(obj*);
obj* l_Lean_DisjointSet_merge(obj*);
obj* l___private_init_lean_disjoint__set_1__findAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_DisjointSet_find___boxed(obj*);
obj* l_Lean_mkDisjointSet(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(8u);
x_4 = l_mkHashmapImp___rarg(x_3);
return x_4;
}
}
obj* l_Lean_mkDisjointSet___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_mkDisjointSet(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_lean_disjoint__set_1__findAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_11 = l_HashmapImp_find___rarg(x_0, x_1, x_4, x_3);
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
obj* l___private_init_lean_disjoint__set_1__findAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_disjoint__set_1__findAux___main___rarg), 5, 0);
return x_1;
}
}
obj* l___private_init_lean_disjoint__set_1__findAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_disjoint__set_1__findAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_disjoint__set_1__findAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_disjoint__set_1__findAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_lean_disjoint__set_1__findAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_disjoint__set_1__findAux___rarg), 5, 0);
return x_1;
}
}
obj* l___private_init_lean_disjoint__set_1__findAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_disjoint__set_1__findAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_DisjointSet_find___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_DHashmap_size___rarg(x_2);
x_5 = l___private_init_lean_disjoint__set_1__findAux___main___rarg(x_0, x_1, x_4, x_3, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_DisjointSet_find___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_DisjointSet_find___main___rarg), 4, 0);
return x_1;
}
}
obj* l_Lean_DisjointSet_find___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_DisjointSet_find___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_DisjointSet_find___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_DisjointSet_find___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_DisjointSet_find(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_DisjointSet_find___rarg), 4, 0);
return x_1;
}
}
obj* l_Lean_DisjointSet_find___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_DisjointSet_find(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_DisjointSet_rank___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_DHashmap_size___rarg(x_2);
x_5 = l___private_init_lean_disjoint__set_1__findAux___main___rarg(x_0, x_1, x_4, x_3, x_2);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_DisjointSet_rank___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_DisjointSet_rank___main___rarg), 4, 0);
return x_1;
}
}
obj* l_Lean_DisjointSet_rank___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_DisjointSet_rank___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_DisjointSet_rank___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_DisjointSet_rank___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_DisjointSet_rank(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_DisjointSet_rank___rarg), 4, 0);
return x_1;
}
}
obj* l_Lean_DisjointSet_rank___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_DisjointSet_rank(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_DisjointSet_merge___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_11; obj* x_16; obj* x_17; obj* x_19; obj* x_22; uint8 x_23; 
x_5 = l_DHashmap_size___rarg(x_2);
lean::inc(x_2);
lean::inc(x_3);
lean::inc(x_5);
lean::inc(x_1);
lean::inc(x_0);
x_11 = l___private_init_lean_disjoint__set_1__findAux___main___rarg(x_0, x_1, x_5, x_3, x_2);
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_1);
lean::inc(x_0);
x_16 = l___private_init_lean_disjoint__set_1__findAux___main___rarg(x_0, x_1, x_5, x_4, x_2);
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
x_36 = l_HashmapImp_insert___rarg(x_0, x_1, x_2, x_4, x_35);
return x_36;
}
else
{
obj* x_37; obj* x_39; obj* x_42; obj* x_43; obj* x_44; obj* x_47; obj* x_48; 
x_37 = lean::mk_nat_obj(0u);
lean::inc(x_4);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_4);
lean::cnstr_set(x_39, 1, x_37);
lean::inc(x_1);
lean::inc(x_0);
x_42 = l_HashmapImp_insert___rarg(x_0, x_1, x_2, x_3, x_39);
x_43 = lean::mk_nat_obj(1u);
x_44 = lean::nat_add(x_27, x_43);
lean::dec(x_27);
lean::inc(x_4);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_4);
lean::cnstr_set(x_47, 1, x_44);
x_48 = l_HashmapImp_insert___rarg(x_0, x_1, x_42, x_4, x_47);
return x_48;
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_24);
lean::dec(x_27);
x_51 = lean::mk_nat_obj(0u);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_4);
lean::cnstr_set(x_52, 1, x_51);
x_53 = l_HashmapImp_insert___rarg(x_0, x_1, x_2, x_3, x_52);
return x_53;
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
obj* l_Lean_DisjointSet_merge___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_DisjointSet_merge___main___rarg), 5, 0);
return x_1;
}
}
obj* l_Lean_DisjointSet_merge___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_DisjointSet_merge___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_DisjointSet_merge___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_DisjointSet_merge___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Lean_DisjointSet_merge(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_DisjointSet_merge___rarg), 5, 0);
return x_1;
}
}
obj* l_Lean_DisjointSet_merge___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_DisjointSet_merge(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* initialize_init_data_hashmap_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_disjoint__set(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_hashmap_basic(w);
return w;
}
