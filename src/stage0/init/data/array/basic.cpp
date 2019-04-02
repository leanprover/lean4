// Lean compiler output
// Module: init.data.array.basic
// Imports: init.data.nat.basic init.data.fin.basic init.data.uint init.data.repr init.data.tostring init.control.id
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
obj* l_Nat_repeatCore___main___at_Array_mkArray___spec__1(obj*);
obj* l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1___boxed(obj*, obj*);
obj* l_Array_toList___rarg___boxed(obj*);
obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Array_miterateAux___main___at_Array_mforeach___spec__1(obj*, obj*);
obj* l_Array_getOpt(obj*);
obj* l_List_repr___rarg(obj*, obj*);
obj* l_Array_update___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_revFoldl(obj*, obj*);
obj* l_Array_miterate___boxed(obj*, obj*, obj*);
obj* l_Array_mkArray(obj*);
obj* l_Array_isEmpty___boxed(obj*);
obj* l_Array_mfoldl___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1(obj*, obj*);
obj* l_Array_foreach___rarg(obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_HasRepr(obj*);
obj* l_Array_singleton___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_foreach___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterate___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_iterate___boxed(obj*, obj*);
obj* l_Array_size___boxed(obj*, obj*);
obj* l_Array_mforeach___rarg___lambda__1___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_redLength___main___rarg(obj*);
obj* l_Array_foreach___boxed(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfoldl___boxed(obj*, obj*, obj*);
obj* l_List_redLength___main(obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_pop___boxed(obj*, obj*);
obj* l_Array_foreach(obj*);
obj* l_Array_Inhabited___boxed(obj*);
obj* l___private_init_data_array_basic_2__mforeachAux(obj*, obj*);
obj* l_List_redLength(obj*);
obj* l_List_toArrayAux___main___boxed(obj*);
obj* l_List_toArrayAux(obj*);
obj* l_Array_miterateAux___main___at_Array_map___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mforeach___rarg___closed__1;
obj* l_Array_mkArray___boxed(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_toList___boxed(obj*);
obj* l_Array_map___rarg(obj*, obj*);
obj* l_Array_empty(obj*);
obj* l_Array_HasEmptyc(obj*);
obj* l_Array_map_u_2082(obj*);
obj* l_List_redLength___main___rarg___boxed(obj*);
obj* l_Array_toList___rarg(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_get___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_iterate(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__2(obj*);
obj* l_Array_mforeach___boxed(obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main(obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_List_toString___rarg(obj*, obj*);
obj* l_Array_revIterate___boxed(obj*, obj*);
obj* l_Array_revFoldl___rarg___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Array_miterateAux___main(obj*, obj*, obj*);
obj* l_Array_foldl(obj*, obj*);
obj* l_Array_mforeach___rarg___lambda__1(obj*);
obj* l_Array_foldl___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_singleton___rarg(obj*);
obj* l_Array_HasEmptyc___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___boxed(obj*, obj*);
obj* l_Array_map_u_2082___boxed(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l___private_init_data_array_basic_2__mforeachAux___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mforeach___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1(obj*, obj*);
uint8 l_Array_isEmpty___rarg(obj*);
obj* l_Array_push___boxed(obj*, obj*, obj*);
obj* l_Array_map(obj*);
obj* l_Array_map___boxed(obj*);
obj* l_Array_mkArray___rarg(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mmap___rarg(obj*, obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___boxed(obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___boxed(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___boxed(obj*, obj*, obj*);
obj* l_List_toArray(obj*);
obj* l_List_redLength___boxed(obj*);
obj* l_Array_getOpt___rarg(obj*, obj*);
obj* l_List_toArrayAux___boxed(obj*);
obj* l___private_init_data_array_basic_2__mforeachAux___rarg(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1(obj*, obj*);
obj* l_Array_Inhabited(obj*);
obj* l_Array_revIterate___rarg(obj*, obj*, obj*);
obj* l_Array_HasRepr___rarg___closed__1;
obj* l_Array_HasToString(obj*);
obj* l_Array_singleton(obj*);
obj* l_Array_updt___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_toArray___boxed(obj*);
obj* l_Array_isEmpty___rarg___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_mforeach___spec__1___boxed(obj*, obj*);
obj* l_Nat_repeatCore___main___at_Array_mkArray___spec__1___boxed(obj*);
obj* l_Array_iterate___rarg(obj*, obj*, obj*);
obj* l_List_toArray___rarg(obj*);
obj* l_Array_empty___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_mforeach___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_mforeach___rarg(obj*, obj*, obj*);
obj* l_Array_HasToString___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_foreach___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_redLength___main___boxed(obj*);
obj* l_Array_miterateAux(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_map___spec__1(obj*);
obj* l_Array_map_u_2082___rarg(obj*, obj*, obj*);
obj* l_Array_isEmpty(obj*);
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mfoldl(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__2___boxed(obj*);
obj* l_Array_miterate(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_index___boxed(obj*, obj*, obj*);
obj* l_Array_revFoldl___boxed(obj*, obj*);
obj* l_Array_HasRepr___boxed(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux(obj*, obj*);
obj* l_Array_HasRepr___rarg(obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Array_miterateAux___main___at_Array_foreach___spec__1(obj*);
obj* l_Array_revIterate___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Nat_repeatCore___main___at_Array_mkArray___spec__1___rarg(obj*, obj*, obj*);
obj* l_Array_getOpt___boxed(obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Array_HasToString___rarg(obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mmap___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1(obj*, obj*);
obj* l_Array_miterateAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_revIterate(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_getOpt___rarg___boxed(obj*, obj*);
obj* l_Array_mmap(obj*, obj*);
obj* l_Array_toList(obj*);
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__1(obj*);
obj* l_Array_set___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_revFoldl___rarg(obj*, obj*, obj*);
obj* l_Array_mforeach(obj*, obj*);
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___boxed(obj*, obj*);
obj* l_Array_idx___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_foldl___rarg(obj*, obj*, obj*);
obj* l_List_toArrayAux___main(obj*);
obj* l_List_redLength___rarg___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_mforeach___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_foreach___spec__1___boxed(obj*);
obj* l_Array_miterateAux___boxed(obj*, obj*, obj*);
obj* l_Array_mkEmpty___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__1___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_map___spec__1___boxed(obj*);
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_map___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___boxed(obj*, obj*);
obj* l_List_redLength___rarg(obj*);
obj* l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_size___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::array_get_size(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_mkEmpty___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::mk_empty_array(x_1);
lean::dec(x_1);
return x_2;
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
obj* l_Nat_repeatCore___main___at_Array_mkArray___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_9; 
x_5 = lean::mk_nat_obj(1ul);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_1);
lean::inc(x_0);
x_9 = lean::array_push(x_2, x_0);
x_1 = x_6;
x_2 = x_9;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
}
obj* l_Nat_repeatCore___main___at_Array_mkArray___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_repeatCore___main___at_Array_mkArray___spec__1___rarg), 3, 0);
return x_1;
}
}
obj* l_Array_mkArray___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_empty_array(x_0);
x_3 = l_Nat_repeatCore___main___at_Array_mkArray___spec__1___rarg(x_1, x_0, x_2);
return x_3;
}
}
obj* l_Array_mkArray(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mkArray___rarg), 2, 0);
return x_1;
}
}
obj* l_Nat_repeatCore___main___at_Array_mkArray___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Nat_repeatCore___main___at_Array_mkArray___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_mkArray___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_mkArray(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Array_empty___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = lean::mk_empty_array(x_0);
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
obj* l_Array_Inhabited(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
obj* l_Array_Inhabited___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_Inhabited(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Array_isEmpty___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::array_get_size(x_0);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::nat_dec_eq(x_1, x_2);
lean::dec(x_1);
return x_3;
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
obj* l_Array_singleton___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(1ul);
x_2 = l_Array_mkArray___rarg(x_1, x_0);
return x_2;
}
}
obj* l_Array_singleton(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_singleton___rarg), 1, 0);
return x_1;
}
}
obj* l_Array_singleton___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_singleton(x_0);
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
obj* l_Array_getOpt___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_0);
x_3 = lean::nat_dec_lt(x_1, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
x_6 = lean::array_index(x_0, x_1);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
}
obj* l_Array_getOpt(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_getOpt___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Array_getOpt___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_getOpt___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_getOpt___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_getOpt(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_Array_pop___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::array_pop(x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; uint8 x_7; 
lean::inc(x_1);
x_6 = lean::array_sz(x_1);
x_7 = lean::nat_dec_lt(x_3, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_12; obj* x_15; obj* x_18; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::apply_2(x_15, lean::box(0), x_4);
return x_18;
}
else
{
obj* x_19; obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; 
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
x_21 = lean::array_index(x_1, x_3);
lean::inc(x_3);
lean::inc(x_2);
x_24 = lean::apply_3(x_2, x_3, x_21, x_4);
x_25 = lean::mk_nat_obj(1ul);
x_26 = lean::nat_add(x_3, x_25);
lean::dec(x_3);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___rarg), 5, 4);
lean::closure_set(x_28, 0, x_0);
lean::closure_set(x_28, 1, x_1);
lean::closure_set(x_28, 2, x_2);
lean::closure_set(x_28, 3, x_26);
x_29 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_24, x_28);
return x_29;
}
}
}
obj* l_Array_miterateAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___rarg), 5, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterateAux___main(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_miterateAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___rarg), 5, 0);
return x_3;
}
}
obj* l_Array_miterateAux___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterateAux(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterate___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Array_miterateAux___main___rarg(x_0, x_1, x_3, x_4, x_2);
return x_5;
}
}
obj* l_Array_miterate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterate___rarg), 4, 0);
return x_3;
}
}
obj* l_Array_miterate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterate(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; uint8 x_8; 
lean::inc(x_3);
x_7 = lean::array_sz(x_3);
x_8 = lean::nat_dec_lt(x_4, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_13; obj* x_16; obj* x_19; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::apply_2(x_16, lean::box(0), x_5);
return x_19;
}
else
{
obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_20 = lean::cnstr_get(x_0, 1);
lean::inc(x_20);
x_22 = lean::array_index(x_3, x_4);
lean::inc(x_2);
x_24 = lean::apply_2(x_2, x_22, x_5);
x_25 = lean::mk_nat_obj(1ul);
x_26 = lean::nat_add(x_4, x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed), 6, 5);
lean::closure_set(x_27, 0, x_0);
lean::closure_set(x_27, 1, x_1);
lean::closure_set(x_27, 2, x_2);
lean::closure_set(x_27, 3, x_3);
lean::closure_set(x_27, 4, x_26);
x_28 = lean::apply_4(x_20, lean::box(0), lean::box(0), x_24, x_27);
return x_28;
}
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_Array_mfoldl___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; 
x_4 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_6 = l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(x_0, x_1, x_3, x_1, x_4, x_2);
return x_6;
}
}
obj* l_Array_mfoldl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mfoldl___rarg), 4, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Array_mfoldl___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Array_mfoldl___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_miterateAux___main___at_Array_mfoldl___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_mfoldl___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_mfoldl(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
x_12 = lean::array_index(x_2, x_3);
lean::inc(x_3);
lean::inc(x_1);
x_15 = lean::apply_3(x_1, x_3, x_12, x_4);
x_16 = lean::mk_nat_obj(1ul);
x_17 = lean::nat_add(x_3, x_16);
lean::dec(x_3);
x_3 = x_17;
x_4 = x_15;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_iterate___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = lean::mk_nat_obj(0ul);
lean::inc(x_0);
x_5 = l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(x_0, x_2, x_0, x_3, x_1);
lean::dec(x_0);
return x_5;
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
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Array_iterate___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Array_iterate___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_miterateAux___main___at_Array_iterate___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
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
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
x_12 = lean::array_index(x_2, x_3);
lean::inc(x_1);
x_14 = lean::apply_2(x_1, x_12, x_4);
x_15 = lean::mk_nat_obj(1ul);
x_16 = lean::nat_add(x_3, x_15);
lean::dec(x_3);
x_3 = x_16;
x_4 = x_14;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_foldl___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = lean::mk_nat_obj(0ul);
lean::inc(x_0);
x_5 = l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(x_0, x_1, x_0, x_3, x_2);
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
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Array_foldl___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Array_foldl___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_miterateAux___main___at_Array_foldl___spec__1(x_0, x_1);
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
obj* l___private_init_data_array_basic_1__revIterateAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_13; 
x_7 = lean::mk_nat_obj(1ul);
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
obj* l___private_init_data_array_basic_1__revIterateAux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__revIterateAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_1__revIterateAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_3);
return x_5;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_array_basic_1__revIterateAux___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_1__revIterateAux___main___rarg(x_0, x_1, x_2, lean::box(0), x_4);
return x_5;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__revIterateAux___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_1__revIterateAux___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_3);
return x_5;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_array_basic_1__revIterateAux(x_0, x_1);
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
x_4 = l___private_init_data_array_basic_1__revIterateAux___main___rarg(x_0, x_2, x_3, lean::box(0), x_1);
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
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0ul);
x_7 = lean::nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_8 = lean::mk_nat_obj(1ul);
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
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Array_revFoldl___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::array_get_size(x_0);
x_4 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(x_0, x_2, x_0, x_3, lean::box(0), x_1);
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
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_4);
return x_6;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_revFoldl___spec__1(x_0, x_1);
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
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
x_7 = lean::mk_nat_obj(1ul);
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
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Array_toList___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::array_get_size(x_0);
x_3 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg(x_0, x_0, x_2, lean::box(0), x_1);
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
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
return x_5;
}
}
obj* l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_data_array_basic_1__revIterateAux___main___at_Array_toList___spec__1(x_0);
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
obj* l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::array_update(x_1, x_2, x_3);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; uint8 x_8; 
lean::inc(x_3);
x_7 = lean::array_sz(x_3);
x_8 = lean::nat_dec_lt(x_4, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_14; obj* x_17; obj* x_20; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
lean::dec(x_0);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = lean::apply_2(x_17, lean::box(0), x_5);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_26; obj* x_27; obj* x_29; obj* x_32; obj* x_33; obj* x_35; obj* x_36; 
x_21 = lean::mk_nat_obj(1ul);
x_22 = lean::nat_add(x_4, x_21);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_0);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1___rarg), 6, 5);
lean::closure_set(x_26, 0, x_0);
lean::closure_set(x_26, 1, x_1);
lean::closure_set(x_26, 2, x_2);
lean::closure_set(x_26, 3, x_3);
lean::closure_set(x_26, 4, x_22);
x_27 = lean::cnstr_get(x_0, 1);
lean::inc(x_27);
x_29 = lean::array_index(x_3, x_4);
lean::dec(x_3);
lean::inc(x_4);
x_32 = lean::apply_2(x_2, x_4, x_29);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_33, 0, x_0);
lean::closure_set(x_33, 1, x_5);
lean::closure_set(x_33, 2, x_4);
lean::inc(x_27);
x_35 = lean::apply_4(x_27, lean::box(0), lean::box(0), x_32, x_33);
x_36 = lean::apply_4(x_27, lean::box(0), lean::box(0), x_35, x_26);
return x_36;
}
}
}
obj* l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1___rarg), 6, 0);
return x_2;
}
}
obj* l___private_init_data_array_basic_2__mforeachAux___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
lean::inc(x_1);
x_6 = l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1___rarg(x_0, x_1, x_2, x_1, x_3, x_1);
return x_6;
}
}
obj* l___private_init_data_array_basic_2__mforeachAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_2__mforeachAux___rarg), 3, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1___rarg___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_miterateAux___main___at___private_init_data_array_basic_2__mforeachAux___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_data_array_basic_2__mforeachAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_array_basic_2__mforeachAux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Array_mforeach___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::array_update(x_1, x_2, x_3);
x_8 = lean::apply_2(x_4, lean::box(0), x_7);
return x_8;
}
}
obj* l_Array_miterateAux___main___at_Array_mforeach___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; uint8 x_9; 
lean::inc(x_4);
x_8 = lean::array_sz(x_4);
x_9 = lean::nat_dec_lt(x_5, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_16; obj* x_19; obj* x_22; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::apply_2(x_19, lean::box(0), x_6);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_29; obj* x_30; obj* x_33; obj* x_36; obj* x_37; obj* x_39; obj* x_40; 
x_23 = lean::mk_nat_obj(1ul);
x_24 = lean::nat_add(x_5, x_23);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_0);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mforeach___spec__1___rarg), 7, 6);
lean::closure_set(x_29, 0, x_0);
lean::closure_set(x_29, 1, x_1);
lean::closure_set(x_29, 2, x_2);
lean::closure_set(x_29, 3, x_3);
lean::closure_set(x_29, 4, x_4);
lean::closure_set(x_29, 5, x_24);
x_30 = lean::cnstr_get(x_0, 1);
lean::inc(x_30);
lean::dec(x_0);
x_33 = lean::array_index(x_4, x_5);
lean::dec(x_4);
lean::inc(x_5);
x_36 = lean::apply_2(x_2, x_5, x_33);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mforeach___spec__1___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_37, 0, x_3);
lean::closure_set(x_37, 1, x_6);
lean::closure_set(x_37, 2, x_5);
lean::inc(x_30);
x_39 = lean::apply_4(x_30, lean::box(0), lean::box(0), x_36, x_37);
x_40 = lean::apply_4(x_30, lean::box(0), lean::box(0), x_39, x_29);
return x_40;
}
}
}
obj* l_Array_miterateAux___main___at_Array_mforeach___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mforeach___spec__1___rarg), 7, 0);
return x_2;
}
}
obj* l_Array_mforeach___rarg___lambda__1(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_Array_mforeach___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mforeach___rarg___lambda__1___boxed), 1, 0);
return x_0;
}
}
obj* l_Array_mforeach___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
lean::dec(x_5);
x_10 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
lean::inc(x_1);
x_13 = l_Array_miterateAux___main___at_Array_mforeach___spec__1___rarg(x_0, x_1, x_2, x_3, x_1, x_10, x_1);
x_14 = l_Array_mforeach___rarg___closed__1;
x_15 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_14, x_13);
return x_15;
}
}
obj* l_Array_mforeach(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mforeach___rarg), 3, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Array_mforeach___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Array_mforeach___spec__1___rarg___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Array_mforeach___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_miterateAux___main___at_Array_mforeach___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_mforeach___rarg___lambda__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_mforeach___rarg___lambda__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_mforeach___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_mforeach(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; uint8 x_9; 
lean::inc(x_4);
x_8 = lean::array_sz(x_4);
x_9 = lean::nat_dec_lt(x_5, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_16; obj* x_19; obj* x_22; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::apply_2(x_19, lean::box(0), x_6);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_29; obj* x_30; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_39; 
x_23 = lean::mk_nat_obj(1ul);
x_24 = lean::nat_add(x_5, x_23);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_0);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg), 7, 6);
lean::closure_set(x_29, 0, x_0);
lean::closure_set(x_29, 1, x_1);
lean::closure_set(x_29, 2, x_2);
lean::closure_set(x_29, 3, x_3);
lean::closure_set(x_29, 4, x_4);
lean::closure_set(x_29, 5, x_24);
x_30 = lean::cnstr_get(x_0, 1);
lean::inc(x_30);
lean::dec(x_0);
x_33 = lean::array_index(x_4, x_5);
lean::dec(x_4);
x_35 = lean::apply_1(x_1, x_33);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mforeach___spec__1___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_36, 0, x_3);
lean::closure_set(x_36, 1, x_6);
lean::closure_set(x_36, 2, x_5);
lean::inc(x_30);
x_38 = lean::apply_4(x_30, lean::box(0), lean::box(0), x_35, x_36);
x_39 = lean::apply_4(x_30, lean::box(0), lean::box(0), x_38, x_29);
return x_39;
}
}
}
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg), 7, 0);
return x_2;
}
}
obj* l_Array_mmap___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
lean::dec(x_5);
x_10 = lean::mk_nat_obj(0ul);
lean::inc(x_2);
lean::inc(x_2);
x_13 = l_Array_miterateAux___main___at_Array_mmap___spec__1___rarg(x_0, x_1, x_2, x_3, x_2, x_10, x_2);
x_14 = l_Array_mforeach___rarg___closed__1;
x_15 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_14, x_13);
return x_15;
}
}
obj* l_Array_mmap(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_mmap___rarg), 3, 0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Array_mmap___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_miterateAux___main___at_Array_mmap___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_mmap___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_mmap(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Array_foreach___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_12 = lean::mk_nat_obj(1ul);
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
obj* l_Array_miterateAux___main___at_Array_foreach___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_foreach___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Array_foreach___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::mk_nat_obj(0ul);
lean::inc(x_0);
lean::inc(x_0);
x_5 = l_Array_miterateAux___main___at_Array_foreach___spec__1___rarg(x_0, x_1, x_0, x_2, x_0);
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
obj* l_Array_miterateAux___main___at_Array_foreach___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Array_foreach___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Array_foreach___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_miterateAux___main___at_Array_foreach___spec__1(x_0);
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
obj* l_Array_miterateAux___main___at_Array_map___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_12 = lean::mk_nat_obj(1ul);
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
obj* l_Array_miterateAux___main___at_Array_map___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_map___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Array_map___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
lean::inc(x_1);
x_5 = l_Array_miterateAux___main___at_Array_map___spec__1___rarg(x_0, x_1, x_1, x_2, x_1);
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
obj* l_Array_miterateAux___main___at_Array_map___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Array_map___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Array_map___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_miterateAux___main___at_Array_map___spec__1(x_0);
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
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
x_13 = lean::mk_nat_obj(1ul);
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
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_map_u_2082___spec__1___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
x_13 = lean::mk_nat_obj(1ul);
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
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_Array_map_u_2082___spec__2___rarg___boxed), 6, 0);
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
x_8 = lean::mk_nat_obj(0ul);
lean::inc(x_2);
lean::inc(x_2);
x_11 = l_Array_miterateAux___main___at_Array_map_u_2082___spec__1___rarg(x_0, x_1, x_2, x_2, x_8, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_11;
}
else
{
obj* x_14; obj* x_17; 
x_14 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
lean::inc(x_1);
x_17 = l_Array_miterateAux___main___at_Array_map_u_2082___spec__2___rarg(x_0, x_1, x_2, x_1, x_14, x_1);
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
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Array_map_u_2082___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_miterateAux___main___at_Array_map_u_2082___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Array_map_u_2082___spec__2___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Array_map_u_2082___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_miterateAux___main___at_Array_map_u_2082___spec__2(x_0);
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
obj* l_List_redLength___main___rarg(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::mk_nat_obj(0ul);
return x_1;
}
else
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 1);
x_3 = l_List_redLength___main___rarg(x_2);
x_4 = lean::mk_nat_obj(1ul);
x_5 = lean::nat_add(x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
}
obj* l_List_redLength___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_redLength___main___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_List_redLength___main___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_redLength___main___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_redLength___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_redLength___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_redLength___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_redLength___main___rarg(x_0);
return x_1;
}
}
obj* l_List_redLength(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_redLength___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_List_redLength___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_redLength___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_redLength___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_List_redLength(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_toArray___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_1 = l_List_redLength___main___rarg(x_0);
x_2 = lean::mk_empty_array(x_1);
lean::dec(x_1);
x_4 = l_List_toArrayAux___main___rarg(x_0, x_2);
return x_4;
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
obj* initialize_init_control_id(obj*);
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
if (io_result_is_error(w)) return w;
w = initialize_init_control_id(w);
 l_Array_empty___closed__1 = _init_l_Array_empty___closed__1();
lean::mark_persistent(l_Array_empty___closed__1);
 l_Array_HasRepr___rarg___closed__1 = _init_l_Array_HasRepr___rarg___closed__1();
lean::mark_persistent(l_Array_HasRepr___rarg___closed__1);
 l_Array_mforeach___rarg___closed__1 = _init_l_Array_mforeach___rarg___closed__1();
lean::mark_persistent(l_Array_mforeach___rarg___closed__1);
return w;
}
