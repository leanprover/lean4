// Lean compiler output
// Module: init.data.array.basic
// Imports: init.data.nat.basic init.data.fin.basic init.data.usize init.data.repr init.function
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
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
obj* l_array_write___rarg(obj*, obj*, obj*);
obj* l_array_rev__iterate(obj*, obj*);
obj* l_array_push___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_array_rev__foldl(obj*, obj*);
obj* l_array_uread___rarg___boxed(obj*, obj*, obj*);
obj* l_array_rev__iterate___rarg(obj*, obj*, obj*);
obj* l_array_read___rarg(obj*, obj*);
obj* l___private_init_data_array_basic_2__rev__iterate__aux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_array_write(obj*);
obj* l_array_uread(obj*);
obj* l_array_uread_x_27(obj*);
obj* l_array_uwrite_x_27(obj*);
obj* l_array_write___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_array_rev__foldl___rarg(obj*, obj*, obj*);
obj* l_array_map_u_2082___rarg(obj*, obj*, obj*);
obj* l_array_uwrite___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_array_uread_x_27___rarg(obj*, obj*, usize);
obj* l_array_empty___rarg___boxed(obj*);
obj* l_array_nil___lambda__1(obj*);
obj* l_array_to__list___rarg___lambda__1(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterate__aux(obj*, obj*);
obj* l_array_write_x_27(obj*);
obj* l_array_map(obj*);
obj* l_array_has__repr___rarg___closed__1;
obj* l_array_map_u_2082___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_array_nil(obj*);
obj* l_array_has__repr(obj*);
obj* l___private_init_data_array_basic_1__iterate__aux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_mk__array___rarg(obj*, obj*);
obj* l___private_init_data_array_basic_3__foreach__aux___rarg(obj*, obj*);
obj* l_array_read(obj*);
obj* l___private_init_data_array_basic_2__rev__iterate__aux(obj*, obj*);
obj* l_nat_pred___main(obj*);
obj* l_array_empty(obj*);
obj* l_array_uread___rarg(obj*, usize, obj*);
obj* l_array_uwrite(obj*);
obj* l_array_read_x_27(obj*);
obj* l_array_foldl(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterate__aux___main(obj*, obj*);
uint8 l_array_empty___rarg(obj*);
obj* l___private_init_data_array_basic_3__foreach__aux(obj*);
obj* l_array_pop___rarg(obj*);
obj* l_list_repr___rarg(obj*, obj*);
obj* l_array_map_u_2082(obj*);
obj* l_list_to__array__aux(obj*);
obj* l_array_uread_x_27___rarg___boxed(obj*, obj*, obj*);
obj* l_array_foreach(obj*);
obj* l_array_foldl___rarg(obj*, obj*, obj*);
obj* l_mk__array___rarg___lambda__1(obj*, obj*);
obj* l_array_to__list___rarg(obj*);
obj* l_list_to__array__aux___rarg(obj*, obj*);
obj* l_list_to__array__aux___main(obj*);
obj* l_array_push(obj*);
obj* l_list_to__array__aux___main___rarg(obj*, obj*);
obj* l_array_uwrite_x_27___rarg(obj*, usize, obj*);
obj* l_array_push___rarg(obj*, obj*);
obj* l_array_iterate___rarg(obj*, obj*, obj*);
obj* l_array_has__repr___rarg(obj*);
obj* l_array_foreach___rarg(obj*, obj*);
obj* l_array_uwrite___rarg(obj*, usize, obj*, obj*);
obj* l___private_init_data_array_basic_3__foreach__aux___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_array_nil___closed__1;
obj* l_array_uwrite_x_27___rarg___boxed(obj*, obj*, obj*);
obj* l_mk__array(obj*);
obj* l_array_pop(obj*);
obj* l_array_write_x_27___rarg(obj*, obj*, obj*);
obj* l_list_to__array(obj*);
obj* l_array_to__list(obj*);
obj* l___private_init_data_array_basic_2__rev__iterate__aux___main(obj*, obj*);
obj* l_array_foldl___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_array_map___rarg(obj*, obj*);
obj* l_array_map___rarg___lambda__1(obj*, obj*, obj*);
obj* l___private_init_data_array_basic_2__rev__iterate__aux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_array_read_x_27___rarg(obj*, obj*, obj*);
obj* l_array_to__list___rarg___closed__1;
obj* l_list_to__array___rarg(obj*);
obj* l_array_iterate(obj*, obj*);
obj* l___private_init_data_array_basic_1__iterate__aux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_mk__array___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_mk__array___rarg___lambda__1), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_mk__array___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
lean::dec(x_1);
return x_0;
}
}
obj* l_mk__array(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_mk__array___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_array_nil___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_array_nil___lambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_array_nil(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_array_nil___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* l_array_nil___lambda__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
lean_unreachable();
x_2 = lean::box(0);
lean::inc(x_2);
return x_2;
}
}
uint8 l_array_empty___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_4; uint8 x_5; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
lean::dec(x_4);
lean::dec(x_1);
if (x_5 == 0)
{
uint8 x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
}
}
obj* l_array_empty(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_empty___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_array_empty___rarg___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_array_empty___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* l_array_read___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::apply_1(x_2, x_1);
return x_5;
}
}
obj* l_array_read(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_read___rarg), 2, 0);
return x_2;
}
}
obj* l_array_write___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_array_write___rarg___lambda__1), 4, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_0);
lean::closure_set(x_5, 2, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_array_write___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_0);
if (x_4 == 0)
{
obj* x_7; obj* x_10; 
lean::dec(x_2);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::apply_1(x_7, x_3);
return x_10;
}
else
{
lean::dec(x_1);
lean::dec(x_3);
return x_2;
}
}
}
obj* l_array_write(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_write___rarg), 3, 0);
return x_2;
}
}
obj* l_array_read_x_27___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_5 == 0)
{
lean::dec(x_1);
lean::dec(x_2);
return x_0;
}
else
{
obj* x_10; 
lean::dec(x_0);
x_10 = l_array_read___rarg(x_1, x_2);
return x_10;
}
}
}
obj* l_array_read_x_27(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_read_x_27___rarg), 3, 0);
return x_2;
}
}
obj* l_array_write_x_27___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_5; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_5 == 0)
{
lean::dec(x_1);
lean::dec(x_2);
return x_0;
}
else
{
obj* x_9; 
x_9 = l_array_write___rarg(x_0, x_1, x_2);
return x_9;
}
}
}
obj* l_array_write_x_27(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_write_x_27___rarg), 3, 0);
return x_2;
}
}
obj* l_array_uread___rarg(obj* x_0, usize x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::dec(x_2);
x_4 = lean::usize_to_nat(x_1);
x_5 = l_array_read___rarg(x_0, x_4);
return x_5;
}
}
obj* l_array_uread(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_uread___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_array_uread___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; obj* x_4; 
x_3 = lean::unbox_size_t(x_1);
x_4 = l_array_uread___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_array_uwrite___rarg(obj* x_0, usize x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::dec(x_3);
x_5 = lean::usize_to_nat(x_1);
x_6 = l_array_write___rarg(x_0, x_5, x_2);
return x_6;
}
}
obj* l_array_uwrite(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_uwrite___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_array_uwrite___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
usize x_4; obj* x_5; 
x_4 = lean::unbox_size_t(x_1);
x_5 = l_array_uwrite___rarg(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_array_uread_x_27___rarg(obj* x_0, obj* x_1, usize x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_6; 
x_3 = lean::usize_to_nat(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_6 == 0)
{
lean::dec(x_1);
lean::dec(x_3);
return x_0;
}
else
{
obj* x_11; 
lean::dec(x_0);
x_11 = l_array_read___rarg(x_1, x_3);
return x_11;
}
}
}
obj* l_array_uread_x_27(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_uread_x_27___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_array_uread_x_27___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; obj* x_4; 
x_3 = lean::unbox_size_t(x_2);
x_4 = l_array_uread_x_27___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_array_uwrite_x_27___rarg(obj* x_0, usize x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_6; 
x_3 = lean::usize_to_nat(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_2);
return x_0;
}
else
{
obj* x_10; 
x_10 = l_array_write___rarg(x_0, x_3, x_2);
return x_10;
}
}
}
obj* l_array_uwrite_x_27(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_uwrite_x_27___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_array_uwrite_x_27___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; obj* x_4; 
x_3 = lean::unbox_size_t(x_1);
x_4 = l_array_uwrite_x_27___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* l_array_push___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_add(x_2, x_4);
lean::dec(x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_array_push___rarg___lambda__1), 4, 3);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_0);
lean::closure_set(x_7, 2, x_1);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_array_push___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::nat_dec_eq(x_3, x_0);
lean::dec(x_0);
if (x_4 == 0)
{
obj* x_7; obj* x_10; 
lean::dec(x_2);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::apply_1(x_7, x_3);
return x_10;
}
else
{
lean::dec(x_1);
lean::dec(x_3);
return x_2;
}
}
}
obj* l_array_push(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_push___rarg), 2, 0);
return x_2;
}
}
obj* l_array_pop___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = l_nat_pred___main(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_array_read___rarg), 2, 1);
lean::closure_set(x_4, 0, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_array_pop(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_pop___rarg), 1, 0);
return x_2;
}
}
obj* l___private_init_data_array_basic_1__iterate__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; uint8 x_7; 
lean::dec(x_3);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_2, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_9; obj* x_10; obj* x_15; obj* x_18; obj* x_19; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_2, x_9);
lean::dec(x_9);
lean::dec(x_2);
lean::inc(x_10);
lean::inc(x_0);
x_15 = l_array_read___rarg(x_0, x_10);
lean::inc(x_10);
lean::inc(x_1);
x_18 = l___private_init_data_array_basic_1__iterate__aux___main___rarg(x_0, x_1, x_10, lean::box(0), x_4);
x_19 = lean::apply_3(x_1, x_10, x_15, x_18);
return x_19;
}
else
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
}
obj* l___private_init_data_array_basic_1__iterate__aux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__iterate__aux___main___rarg), 5, 0);
return x_4;
}
}
obj* l___private_init_data_array_basic_1__iterate__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; 
lean::dec(x_3);
x_6 = l___private_init_data_array_basic_1__iterate__aux___main___rarg(x_0, x_1, x_2, lean::box(0), x_4);
return x_6;
}
}
obj* l___private_init_data_array_basic_1__iterate__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_1__iterate__aux___rarg), 5, 0);
return x_4;
}
}
obj* l_array_iterate___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = l___private_init_data_array_basic_1__iterate__aux___main___rarg(x_0, x_2, x_3, lean::box(0), x_1);
return x_5;
}
}
obj* l_array_iterate(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_array_iterate___rarg), 3, 0);
return x_4;
}
}
obj* l_array_foldl___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_array_foldl___rarg___lambda__1), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_array_iterate___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_array_foldl___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_1);
x_5 = lean::apply_2(x_0, x_2, x_3);
return x_5;
}
}
obj* l_array_foldl(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_array_foldl___rarg), 3, 0);
return x_4;
}
}
obj* l___private_init_data_array_basic_2__rev__iterate__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; uint8 x_7; 
lean::dec(x_3);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_2, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_9; obj* x_10; obj* x_15; obj* x_18; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_2, x_9);
lean::dec(x_9);
lean::dec(x_2);
lean::inc(x_10);
lean::inc(x_0);
x_15 = l_array_read___rarg(x_0, x_10);
lean::inc(x_10);
lean::inc(x_1);
x_18 = lean::apply_3(x_1, x_10, x_15, x_4);
x_2 = x_10;
x_3 = x_0;
x_4 = x_18;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
}
obj* l___private_init_data_array_basic_2__rev__iterate__aux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_2__rev__iterate__aux___main___rarg), 5, 0);
return x_4;
}
}
obj* l___private_init_data_array_basic_2__rev__iterate__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; 
lean::dec(x_3);
x_6 = l___private_init_data_array_basic_2__rev__iterate__aux___main___rarg(x_0, x_1, x_2, lean::box(0), x_4);
return x_6;
}
}
obj* l___private_init_data_array_basic_2__rev__iterate__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_2__rev__iterate__aux___rarg), 5, 0);
return x_4;
}
}
obj* l_array_rev__iterate___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = l___private_init_data_array_basic_2__rev__iterate__aux___main___rarg(x_0, x_2, x_3, lean::box(0), x_1);
return x_5;
}
}
obj* l_array_rev__iterate(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_array_rev__iterate___rarg), 3, 0);
return x_4;
}
}
obj* l_array_rev__foldl___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_array_foldl___rarg___lambda__1), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_array_rev__iterate___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* l_array_rev__foldl(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_array_rev__foldl___rarg), 3, 0);
return x_4;
}
}
obj* _init_l_array_to__list___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_array_to__list___rarg___lambda__1), 2, 0);
return x_0;
}
}
obj* l_array_to__list___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_1 = lean::box(0);
x_2 = l_array_to__list___rarg___closed__1;
lean::inc(x_2);
x_4 = l_array_rev__foldl___rarg(x_0, x_1, x_2);
return x_4;
}
}
obj* l_array_to__list___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_array_to__list(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_to__list___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_array_has__repr___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_array_to__list___rarg), 1, 0);
return x_0;
}
}
obj* l_array_has__repr___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_repr___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = l_array_has__repr___rarg___closed__1;
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_array_has__repr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_has__repr___rarg), 1, 0);
return x_2;
}
}
obj* l___private_init_data_array_basic_3__foreach__aux___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_3__foreach__aux___rarg___lambda__1), 4, 1);
lean::closure_set(x_2, 0, x_1);
lean::inc(x_0);
x_4 = l_array_iterate___rarg(x_0, x_0, x_2);
return x_4;
}
}
obj* l___private_init_data_array_basic_3__foreach__aux___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_1);
x_5 = lean::apply_2(x_0, x_1, x_2);
x_6 = l_array_write___rarg(x_3, x_1, x_5);
return x_6;
}
}
obj* l___private_init_data_array_basic_3__foreach__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_basic_3__foreach__aux___rarg), 2, 0);
return x_2;
}
}
obj* l_array_foreach___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_data_array_basic_3__foreach__aux___rarg(x_0, x_1);
return x_2;
}
}
obj* l_array_foreach(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_foreach___rarg), 2, 0);
return x_2;
}
}
obj* l_array_map___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_map___rarg___lambda__1), 3, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = l___private_init_data_array_basic_3__foreach__aux___rarg(x_1, x_2);
return x_3;
}
}
obj* l_array_map___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::apply_1(x_0, x_2);
return x_4;
}
}
obj* l_array_map(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_map___rarg), 2, 0);
return x_2;
}
}
obj* l_array_map_u_2082___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::nat_dec_le(x_3, x_5);
lean::dec(x_5);
lean::dec(x_3);
if (x_7 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_array_map_u_2082___rarg___lambda__1), 4, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_0);
x_11 = l___private_init_data_array_basic_3__foreach__aux___rarg(x_2, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_13; 
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_array_map_u_2082___rarg___lambda__1), 4, 2);
lean::closure_set(x_12, 0, x_2);
lean::closure_set(x_12, 1, x_0);
x_13 = l___private_init_data_array_basic_3__foreach__aux___rarg(x_1, x_12);
return x_13;
}
}
}
obj* l_array_map_u_2082___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_array_read___rarg(x_0, x_2);
x_5 = lean::apply_2(x_1, x_4, x_3);
return x_5;
}
}
obj* l_array_map_u_2082(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_array_map_u_2082___rarg), 3, 0);
return x_2;
}
}
obj* l_list_to__array__aux___main___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_array_push___rarg(x_1, x_3);
x_0 = x_5;
x_1 = x_8;
goto _start;
}
}
}
obj* l_list_to__array__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_to__array__aux___main___rarg), 2, 0);
return x_2;
}
}
obj* l_list_to__array__aux___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_to__array__aux___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_list_to__array__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_to__array__aux___rarg), 2, 0);
return x_2;
}
}
obj* l_list_to__array___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_array_nil___closed__1;
lean::inc(x_1);
x_3 = l_list_to__array__aux___main___rarg(x_0, x_1);
return x_3;
}
}
obj* l_list_to__array(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_to__array___rarg), 1, 0);
return x_2;
}
}
void initialize_init_data_nat_basic();
void initialize_init_data_fin_basic();
void initialize_init_data_usize();
void initialize_init_data_repr();
void initialize_init_function();
static bool _G_initialized = false;
void initialize_init_data_array_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_data_nat_basic();
 initialize_init_data_fin_basic();
 initialize_init_data_usize();
 initialize_init_data_repr();
 initialize_init_function();
 l_array_nil___closed__1 = _init_l_array_nil___closed__1();
 l_array_to__list___rarg___closed__1 = _init_l_array_to__list___rarg___closed__1();
 l_array_has__repr___rarg___closed__1 = _init_l_array_has__repr___rarg___closed__1();
}
