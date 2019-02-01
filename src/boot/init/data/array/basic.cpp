// Lean compiler output
// Module: init.data.array.basic
// Imports: init.data.nat.basic init.data.fin.basic init.data.usize init.data.repr init.function
#include "runtime/object.h"
#include "runtime/apply.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s4_list_s9_to__array(obj*);
obj* _l_s5_array_s8_read_x27_s6___rarg(obj*, obj*, obj*);
obj* _l_s8_function_s4_comp_s6___rarg(obj*, obj*, obj*);
obj* _l_s5_array_s5_empty(obj*);
obj* _l_s5_array_s5_foldl(obj*, obj*);
obj* _l_s5_array_s4_read_s6___rarg(obj*, obj*);
obj* _l_s4_list_s14_to__array__aux_s6___rarg(obj*, obj*);
obj* _l_s5_array_s3_nil(obj*);
obj* _l_s5_array_s9_map_u2082_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s5_array_s5_empty_s6___rarg_s7___boxed(obj*);
obj* _l_s9_mk__array_s6___rarg(obj*, obj*);
obj* _l_s5_array_s3_pop_s6___rarg(obj*);
obj* _l_s5_array_s12_rev__iterate(obj*, obj*);
obj* _l_s4_list_s14_to__array__aux_s6___main(obj*);
obj* _l_s5_array_s10_uwrite_x27_s6___rarg_s7___boxed(obj*, obj*, obj*);
obj* _l_s5_array_s3_map(obj*);
obj* _l_s4_list_s14_to__array__aux_s6___main_s6___rarg(obj*, obj*);
obj* _l_s5_array_s7_iterate(obj*, obj*);
obj* _l_s5_array_s5_foldl_s6___rarg(obj*, obj*, obj*);
obj* _l_s5_array_s9_uread_x27(obj*);
obj* _l_s9___private_2151191555__s12_iterate__aux_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s5_array_s10_rev__foldl(obj*, obj*);
obj* _l_s9_mk__array_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s5_array_s9_has__repr_s6___rarg_s11___closed__1;
obj* _l_s5_array_s7_foreach(obj*);
obj* _l_s9_mk__array(obj*);
obj* _l_s9___private_2151191555__s12_iterate__aux_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s5_array_s9_map_u2082(obj*);
obj* _l_s9___private_2151191555__s12_iterate__aux_s6___main(obj*, obj*);
obj* _l_s5_array_s9_write_x27_s6___rarg(obj*, obj*, obj*);
obj* _l_s5_array_s9_has__repr_s6___rarg(obj*);
obj* _l_s5_array_s12_rev__iterate_s6___rarg(obj*, obj*, obj*);
obj* _l_s5_array_s6_uwrite_s6___rarg_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s5_array_s7_iterate_s6___rarg(obj*, obj*, obj*);
obj* _l_s5_array_s4_push_s6___rarg(obj*, obj*);
obj* _l_s5_array_s9_map_u2082_s6___rarg(obj*, obj*, obj*);
obj* _l_s9___private_2406439935__s12_foreach__aux_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s9___private_2406439935__s12_foreach__aux(obj*);
obj* _l_s5_array_s8_read_x27(obj*);
obj* _l_s3_nat_s4_pred_s6___main(obj*);
obj* _l_s9___private_717503411__s17_rev__iterate__aux(obj*, obj*);
obj* _l_s5_array_s3_map_s6___rarg(obj*, obj*);
obj* _l_s5_array_s5_foldl_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s5_array_s4_push(obj*);
obj* _l_s5_array_s5_uread_s6___rarg_s7___boxed(obj*, obj*, obj*);
unsigned char _l_s5_array_s5_empty_s6___rarg(obj*);
obj* _l_s5_array_s6_uwrite(obj*);
obj* _l_s5_array_s9_uread_x27_s6___rarg(obj*, obj*, size_t);
obj* _l_s5_array_s9_uread_x27_s6___rarg_s7___boxed(obj*, obj*, obj*);
obj* _l_s5_array_s8_to__list_s6___rarg_s11___closed__1;
obj* _l_s5_array_s3_nil_s11___lambda__1(obj*);
obj* _l_s9___private_717503411__s17_rev__iterate__aux_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s5_array_s10_rev__foldl_s6___rarg(obj*, obj*, obj*);
obj* _l_s5_array_s9_write_x27(obj*);
obj* _l_s9___private_2151191555__s12_iterate__aux(obj*, obj*);
obj* _l_s5_array_s10_uwrite_x27_s6___rarg(obj*, size_t, obj*);
obj* _l_s5_array_s5_write_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_list_s9_to__array_s6___rarg(obj*);
obj* _l_s5_array_s4_push_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s5_array_s5_write(obj*);
obj* _l_s4_list_s4_repr_s6___rarg(obj*, obj*);
obj* _l_s5_array_s4_read(obj*);
obj* _l_s9___private_2406439935__s12_foreach__aux_s6___rarg(obj*, obj*);
obj* _l_s5_array_s6_uwrite_s6___rarg(obj*, size_t, obj*, obj*);
obj* _l_s5_array_s3_pop(obj*);
obj* _l_s5_array_s9_has__repr(obj*);
obj* _l_s5_array_s10_uwrite_x27(obj*);
obj* _l_s4_list_s14_to__array__aux(obj*);
obj* _l_s5_array_s5_write_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s5_array_s5_uread(obj*);
obj* _l_s5_array_s3_map_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s5_array_s8_to__list_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s5_usize_s7_to__nat_s6___main(size_t);
obj* _l_s9___private_717503411__s17_rev__iterate__aux_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s5_array_s3_nil_s11___closed__1;
obj* _l_s5_array_s7_foreach_s6___rarg(obj*, obj*);
obj* _l_s5_array_s8_to__list(obj*);
obj* _l_s5_array_s8_to__list_s6___rarg(obj*);
obj* _l_s5_array_s5_uread_s6___rarg(obj*, size_t, obj*);
obj* _l_s9___private_717503411__s17_rev__iterate__aux_s6___main(obj*, obj*);
obj* _l_s9_mk__array_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_mk__array_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _l_s9_mk__array_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{

lean::dec(x_1);
return x_0;
}
}
obj* _l_s9_mk__array(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_mk__array_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_array_s3_nil(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = _l_s5_array_s3_nil_s11___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* _init__l_s5_array_s3_nil_s11___closed__1() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(0u);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s3_nil_s11___lambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s5_array_s3_nil_s11___lambda__1(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
lean_unreachable();
x_2 = lean::box(0);
lean::inc(x_2);
return x_2;
}
}
unsigned char _l_s5_array_s5_empty_s6___rarg(obj* x_0) {
{
obj* x_1; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
lean::dec(x_4);
lean::dec(x_1);
if (lean::obj_tag(x_5) == 0)
{
unsigned char x_9; 
lean::dec(x_5);
x_9 = 0;
return x_9;
}
else
{
unsigned char x_11; 
lean::dec(x_5);
x_11 = 1;
return x_11;
}
}
}
obj* _l_s5_array_s5_empty(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s5_empty_s6___rarg_s7___boxed), 1, 0);
return x_2;
}
}
obj* _l_s5_array_s5_empty_s6___rarg_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = _l_s5_array_s5_empty_s6___rarg(x_0);
x_2 = lean::box(x_1);
return x_2;
}
}
obj* _l_s5_array_s4_read_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::apply_1(x_2, x_1);
return x_5;
}
}
obj* _l_s5_array_s4_read(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s4_read_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_array_s5_write_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s5_write_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_0);
lean::closure_set(x_5, 2, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _l_s5_array_s5_write_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; 
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_11; 
lean::dec(x_4);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::apply_1(x_8, x_3);
return x_11;
}
else
{

lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
return x_2;
}
}
}
obj* _l_s5_array_s5_write(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s5_write_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s5_array_s8_read_x27_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_5) == 0)
{

lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_0;
}
else
{
obj* x_12; 
lean::dec(x_5);
lean::dec(x_0);
x_12 = _l_s5_array_s4_read_s6___rarg(x_1, x_2);
return x_12;
}
}
}
obj* _l_s5_array_s8_read_x27(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s8_read_x27_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s5_array_s9_write_x27_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_5) == 0)
{

lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_0;
}
else
{
obj* x_11; 
lean::dec(x_5);
x_11 = _l_s5_array_s5_write_s6___rarg(x_0, x_1, x_2);
return x_11;
}
}
}
obj* _l_s5_array_s9_write_x27(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s9_write_x27_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s5_array_s5_uread_s6___rarg(obj* x_0, size_t x_1, obj* x_2) {
{
obj* x_4; obj* x_5; 
lean::dec(x_2);
x_4 = _l_s5_usize_s7_to__nat_s6___main(x_1);
x_5 = _l_s5_array_s4_read_s6___rarg(x_0, x_4);
return x_5;
}
}
obj* _l_s5_array_s5_uread(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s5_uread_s6___rarg_s7___boxed), 3, 0);
return x_2;
}
}
obj* _l_s5_array_s5_uread_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
size_t x_3; obj* x_4; 
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_array_s5_uread_s6___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* _l_s5_array_s6_uwrite_s6___rarg(obj* x_0, size_t x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_6; 
lean::dec(x_3);
x_5 = _l_s5_usize_s7_to__nat_s6___main(x_1);
x_6 = _l_s5_array_s5_write_s6___rarg(x_0, x_5, x_2);
return x_6;
}
}
obj* _l_s5_array_s6_uwrite(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s6_uwrite_s6___rarg_s7___boxed), 4, 0);
return x_2;
}
}
obj* _l_s5_array_s6_uwrite_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
size_t x_4; obj* x_5; 
x_4 = lean::unbox_size_t(x_1);
x_5 = _l_s5_array_s6_uwrite_s6___rarg(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _l_s5_array_s9_uread_x27_s6___rarg(obj* x_0, obj* x_1, size_t x_2) {
{
obj* x_3; obj* x_4; obj* x_6; 
x_3 = _l_s5_usize_s7_to__nat_s6___main(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (lean::obj_tag(x_6) == 0)
{

lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_3);
return x_0;
}
else
{
obj* x_13; 
lean::dec(x_6);
lean::dec(x_0);
x_13 = _l_s5_array_s4_read_s6___rarg(x_1, x_3);
return x_13;
}
}
}
obj* _l_s5_array_s9_uread_x27(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s9_uread_x27_s6___rarg_s7___boxed), 3, 0);
return x_2;
}
}
obj* _l_s5_array_s9_uread_x27_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
size_t x_3; obj* x_4; 
x_3 = lean::unbox_size_t(x_2);
x_4 = _l_s5_array_s9_uread_x27_s6___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s5_array_s10_uwrite_x27_s6___rarg(obj* x_0, size_t x_1, obj* x_2) {
{
obj* x_3; obj* x_4; obj* x_6; 
x_3 = _l_s5_usize_s7_to__nat_s6___main(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (lean::obj_tag(x_6) == 0)
{

lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_3);
return x_0;
}
else
{
obj* x_12; 
lean::dec(x_6);
x_12 = _l_s5_array_s5_write_s6___rarg(x_0, x_3, x_2);
return x_12;
}
}
}
obj* _l_s5_array_s10_uwrite_x27(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s10_uwrite_x27_s6___rarg_s7___boxed), 3, 0);
return x_2;
}
}
obj* _l_s5_array_s10_uwrite_x27_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
size_t x_3; obj* x_4; 
x_3 = lean::unbox_size_t(x_1);
x_4 = _l_s5_array_s10_uwrite_x27_s6___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* _l_s5_array_s4_push_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_add(x_2, x_4);
lean::dec(x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s4_push_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_0);
lean::closure_set(x_7, 2, x_1);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* _l_s5_array_s4_push_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; 
x_4 = lean::nat_dec_eq(x_3, x_0);
lean::dec(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_11; 
lean::dec(x_4);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::apply_1(x_8, x_3);
return x_11;
}
else
{

lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
return x_2;
}
}
}
obj* _l_s5_array_s4_push(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s4_push_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_array_s3_pop_s6___rarg(obj* x_0) {
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = _l_s3_nat_s4_pred_s6___main(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s4_read_s6___rarg), 2, 1);
lean::closure_set(x_4, 0, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* _l_s5_array_s3_pop(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s3_pop_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s9___private_2151191555__s12_iterate__aux_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_7; 
lean::dec(x_3);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_2, x_6);
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_11; obj* x_16; obj* x_19; obj* x_20; 
lean::dec(x_7);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_2, x_10);
lean::dec(x_10);
lean::dec(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_16 = _l_s5_array_s4_read_s6___rarg(x_0, x_11);
lean::inc(x_11);
lean::inc(x_1);
x_19 = _l_s9___private_2151191555__s12_iterate__aux_s6___main_s6___rarg(x_0, x_1, x_11, lean::box(0), x_4);
x_20 = lean::apply_3(x_1, x_11, x_16, x_19);
return x_20;
}
else
{

lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
}
obj* _l_s9___private_2151191555__s12_iterate__aux_s6___main(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_2151191555__s12_iterate__aux_s6___main_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s9___private_2151191555__s12_iterate__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; 
lean::dec(x_3);
x_6 = _l_s9___private_2151191555__s12_iterate__aux_s6___main_s6___rarg(x_0, x_1, x_2, lean::box(0), x_4);
return x_6;
}
}
obj* _l_s9___private_2151191555__s12_iterate__aux(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_2151191555__s12_iterate__aux_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s5_array_s7_iterate_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = _l_s9___private_2151191555__s12_iterate__aux_s6___main_s6___rarg(x_0, x_2, x_3, lean::box(0), x_1);
return x_5;
}
}
obj* _l_s5_array_s7_iterate(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s7_iterate_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s5_array_s5_foldl_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s5_foldl_s6___rarg_s11___lambda__1), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = _l_s5_array_s7_iterate_s6___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s5_array_s5_foldl_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; 
lean::dec(x_1);
x_5 = lean::apply_2(x_0, x_2, x_3);
return x_5;
}
}
obj* _l_s5_array_s5_foldl(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s5_foldl_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s9___private_717503411__s17_rev__iterate__aux_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_7; 
lean::dec(x_3);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_2, x_6);
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_11; obj* x_16; obj* x_19; obj* x_20; 
lean::dec(x_7);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_2, x_10);
lean::dec(x_10);
lean::dec(x_2);
lean::inc(x_11);
lean::inc(x_0);
x_16 = _l_s5_array_s4_read_s6___rarg(x_0, x_11);
lean::inc(x_11);
lean::inc(x_1);
x_19 = lean::apply_3(x_1, x_11, x_16, x_4);
x_20 = _l_s9___private_717503411__s17_rev__iterate__aux_s6___main_s6___rarg(x_0, x_1, x_11, lean::box(0), x_19);
return x_20;
}
else
{

lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
}
obj* _l_s9___private_717503411__s17_rev__iterate__aux_s6___main(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_717503411__s17_rev__iterate__aux_s6___main_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s9___private_717503411__s17_rev__iterate__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; 
lean::dec(x_3);
x_6 = _l_s9___private_717503411__s17_rev__iterate__aux_s6___main_s6___rarg(x_0, x_1, x_2, lean::box(0), x_4);
return x_6;
}
}
obj* _l_s9___private_717503411__s17_rev__iterate__aux(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_717503411__s17_rev__iterate__aux_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s5_array_s12_rev__iterate_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = _l_s9___private_717503411__s17_rev__iterate__aux_s6___main_s6___rarg(x_0, x_2, x_3, lean::box(0), x_1);
return x_5;
}
}
obj* _l_s5_array_s12_rev__iterate(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s12_rev__iterate_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s5_array_s10_rev__foldl_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s5_foldl_s6___rarg_s11___lambda__1), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = _l_s5_array_s12_rev__iterate_s6___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s5_array_s10_rev__foldl(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s10_rev__foldl_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s5_array_s8_to__list_s6___rarg(obj* x_0) {
{
obj* x_1; obj* x_2; obj* x_4; 
x_1 = lean::alloc_cnstr(0, 0, 0);
;
x_2 = _l_s5_array_s8_to__list_s6___rarg_s11___closed__1;
lean::inc(x_2);
x_4 = _l_s5_array_s10_rev__foldl_s6___rarg(x_0, x_1, x_2);
return x_4;
}
}
obj* _init__l_s5_array_s8_to__list_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s8_to__list_s6___rarg_s11___lambda__1), 2, 0);
return x_0;
}
}
obj* _l_s5_array_s8_to__list_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s5_array_s8_to__list(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s8_to__list_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s5_array_s9_has__repr_s6___rarg(obj* x_0) {
{
obj* x_1; obj* x_2; obj* x_4; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s4_repr_s6___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = _l_s5_array_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
return x_4;
}
}
obj* _init__l_s5_array_s9_has__repr_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s8_to__list_s6___rarg), 1, 0);
return x_0;
}
}
obj* _l_s5_array_s9_has__repr(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s9_has__repr_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s9___private_2406439935__s12_foreach__aux_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_2406439935__s12_foreach__aux_s6___rarg_s11___lambda__1), 4, 1);
lean::closure_set(x_2, 0, x_1);
lean::inc(x_0);
x_4 = _l_s5_array_s7_iterate_s6___rarg(x_0, x_0, x_2);
return x_4;
}
}
obj* _l_s9___private_2406439935__s12_foreach__aux_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_6; 
lean::inc(x_1);
x_5 = lean::apply_2(x_0, x_1, x_2);
x_6 = _l_s5_array_s5_write_s6___rarg(x_3, x_1, x_5);
return x_6;
}
}
obj* _l_s9___private_2406439935__s12_foreach__aux(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_2406439935__s12_foreach__aux_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_array_s7_foreach_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s9___private_2406439935__s12_foreach__aux_s6___rarg(x_0, x_1);
return x_2;
}
}
obj* _l_s5_array_s7_foreach(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s7_foreach_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_array_s3_map_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s3_map_s6___rarg_s11___lambda__1), 3, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = _l_s9___private_2406439935__s12_foreach__aux_s6___rarg(x_1, x_2);
return x_3;
}
}
obj* _l_s5_array_s3_map_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::apply_1(x_0, x_2);
return x_4;
}
}
obj* _l_s5_array_s3_map(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s3_map_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_array_s9_map_u2082_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_7; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::nat_dec_le(x_3, x_5);
lean::dec(x_5);
lean::dec(x_3);
if (lean::obj_tag(x_7) == 0)
{
obj* x_11; obj* x_12; 
lean::dec(x_7);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s9_map_u2082_s6___rarg_s11___lambda__1), 4, 2);
lean::closure_set(x_11, 0, x_1);
lean::closure_set(x_11, 1, x_0);
x_12 = _l_s9___private_2406439935__s12_foreach__aux_s6___rarg(x_2, x_11);
return x_12;
}
else
{
obj* x_14; obj* x_15; 
lean::dec(x_7);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s9_map_u2082_s6___rarg_s11___lambda__1), 4, 2);
lean::closure_set(x_14, 0, x_2);
lean::closure_set(x_14, 1, x_0);
x_15 = _l_s9___private_2406439935__s12_foreach__aux_s6___rarg(x_1, x_14);
return x_15;
}
}
}
obj* _l_s5_array_s9_map_u2082_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; obj* x_5; 
x_4 = _l_s5_array_s4_read_s6___rarg(x_0, x_2);
x_5 = lean::apply_2(x_1, x_4, x_3);
return x_5;
}
}
obj* _l_s5_array_s9_map_u2082(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_array_s9_map_u2082_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s4_list_s14_to__array__aux_s6___main_s6___rarg(obj* x_0, obj* x_1) {
{

if (lean::obj_tag(x_0) == 0)
{

lean::dec(x_0);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = _l_s5_array_s4_push_s6___rarg(x_1, x_3);
x_9 = _l_s4_list_s14_to__array__aux_s6___main_s6___rarg(x_5, x_8);
return x_9;
}
}
}
obj* _l_s4_list_s14_to__array__aux_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s14_to__array__aux_s6___main_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s4_list_s14_to__array__aux_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = _l_s4_list_s14_to__array__aux_s6___main_s6___rarg(x_0, x_1);
return x_2;
}
}
obj* _l_s4_list_s14_to__array__aux(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s14_to__array__aux_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s4_list_s9_to__array_s6___rarg(obj* x_0) {
{
obj* x_1; obj* x_3; 
x_1 = _l_s5_array_s3_nil_s11___closed__1;
lean::inc(x_1);
x_3 = _l_s4_list_s14_to__array__aux_s6___main_s6___rarg(x_0, x_1);
return x_3;
}
}
obj* _l_s4_list_s9_to__array(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s9_to__array_s6___rarg), 1, 0);
return x_2;
}
}
void _l_initialize__l_s4_init_s4_data_s3_nat_s5_basic();
void _l_initialize__l_s4_init_s4_data_s3_fin_s5_basic();
void _l_initialize__l_s4_init_s4_data_s5_usize();
void _l_initialize__l_s4_init_s4_data_s4_repr();
void _l_initialize__l_s4_init_s8_function();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_data_s5_array_s5_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s3_nat_s5_basic();
 _l_initialize__l_s4_init_s4_data_s3_fin_s5_basic();
 _l_initialize__l_s4_init_s4_data_s5_usize();
 _l_initialize__l_s4_init_s4_data_s4_repr();
 _l_initialize__l_s4_init_s8_function();
 _l_s5_array_s3_nil_s11___closed__1 = _init__l_s5_array_s3_nil_s11___closed__1();
 _l_s5_array_s8_to__list_s6___rarg_s11___closed__1 = _init__l_s5_array_s8_to__list_s6___rarg_s11___closed__1();
 _l_s5_array_s9_has__repr_s6___rarg_s11___closed__1 = _init__l_s5_array_s9_has__repr_s6___rarg_s11___closed__1();
}
