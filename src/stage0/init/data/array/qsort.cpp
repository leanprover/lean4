// Lean compiler output
// Module: init.data.array.qsort
// Imports: init.data.array.basic
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
obj* l_Array_partition___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux(obj*);
obj* l_Array_qsortAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_qsort___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_qsortAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_swap(obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main(obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_qsortAux___rarg(obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Array_partition(obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_partition___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_qsortAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_qsortAux(obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Array_qsortAux___main(obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l___private_init_data_array_qsort_1__partitionAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_qsort(obj*);
obj* l_Array_qsort___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; 
x_8 = lean::nat_dec_lt(x_7, x_3);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_9 = lean::array_swap(x_5, x_6, x_3);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
else
{
obj* x_11; obj* x_12; uint8 x_13; 
lean::inc(x_1);
x_11 = lean::array_get(x_1, x_5, x_7);
lean::inc(x_2);
lean::inc(x_4);
x_12 = lean::apply_2(x_2, x_11, x_4);
x_13 = lean::unbox(x_12);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_7, x_14);
lean::dec(x_7);
x_7 = x_15;
goto _start;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::array_swap(x_5, x_6, x_7);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_6, x_18);
lean::dec(x_6);
x_20 = lean::nat_add(x_7, x_18);
lean::dec(x_7);
x_5 = x_17;
x_6 = x_19;
x_7 = x_20;
goto _start;
}
}
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_qsort_1__partitionAux___main___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_3);
return x_8;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_qsort_1__partitionAux___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l___private_init_data_array_qsort_1__partitionAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_3);
return x_8;
}
}
obj* l_Array_partition___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_31; obj* x_32; obj* x_33; uint8 x_34; 
x_6 = lean::nat_add(x_4, x_5);
x_7 = lean::mk_nat_obj(2u);
x_8 = lean::nat_div(x_6, x_7);
lean::dec(x_6);
lean::inc(x_1);
x_31 = lean::array_get(x_1, x_2, x_8);
lean::inc(x_1);
x_32 = lean::array_get(x_1, x_2, x_4);
lean::inc(x_3);
x_33 = lean::apply_2(x_3, x_31, x_32);
x_34 = lean::unbox(x_33);
lean::dec(x_33);
if (x_34 == 0)
{
x_9 = x_2;
goto block_30;
}
else
{
obj* x_35; 
x_35 = lean::array_swap(x_2, x_4, x_8);
x_9 = x_35;
goto block_30;
}
block_30:
{
obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
lean::inc(x_1);
x_10 = lean::array_get(x_1, x_9, x_5);
lean::inc(x_1);
x_11 = lean::array_get(x_1, x_9, x_4);
lean::inc(x_3);
lean::inc(x_10);
x_12 = lean::apply_2(x_3, x_10, x_11);
x_13 = lean::unbox(x_12);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; uint8 x_16; 
lean::inc(x_1);
x_14 = lean::array_get(x_1, x_9, x_8);
lean::inc(x_3);
lean::inc(x_10);
x_15 = lean::apply_2(x_3, x_14, x_10);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_17; 
lean::dec(x_8);
lean::inc(x_4);
x_17 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_1, x_3, x_5, x_10, x_9, x_4, x_4);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_10);
x_18 = lean::array_swap(x_9, x_8, x_5);
lean::dec(x_8);
lean::inc(x_1);
x_19 = lean::array_get(x_1, x_18, x_5);
lean::inc(x_4);
x_20 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_1, x_3, x_5, x_19, x_18, x_4, x_4);
return x_20;
}
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; 
lean::dec(x_10);
x_21 = lean::array_swap(x_9, x_4, x_5);
lean::inc(x_1);
x_22 = lean::array_get(x_1, x_21, x_8);
lean::inc(x_1);
x_23 = lean::array_get(x_1, x_21, x_5);
lean::inc(x_3);
lean::inc(x_23);
x_24 = lean::apply_2(x_3, x_22, x_23);
x_25 = lean::unbox(x_24);
lean::dec(x_24);
if (x_25 == 0)
{
obj* x_26; 
lean::dec(x_8);
lean::inc(x_4);
x_26 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_1, x_3, x_5, x_23, x_21, x_4, x_4);
return x_26;
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_23);
x_27 = lean::array_swap(x_21, x_8, x_5);
lean::dec(x_8);
lean::inc(x_1);
x_28 = lean::array_get(x_1, x_27, x_5);
lean::inc(x_4);
x_29 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_1, x_3, x_5, x_28, x_27, x_4, x_4);
return x_29;
}
}
}
}
}
obj* l_Array_partition(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_partition___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_partition___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_partition___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Array_qsortAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_15; 
x_15 = lean::nat_dec_lt(x_4, x_5);
if (x_15 == 0)
{
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_41; obj* x_42; obj* x_43; uint8 x_44; 
x_16 = lean::nat_add(x_4, x_5);
x_17 = lean::mk_nat_obj(2u);
x_18 = lean::nat_div(x_16, x_17);
lean::dec(x_16);
lean::inc(x_1);
x_41 = lean::array_get(x_1, x_3, x_18);
lean::inc(x_1);
x_42 = lean::array_get(x_1, x_3, x_4);
lean::inc(x_2);
x_43 = lean::apply_2(x_2, x_41, x_42);
x_44 = lean::unbox(x_43);
lean::dec(x_43);
if (x_44 == 0)
{
x_19 = x_3;
goto block_40;
}
else
{
obj* x_45; 
x_45 = lean::array_swap(x_3, x_4, x_18);
x_19 = x_45;
goto block_40;
}
block_40:
{
obj* x_20; obj* x_21; obj* x_22; uint8 x_23; 
lean::inc(x_1);
x_20 = lean::array_get(x_1, x_19, x_5);
lean::inc(x_1);
x_21 = lean::array_get(x_1, x_19, x_4);
lean::inc(x_2);
lean::inc(x_20);
x_22 = lean::apply_2(x_2, x_20, x_21);
x_23 = lean::unbox(x_22);
lean::dec(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; uint8 x_26; 
lean::inc(x_1);
x_24 = lean::array_get(x_1, x_19, x_18);
lean::inc(x_2);
lean::inc(x_20);
x_25 = lean::apply_2(x_2, x_24, x_20);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
obj* x_27; 
lean::dec(x_18);
lean::inc(x_4, 2);
lean::inc(x_2);
lean::inc(x_1);
x_27 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_20, x_19, x_4, x_4);
x_6 = x_27;
goto block_14;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_20);
x_28 = lean::array_swap(x_19, x_18, x_5);
lean::dec(x_18);
lean::inc(x_1);
x_29 = lean::array_get(x_1, x_28, x_5);
lean::inc(x_4, 2);
lean::inc(x_2);
lean::inc(x_1);
x_30 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_29, x_28, x_4, x_4);
x_6 = x_30;
goto block_14;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; uint8 x_35; 
lean::dec(x_20);
x_31 = lean::array_swap(x_19, x_4, x_5);
lean::inc(x_1);
x_32 = lean::array_get(x_1, x_31, x_18);
lean::inc(x_1);
x_33 = lean::array_get(x_1, x_31, x_5);
lean::inc(x_2);
lean::inc(x_33);
x_34 = lean::apply_2(x_2, x_32, x_33);
x_35 = lean::unbox(x_34);
lean::dec(x_34);
if (x_35 == 0)
{
obj* x_36; 
lean::dec(x_18);
lean::inc(x_4, 2);
lean::inc(x_2);
lean::inc(x_1);
x_36 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_33, x_31, x_4, x_4);
x_6 = x_36;
goto block_14;
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_33);
x_37 = lean::array_swap(x_31, x_18, x_5);
lean::dec(x_18);
lean::inc(x_1);
x_38 = lean::array_get(x_1, x_37, x_5);
lean::inc(x_4, 2);
lean::inc(x_2);
lean::inc(x_1);
x_39 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_38, x_37, x_4, x_4);
x_6 = x_39;
goto block_14;
}
}
}
}
block_14:
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
lean::dec(x_6);
x_9 = lean::nat_dec_le(x_5, x_7);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
lean::inc(x_2);
lean::inc(x_1);
x_10 = l_Array_qsortAux___main___rarg(x_1, x_2, x_8, x_4, x_7);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_7, x_11);
lean::dec(x_7);
x_3 = x_10;
x_4 = x_12;
goto _start;
}
else
{
lean::dec(x_7);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
}
}
}
obj* l_Array_qsortAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_qsortAux___main___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_qsortAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_qsortAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Array_qsortAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_qsortAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Array_qsortAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_qsortAux___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_qsortAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_qsortAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Array_qsort___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_qsortAux___main___rarg(x_1, x_3, x_2, x_4, x_5);
return x_6;
}
}
obj* l_Array_qsort(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_qsort___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Array_qsort___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_qsort___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* initialize_init_data_array_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_array_qsort(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_array_basic(w);
if (io_result_is_error(w)) return w;
return w;
}
