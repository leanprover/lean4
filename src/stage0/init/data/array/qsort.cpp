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
uint8 x_6; 
x_6 = lean::nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_56; obj* x_57; obj* x_58; uint8 x_59; 
x_7 = lean::nat_add(x_4, x_5);
x_8 = lean::mk_nat_obj(2u);
x_9 = lean::nat_div(x_7, x_8);
lean::dec(x_7);
lean::inc(x_1);
x_56 = lean::array_get(x_1, x_3, x_9);
lean::inc(x_1);
x_57 = lean::array_get(x_1, x_3, x_4);
lean::inc(x_2);
x_58 = lean::apply_2(x_2, x_56, x_57);
x_59 = lean::unbox(x_58);
lean::dec(x_58);
if (x_59 == 0)
{
x_10 = x_3;
goto block_55;
}
else
{
obj* x_60; 
x_60 = lean::array_swap(x_3, x_4, x_9);
x_10 = x_60;
goto block_55;
}
block_55:
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
lean::inc(x_1);
x_11 = lean::array_get(x_1, x_10, x_5);
lean::inc(x_1);
x_12 = lean::array_get(x_1, x_10, x_4);
lean::inc(x_2);
lean::inc(x_11);
x_13 = lean::apply_2(x_2, x_11, x_12);
x_14 = lean::unbox(x_13);
lean::dec(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; uint8 x_17; 
lean::inc(x_1);
x_15 = lean::array_get(x_1, x_10, x_9);
lean::inc(x_2);
lean::inc(x_11);
x_16 = lean::apply_2(x_2, x_15, x_11);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::inc(x_4, 2);
lean::inc(x_2);
lean::inc(x_1);
x_18 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_11, x_10, x_4, x_4);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_18, 1);
lean::inc(x_20);
lean::dec(x_18);
lean::inc(x_2);
lean::inc(x_1);
x_21 = l_Array_qsortAux___main___rarg(x_1, x_2, x_20, x_4, x_19);
x_22 = lean::mk_nat_obj(1u);
x_23 = lean::nat_add(x_19, x_22);
lean::dec(x_19);
x_3 = x_21;
x_4 = x_23;
goto _start;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_11);
x_25 = lean::array_swap(x_10, x_9, x_5);
lean::dec(x_9);
lean::inc(x_1);
x_26 = lean::array_get(x_1, x_25, x_5);
lean::inc(x_4, 2);
lean::inc(x_2);
lean::inc(x_1);
x_27 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_26, x_25, x_4, x_4);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
lean::dec(x_27);
lean::inc(x_2);
lean::inc(x_1);
x_30 = l_Array_qsortAux___main___rarg(x_1, x_2, x_29, x_4, x_28);
x_31 = lean::mk_nat_obj(1u);
x_32 = lean::nat_add(x_28, x_31);
lean::dec(x_28);
x_3 = x_30;
x_4 = x_32;
goto _start;
}
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; uint8 x_38; 
lean::dec(x_11);
x_34 = lean::array_swap(x_10, x_4, x_5);
lean::inc(x_1);
x_35 = lean::array_get(x_1, x_34, x_9);
lean::inc(x_1);
x_36 = lean::array_get(x_1, x_34, x_5);
lean::inc(x_2);
lean::inc(x_36);
x_37 = lean::apply_2(x_2, x_35, x_36);
x_38 = lean::unbox(x_37);
lean::dec(x_37);
if (x_38 == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_9);
lean::inc(x_4, 2);
lean::inc(x_2);
lean::inc(x_1);
x_39 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_36, x_34, x_4, x_4);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_39, 1);
lean::inc(x_41);
lean::dec(x_39);
lean::inc(x_2);
lean::inc(x_1);
x_42 = l_Array_qsortAux___main___rarg(x_1, x_2, x_41, x_4, x_40);
x_43 = lean::mk_nat_obj(1u);
x_44 = lean::nat_add(x_40, x_43);
lean::dec(x_40);
x_3 = x_42;
x_4 = x_44;
goto _start;
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_36);
x_46 = lean::array_swap(x_34, x_9, x_5);
lean::dec(x_9);
lean::inc(x_1);
x_47 = lean::array_get(x_1, x_46, x_5);
lean::inc(x_4, 2);
lean::inc(x_2);
lean::inc(x_1);
x_48 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_1, x_2, x_5, x_47, x_46, x_4, x_4);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_48, 1);
lean::inc(x_50);
lean::dec(x_48);
lean::inc(x_2);
lean::inc(x_1);
x_51 = l_Array_qsortAux___main___rarg(x_1, x_2, x_50, x_4, x_49);
x_52 = lean::mk_nat_obj(1u);
x_53 = lean::nat_add(x_49, x_52);
lean::dec(x_49);
x_3 = x_51;
x_4 = x_53;
goto _start;
}
}
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
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Array"), "partition"), 1, l_Array_partition);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Array"), "qsortAux"), 1, l_Array_qsortAux);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Array"), "qsort"), 1, l_Array_qsort);
return w;
}
