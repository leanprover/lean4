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
obj* l_Array_partition___boxed(obj*);
obj* l_Array_qsortAux___boxed(obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___boxed(obj*);
obj* l_Array_qsort___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___boxed(obj*);
obj* l_Array_qsortAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
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
obj* l_Array_qsortAux___main___boxed(obj*);
obj* l_Array_qsortAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_qsortAux(obj*);
obj* l_Array_qsort___boxed(obj*);
obj* l_Array_qsortAux___main(obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l___private_init_data_array_qsort_1__partitionAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_qsort(obj*);
obj* l_Array_qsort___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_data_array_qsort_1__partitionAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = lean::nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
obj* x_12; obj* x_13; 
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_0);
x_12 = lean::array_swap(x_4, x_5, x_2);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_5);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
else
{
obj* x_15; obj* x_18; uint8 x_19; 
lean::inc(x_0);
x_15 = lean::array_get(x_0, x_4, x_6);
lean::inc(x_3);
lean::inc(x_1);
x_18 = lean::apply_2(x_1, x_15, x_3);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::mk_nat_obj(1ul);
x_21 = lean::nat_add(x_6, x_20);
lean::dec(x_6);
x_6 = x_21;
goto _start;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_28; 
x_24 = lean::array_swap(x_4, x_5, x_6);
x_25 = lean::mk_nat_obj(1ul);
x_26 = lean::nat_add(x_5, x_25);
lean::dec(x_5);
x_28 = lean::nat_add(x_6, x_25);
lean::dec(x_6);
x_4 = x_24;
x_5 = x_26;
x_6 = x_28;
goto _start;
}
}
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_qsort_1__partitionAux___main___rarg___boxed), 7, 0);
return x_1;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
return x_7;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_data_array_qsort_1__partitionAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_data_array_qsort_1__partitionAux___rarg___boxed), 7, 0);
return x_1;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_data_array_qsort_1__partitionAux___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
return x_7;
}
}
obj* l___private_init_data_array_qsort_1__partitionAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_data_array_qsort_1__partitionAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_partition___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_5 = lean::nat_add(x_3, x_4);
x_6 = lean::mk_nat_obj(2ul);
x_7 = lean::nat_div(x_5, x_6);
lean::dec(x_5);
lean::inc(x_0);
x_12 = lean::array_get(x_0, x_1, x_7);
lean::inc(x_0);
x_14 = lean::array_get(x_0, x_1, x_3);
lean::inc(x_2);
x_16 = lean::apply_2(x_2, x_12, x_14);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
x_9 = x_1;
goto lbl_10;
}
else
{
obj* x_18; 
x_18 = lean::array_swap(x_1, x_3, x_7);
x_9 = x_18;
goto lbl_10;
}
lbl_10:
{
obj* x_20; obj* x_22; obj* x_25; uint8 x_26; 
lean::inc(x_0);
x_20 = lean::array_get(x_0, x_9, x_4);
lean::inc(x_0);
x_22 = lean::array_get(x_0, x_9, x_3);
lean::inc(x_20);
lean::inc(x_2);
x_25 = lean::apply_2(x_2, x_20, x_22);
x_26 = lean::unbox(x_25);
if (x_26 == 0)
{
obj* x_28; obj* x_31; uint8 x_32; 
lean::inc(x_0);
x_28 = lean::array_get(x_0, x_9, x_7);
lean::inc(x_20);
lean::inc(x_2);
x_31 = lean::apply_2(x_2, x_28, x_20);
x_32 = lean::unbox(x_31);
if (x_32 == 0)
{
obj* x_35; 
lean::dec(x_7);
lean::inc(x_3);
x_35 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_0, x_2, x_4, x_20, x_9, x_3, x_3);
return x_35;
}
else
{
obj* x_37; obj* x_40; obj* x_42; 
lean::dec(x_20);
x_37 = lean::array_swap(x_9, x_7, x_4);
lean::dec(x_7);
lean::inc(x_0);
x_40 = lean::array_get(x_0, x_37, x_4);
lean::inc(x_3);
x_42 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_0, x_2, x_4, x_40, x_37, x_3, x_3);
return x_42;
}
}
else
{
obj* x_44; obj* x_46; obj* x_48; obj* x_51; uint8 x_52; 
lean::dec(x_20);
x_44 = lean::array_swap(x_9, x_3, x_4);
lean::inc(x_0);
x_46 = lean::array_get(x_0, x_44, x_7);
lean::inc(x_0);
x_48 = lean::array_get(x_0, x_44, x_4);
lean::inc(x_48);
lean::inc(x_2);
x_51 = lean::apply_2(x_2, x_46, x_48);
x_52 = lean::unbox(x_51);
if (x_52 == 0)
{
obj* x_55; 
lean::dec(x_7);
lean::inc(x_3);
x_55 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_0, x_2, x_4, x_48, x_44, x_3, x_3);
return x_55;
}
else
{
obj* x_57; obj* x_60; obj* x_62; 
lean::dec(x_48);
x_57 = lean::array_swap(x_44, x_7, x_4);
lean::dec(x_7);
lean::inc(x_0);
x_60 = lean::array_get(x_0, x_57, x_4);
lean::inc(x_3);
x_62 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_0, x_2, x_4, x_60, x_57, x_3, x_3);
return x_62;
}
}
}
}
}
obj* l_Array_partition(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_partition___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Array_partition___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_partition___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Array_partition___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_partition(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_qsortAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_20; uint8 x_21; 
x_9 = lean::nat_add(x_3, x_4);
x_10 = lean::mk_nat_obj(2ul);
x_11 = lean::nat_div(x_9, x_10);
lean::dec(x_9);
lean::inc(x_0);
x_16 = lean::array_get(x_0, x_2, x_11);
lean::inc(x_0);
x_18 = lean::array_get(x_0, x_2, x_3);
lean::inc(x_1);
x_20 = lean::apply_2(x_1, x_16, x_18);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
x_13 = x_2;
goto lbl_14;
}
else
{
obj* x_22; 
x_22 = lean::array_swap(x_2, x_3, x_11);
x_13 = x_22;
goto lbl_14;
}
lbl_14:
{
obj* x_24; obj* x_26; obj* x_29; uint8 x_30; 
lean::inc(x_0);
x_24 = lean::array_get(x_0, x_13, x_4);
lean::inc(x_0);
x_26 = lean::array_get(x_0, x_13, x_3);
lean::inc(x_24);
lean::inc(x_1);
x_29 = lean::apply_2(x_1, x_24, x_26);
x_30 = lean::unbox(x_29);
if (x_30 == 0)
{
obj* x_32; obj* x_35; uint8 x_36; 
lean::inc(x_0);
x_32 = lean::array_get(x_0, x_13, x_11);
lean::inc(x_24);
lean::inc(x_1);
x_35 = lean::apply_2(x_1, x_32, x_24);
x_36 = lean::unbox(x_35);
if (x_36 == 0)
{
obj* x_42; obj* x_43; obj* x_45; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_11);
lean::inc(x_3);
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_0);
x_42 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_0, x_1, x_4, x_24, x_13, x_3, x_3);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
lean::inc(x_1);
lean::inc(x_0);
x_50 = l_Array_qsortAux___main___rarg(x_0, x_1, x_45, x_3, x_43);
x_51 = lean::mk_nat_obj(1ul);
x_52 = lean::nat_add(x_43, x_51);
lean::dec(x_43);
x_2 = x_50;
x_3 = x_52;
goto _start;
}
else
{
obj* x_56; obj* x_59; obj* x_64; obj* x_65; obj* x_67; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_24);
x_56 = lean::array_swap(x_13, x_11, x_4);
lean::dec(x_11);
lean::inc(x_0);
x_59 = lean::array_get(x_0, x_56, x_4);
lean::inc(x_3);
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_0);
x_64 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_0, x_1, x_4, x_59, x_56, x_3, x_3);
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_64, 1);
lean::inc(x_67);
lean::dec(x_64);
lean::inc(x_1);
lean::inc(x_0);
x_72 = l_Array_qsortAux___main___rarg(x_0, x_1, x_67, x_3, x_65);
x_73 = lean::mk_nat_obj(1ul);
x_74 = lean::nat_add(x_65, x_73);
lean::dec(x_65);
x_2 = x_72;
x_3 = x_74;
goto _start;
}
}
else
{
obj* x_78; obj* x_80; obj* x_82; obj* x_85; uint8 x_86; 
lean::dec(x_24);
x_78 = lean::array_swap(x_13, x_3, x_4);
lean::inc(x_0);
x_80 = lean::array_get(x_0, x_78, x_11);
lean::inc(x_0);
x_82 = lean::array_get(x_0, x_78, x_4);
lean::inc(x_82);
lean::inc(x_1);
x_85 = lean::apply_2(x_1, x_80, x_82);
x_86 = lean::unbox(x_85);
if (x_86 == 0)
{
obj* x_92; obj* x_93; obj* x_95; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_11);
lean::inc(x_3);
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_0);
x_92 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_0, x_1, x_4, x_82, x_78, x_3, x_3);
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_92, 1);
lean::inc(x_95);
lean::dec(x_92);
lean::inc(x_1);
lean::inc(x_0);
x_100 = l_Array_qsortAux___main___rarg(x_0, x_1, x_95, x_3, x_93);
x_101 = lean::mk_nat_obj(1ul);
x_102 = lean::nat_add(x_93, x_101);
lean::dec(x_93);
x_2 = x_100;
x_3 = x_102;
goto _start;
}
else
{
obj* x_106; obj* x_109; obj* x_114; obj* x_115; obj* x_117; obj* x_122; obj* x_123; obj* x_124; 
lean::dec(x_82);
x_106 = lean::array_swap(x_78, x_11, x_4);
lean::dec(x_11);
lean::inc(x_0);
x_109 = lean::array_get(x_0, x_106, x_4);
lean::inc(x_3);
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_0);
x_114 = l___private_init_data_array_qsort_1__partitionAux___main___rarg(x_0, x_1, x_4, x_109, x_106, x_3, x_3);
x_115 = lean::cnstr_get(x_114, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_114, 1);
lean::inc(x_117);
lean::dec(x_114);
lean::inc(x_1);
lean::inc(x_0);
x_122 = l_Array_qsortAux___main___rarg(x_0, x_1, x_117, x_3, x_115);
x_123 = lean::mk_nat_obj(1ul);
x_124 = lean::nat_add(x_115, x_123);
lean::dec(x_115);
x_2 = x_122;
x_3 = x_124;
goto _start;
}
}
}
}
}
}
obj* l_Array_qsortAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_qsortAux___main___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Array_qsortAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_qsortAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Array_qsortAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_qsortAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_qsortAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_qsortAux___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_qsortAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_qsortAux___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Array_qsortAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_qsortAux___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Array_qsortAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_qsortAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_qsort___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_qsortAux___main___rarg(x_0, x_2, x_1, x_3, x_4);
return x_5;
}
}
obj* l_Array_qsort(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_qsort___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Array_qsort___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_qsort___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Array_qsort___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_qsort(x_0);
lean::dec(x_0);
return x_1;
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
