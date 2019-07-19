// Lean compiler output
// Module: init.data.array.binsearch
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
obj* l_Array_binSearch___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
uint8 l_Array_binSearchContains___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearch___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchContains___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearch(obj*);
obj* l_Array_binSearchAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Array_binSearchContains(obj*);
obj* l_Array_binSearchAux___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchAux(obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Array_binSearchAux___main___at_Array_binSearch___spec__1(obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1(obj*);
obj* l_Array_binSearchAux___main(obj*, obj*);
obj* l_Array_binSearchAux___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; 
x_9 = lean::nat_dec_le(x_7, x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; 
lean::dec(x_8);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_1);
x_10 = lean::box(0);
x_11 = lean::apply_1(x_4, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; 
x_12 = lean::nat_add(x_7, x_8);
x_13 = lean::mk_nat_obj(2u);
x_14 = lean::nat_div(x_12, x_13);
lean::dec(x_12);
lean::inc(x_1);
x_15 = lean::array_get(x_1, x_5, x_14);
lean::inc(x_3);
lean::inc(x_6);
lean::inc(x_15);
x_16 = lean::apply_2(x_3, x_15, x_6);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; 
lean::dec(x_8);
lean::inc(x_3);
lean::inc(x_15);
lean::inc(x_6);
x_18 = lean::apply_2(x_3, x_6, x_15);
x_19 = lean::unbox(x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_14);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_1);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_15);
x_21 = lean::apply_1(x_4, x_20);
return x_21;
}
else
{
obj* x_22; uint8 x_23; 
lean::dec(x_15);
x_22 = lean::mk_nat_obj(0u);
x_23 = lean::nat_dec_eq(x_14, x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::mk_nat_obj(1u);
x_25 = lean::nat_sub(x_14, x_24);
lean::dec(x_14);
x_8 = x_25;
goto _start;
}
else
{
obj* x_27; obj* x_28; 
lean::dec(x_14);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_1);
x_27 = lean::box(0);
x_28 = lean::apply_1(x_4, x_27);
return x_28;
}
}
}
else
{
obj* x_29; obj* x_30; 
lean::dec(x_15);
lean::dec(x_7);
x_29 = lean::mk_nat_obj(1u);
x_30 = lean::nat_add(x_14, x_29);
lean::dec(x_14);
x_7 = x_30;
goto _start;
}
}
}
}
obj* l_Array_binSearchAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_binSearchAux___main___rarg___boxed), 8, 0);
return x_3;
}
}
obj* l_Array_binSearchAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Array_binSearchAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_5);
lean::dec(x_2);
return x_9;
}
}
obj* l_Array_binSearchAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Array_binSearchAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
obj* l_Array_binSearchAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_binSearchAux___rarg___boxed), 8, 0);
return x_3;
}
}
obj* l_Array_binSearchAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Array_binSearchAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_5);
lean::dec(x_2);
return x_9;
}
}
obj* l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = lean::nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
obj* x_8; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_8 = lean::box(0);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_9 = lean::nat_add(x_5, x_6);
x_10 = lean::mk_nat_obj(2u);
x_11 = lean::nat_div(x_9, x_10);
lean::dec(x_9);
lean::inc(x_1);
x_12 = lean::array_get(x_1, x_3, x_11);
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_12);
x_13 = lean::apply_2(x_2, x_12, x_4);
x_14 = lean::unbox(x_13);
lean::dec(x_13);
if (x_14 == 0)
{
obj* x_15; uint8 x_16; 
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_12);
lean::inc(x_4);
x_15 = lean::apply_2(x_2, x_4, x_12);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_17; 
lean::dec(x_11);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_12);
return x_17;
}
else
{
obj* x_18; uint8 x_19; 
lean::dec(x_12);
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::mk_nat_obj(1u);
x_21 = lean::nat_sub(x_11, x_20);
lean::dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
obj* x_23; 
lean::dec(x_11);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_23 = lean::box(0);
return x_23;
}
}
}
else
{
obj* x_24; obj* x_25; 
lean::dec(x_12);
lean::dec(x_5);
x_24 = lean::mk_nat_obj(1u);
x_25 = lean::nat_add(x_11, x_24);
lean::dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
obj* l_Array_binSearchAux___main___at_Array_binSearch___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Array_binSearch___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg(x_1, x_4, x_2, x_3, x_5, x_6);
return x_7;
}
}
obj* l_Array_binSearch(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_binSearch___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
return x_7;
}
}
obj* l_Array_binSearch___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_binSearch___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
return x_7;
}
}
uint8 l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = lean::nat_dec_le(x_5, x_6);
if (x_7 == 0)
{
uint8 x_8; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_8 = 0;
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_9 = lean::nat_add(x_5, x_6);
x_10 = lean::mk_nat_obj(2u);
x_11 = lean::nat_div(x_9, x_10);
lean::dec(x_9);
lean::inc(x_1);
x_12 = lean::array_get(x_1, x_3, x_11);
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_12);
x_13 = lean::apply_2(x_2, x_12, x_4);
x_14 = lean::unbox(x_13);
lean::dec(x_13);
if (x_14 == 0)
{
obj* x_15; uint8 x_16; 
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_4);
x_15 = lean::apply_2(x_2, x_4, x_12);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
uint8 x_17; 
lean::dec(x_11);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_17 = 1;
return x_17;
}
else
{
obj* x_18; uint8 x_19; 
x_18 = lean::mk_nat_obj(0u);
x_19 = lean::nat_dec_eq(x_11, x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::mk_nat_obj(1u);
x_21 = lean::nat_sub(x_11, x_20);
lean::dec(x_11);
x_6 = x_21;
goto _start;
}
else
{
uint8 x_23; 
lean::dec(x_11);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_23 = 0;
return x_23;
}
}
}
else
{
obj* x_24; obj* x_25; 
lean::dec(x_12);
lean::dec(x_5);
x_24 = lean::mk_nat_obj(1u);
x_25 = lean::nat_add(x_11, x_24);
lean::dec(x_11);
x_5 = x_25;
goto _start;
}
}
}
}
obj* l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
uint8 l_Array_binSearchContains___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg(x_1, x_4, x_2, x_3, x_5, x_6);
return x_7;
}
}
obj* l_Array_binSearchContains(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_binSearchContains___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
x_8 = lean::box(x_7);
return x_8;
}
}
obj* l_Array_binSearchContains___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = l_Array_binSearchContains___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
x_8 = lean::box(x_7);
return x_8;
}
}
obj* initialize_init_data_array_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_array_binsearch(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_array_basic(w);
if (io_result_is_error(w)) return w;
return w;
}
