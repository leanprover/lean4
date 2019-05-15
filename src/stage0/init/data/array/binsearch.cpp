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
obj* l_Array_binSearchAux___boxed(obj*);
obj* l_Array_binSearchAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearch___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearch___boxed(obj*);
obj* l_Array_binSearch(obj*);
obj* l_Array_binSearchAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Array_binSearchAux___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchAux(obj*);
obj* l_Array_binSearchAux___main___boxed(obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_Array_binSearchAux___main(obj*);
obj* l_Array_binSearchAux___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = lean::nat_dec_le(x_4, x_5);
if (x_6 == 0)
{
obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_12 = lean::box(0);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_18; obj* x_22; uint8 x_23; 
x_13 = lean::nat_add(x_4, x_5);
x_14 = lean::mk_nat_obj(2ul);
x_15 = lean::nat_div(x_13, x_14);
lean::dec(x_13);
lean::inc(x_0);
x_18 = lean::array_get(x_0, x_2, x_15);
lean::inc(x_3);
lean::inc(x_18);
lean::inc(x_1);
x_22 = lean::apply_2(x_1, x_18, x_3);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
obj* x_28; uint8 x_29; 
lean::dec(x_5);
lean::inc(x_18);
lean::inc(x_3);
lean::inc(x_1);
x_28 = lean::apply_2(x_1, x_3, x_18);
x_29 = lean::unbox(x_28);
if (x_29 == 0)
{
obj* x_35; 
lean::dec(x_15);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_18);
return x_35;
}
else
{
obj* x_37; uint8 x_38; 
lean::dec(x_18);
x_37 = lean::mk_nat_obj(0ul);
x_38 = lean::nat_dec_eq(x_15, x_37);
if (x_38 == 0)
{
obj* x_39; obj* x_40; 
x_39 = lean::mk_nat_obj(1ul);
x_40 = lean::nat_sub(x_15, x_39);
lean::dec(x_15);
x_5 = x_40;
goto _start;
}
else
{
obj* x_48; 
lean::dec(x_15);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_48 = lean::box(0);
return x_48;
}
}
}
else
{
obj* x_51; obj* x_52; 
lean::dec(x_18);
lean::dec(x_4);
x_51 = lean::mk_nat_obj(1ul);
x_52 = lean::nat_add(x_15, x_51);
lean::dec(x_15);
x_4 = x_52;
goto _start;
}
}
}
}
obj* l_Array_binSearchAux___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_binSearchAux___main___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Array_binSearchAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_binSearchAux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_binSearchAux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_binSearchAux___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_binSearchAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_binSearchAux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Array_binSearchAux(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_binSearchAux___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Array_binSearchAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_binSearchAux___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_binSearchAux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_binSearchAux(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_binSearch___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_binSearchAux___main___rarg(x_0, x_3, x_1, x_2, x_4, x_5);
return x_6;
}
}
obj* l_Array_binSearch(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_binSearch___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Array_binSearch___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_binSearch___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_binSearch___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_binSearch(x_0);
lean::dec(x_0);
return x_1;
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
