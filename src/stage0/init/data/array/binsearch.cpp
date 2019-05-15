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
obj* l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___boxed(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
uint8 l_Array_binSearchContains___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchAux___boxed(obj*, obj*);
obj* l_Array_binSearchContains___boxed(obj*);
obj* l_Array_binSearchAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearch___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearchContains___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_binSearch___boxed(obj*);
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
obj* l_Array_binSearchAux___main___boxed(obj*, obj*);
obj* l_Array_binSearchAux___main___at_Array_binSearch___spec__1___boxed(obj*);
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
obj* l_Array_binSearchAux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; 
x_8 = lean::nat_dec_le(x_6, x_7);
if (x_8 == 0)
{
obj* x_14; obj* x_15; 
lean::dec(x_5);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_14 = lean::box(0);
x_15 = lean::apply_1(x_3, x_14);
return x_15;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_25; uint8 x_26; 
x_16 = lean::nat_add(x_6, x_7);
x_17 = lean::mk_nat_obj(2ul);
x_18 = lean::nat_div(x_16, x_17);
lean::dec(x_16);
lean::inc(x_0);
x_21 = lean::array_get(x_0, x_4, x_18);
lean::inc(x_5);
lean::inc(x_21);
lean::inc(x_2);
x_25 = lean::apply_2(x_2, x_21, x_5);
x_26 = lean::unbox(x_25);
if (x_26 == 0)
{
obj* x_31; uint8 x_32; 
lean::dec(x_7);
lean::inc(x_21);
lean::inc(x_5);
lean::inc(x_2);
x_31 = lean::apply_2(x_2, x_5, x_21);
x_32 = lean::unbox(x_31);
if (x_32 == 0)
{
obj* x_38; obj* x_39; 
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_18);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_21);
x_39 = lean::apply_1(x_3, x_38);
return x_39;
}
else
{
obj* x_41; uint8 x_42; 
lean::dec(x_21);
x_41 = lean::mk_nat_obj(0ul);
x_42 = lean::nat_dec_eq(x_18, x_41);
if (x_42 == 0)
{
obj* x_43; obj* x_44; 
x_43 = lean::mk_nat_obj(1ul);
x_44 = lean::nat_sub(x_18, x_43);
lean::dec(x_18);
x_7 = x_44;
goto _start;
}
else
{
obj* x_52; obj* x_53; 
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_18);
x_52 = lean::box(0);
x_53 = lean::apply_1(x_3, x_52);
return x_53;
}
}
}
else
{
obj* x_56; obj* x_57; 
lean::dec(x_6);
lean::dec(x_21);
x_56 = lean::mk_nat_obj(1ul);
x_57 = lean::nat_add(x_18, x_56);
lean::dec(x_18);
x_6 = x_57;
goto _start;
}
}
}
}
obj* l_Array_binSearchAux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_binSearchAux___main___rarg___boxed), 8, 0);
return x_2;
}
}
obj* l_Array_binSearchAux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_binSearchAux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_1);
lean::dec(x_4);
return x_8;
}
}
obj* l_Array_binSearchAux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_binSearchAux___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_binSearchAux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_binSearchAux___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
obj* l_Array_binSearchAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_binSearchAux___rarg___boxed), 8, 0);
return x_2;
}
}
obj* l_Array_binSearchAux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_binSearchAux___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_1);
lean::dec(x_4);
return x_8;
}
}
obj* l_Array_binSearchAux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_binSearchAux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_Array_binSearchAux___main___at_Array_binSearch___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Array_binSearch___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg(x_0, x_3, x_1, x_2, x_4, x_5);
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
obj* l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_binSearchAux___main___at_Array_binSearch___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_binSearchAux___main___at_Array_binSearch___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_binSearchAux___main___at_Array_binSearch___spec__1(x_0);
lean::dec(x_0);
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
uint8 l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = lean::nat_dec_le(x_4, x_5);
if (x_6 == 0)
{
uint8 x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_12 = 0;
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
obj* x_27; uint8 x_28; 
lean::dec(x_5);
lean::inc(x_3);
lean::inc(x_1);
x_27 = lean::apply_2(x_1, x_3, x_18);
x_28 = lean::unbox(x_27);
if (x_28 == 0)
{
uint8 x_34; 
lean::dec(x_15);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_34 = 1;
return x_34;
}
else
{
obj* x_35; uint8 x_36; 
x_35 = lean::mk_nat_obj(0ul);
x_36 = lean::nat_dec_eq(x_15, x_35);
if (x_36 == 0)
{
obj* x_37; obj* x_38; 
x_37 = lean::mk_nat_obj(1ul);
x_38 = lean::nat_sub(x_15, x_37);
lean::dec(x_15);
x_5 = x_38;
goto _start;
}
else
{
uint8 x_46; 
lean::dec(x_15);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_46 = 0;
return x_46;
}
}
}
else
{
obj* x_49; obj* x_50; 
lean::dec(x_18);
lean::dec(x_4);
x_49 = lean::mk_nat_obj(1ul);
x_50 = lean::nat_add(x_15, x_49);
lean::dec(x_15);
x_4 = x_50;
goto _start;
}
}
}
}
obj* l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg___boxed), 6, 0);
return x_1;
}
}
uint8 l_Array_binSearchContains___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg(x_0, x_3, x_1, x_2, x_4, x_5);
return x_6;
}
}
obj* l_Array_binSearchContains(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_binSearchContains___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
x_7 = lean::box(x_6);
lean::dec(x_2);
return x_7;
}
}
obj* l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_binSearchAux___main___at_Array_binSearchContains___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_binSearchContains___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = l_Array_binSearchContains___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
x_7 = lean::box(x_6);
lean::dec(x_1);
return x_7;
}
}
obj* l_Array_binSearchContains___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_binSearchContains(x_0);
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
