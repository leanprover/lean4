// Lean compiler output
// Module: init.data.nat.bitwise
// Imports: init.data.nat.basic init.data.nat.div init.coe
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
obj* l_Nat_bitwise___boxed(obj*, obj*, obj*);
obj* l_Nat_bitwise___main(obj*, obj*, obj*);
obj* l_Nat_lor___closed__1;
obj* l_Nat_lor___lambda__1___boxed(obj*, obj*);
obj* l_Nat_land___lambda__1___boxed(obj*, obj*);
uint8 l_Nat_lor___lambda__1(uint8, uint8);
obj* l_Nat_bitwise___main___boxed(obj*, obj*, obj*);
namespace lean {
obj* nat_mod(obj*, obj*);
}
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Nat_land___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l_Nat_land___lambda__1(uint8, uint8);
obj* l_Nat_bitwise(obj*, obj*, obj*);
obj* l_Nat_land___closed__1;
obj* l_Nat_land(obj*, obj*);
obj* l_Nat_lor___boxed(obj*, obj*);
namespace lean {
obj* nat_div(obj*, obj*);
}
obj* l_Nat_lor(obj*, obj*);
obj* l_Nat_bitwise___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_3, x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_7 = lean::mk_nat_obj(2u);
x_8 = lean::nat_div(x_2, x_7);
x_9 = lean::nat_div(x_3, x_7);
lean::inc(x_1);
x_10 = l_Nat_bitwise___main(x_1, x_8, x_9);
lean::dec(x_9);
lean::dec(x_8);
x_11 = lean::nat_mod(x_2, x_7);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_dec_eq(x_11, x_12);
lean::dec(x_11);
x_14 = lean::nat_mod(x_3, x_7);
x_15 = lean::nat_dec_eq(x_14, x_12);
lean::dec(x_14);
x_16 = lean::box(x_13);
x_17 = lean::box(x_15);
x_18 = lean::apply_2(x_1, x_16, x_17);
x_19 = lean::unbox(x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_20; 
x_20 = lean::nat_add(x_10, x_10);
lean::dec(x_10);
return x_20;
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::nat_add(x_10, x_10);
lean::dec(x_10);
x_22 = lean::nat_add(x_21, x_12);
lean::dec(x_21);
return x_22;
}
}
else
{
uint8 x_23; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; uint8 x_28; 
x_23 = 1;
x_24 = 0;
x_25 = lean::box(x_23);
x_26 = lean::box(x_24);
x_27 = lean::apply_2(x_1, x_25, x_26);
x_28 = lean::unbox(x_27);
lean::dec(x_27);
if (x_28 == 0)
{
obj* x_29; 
x_29 = lean::mk_nat_obj(0u);
return x_29;
}
else
{
lean::inc(x_2);
return x_2;
}
}
}
else
{
uint8 x_30; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; uint8 x_35; 
x_30 = 0;
x_31 = 1;
x_32 = lean::box(x_30);
x_33 = lean::box(x_31);
x_34 = lean::apply_2(x_1, x_32, x_33);
x_35 = lean::unbox(x_34);
lean::dec(x_34);
if (x_35 == 0)
{
obj* x_36; 
x_36 = lean::mk_nat_obj(0u);
return x_36;
}
else
{
lean::inc(x_3);
return x_3;
}
}
}
}
obj* l_Nat_bitwise___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Nat_bitwise___main(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Nat_bitwise(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Nat_bitwise___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Nat_bitwise___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Nat_bitwise(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
uint8 l_Nat_land___lambda__1(uint8 x_1, uint8 x_2) {
_start:
{
if (x_1 == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
return x_2;
}
}
}
obj* _init_l_Nat_land___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_land___lambda__1___boxed), 2, 0);
return x_1;
}
}
obj* l_Nat_land(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Nat_land___closed__1;
x_4 = l_Nat_bitwise___main(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Nat_land___lambda__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; uint8 x_5; obj* x_6; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_Nat_land___lambda__1(x_3, x_4);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_Nat_land___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Nat_land(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Nat_lor___lambda__1(uint8 x_1, uint8 x_2) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
}
}
obj* _init_l_Nat_lor___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_lor___lambda__1___boxed), 2, 0);
return x_1;
}
}
obj* l_Nat_lor(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Nat_lor___closed__1;
x_4 = l_Nat_bitwise___main(x_3, x_1, x_2);
return x_4;
}
}
obj* l_Nat_lor___lambda__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; uint8 x_5; obj* x_6; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l_Nat_lor___lambda__1(x_3, x_4);
x_6 = lean::box(x_5);
return x_6;
}
}
obj* l_Nat_lor___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Nat_lor(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* initialize_init_data_nat_basic(obj*);
obj* initialize_init_data_nat_div(obj*);
obj* initialize_init_coe(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_nat_bitwise(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_nat_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_nat_div(w);
if (io_result_is_error(w)) return w;
w = initialize_init_coe(w);
if (io_result_is_error(w)) return w;
l_Nat_land___closed__1 = _init_l_Nat_land___closed__1();
lean::mark_persistent(l_Nat_land___closed__1);
l_Nat_lor___closed__1 = _init_l_Nat_lor___closed__1();
lean::mark_persistent(l_Nat_lor___closed__1);
return w;
}
